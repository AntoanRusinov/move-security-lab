/// Phase 1.2: Reentrancy Attacks in Move
/// These examples show how reentrancy manifests differently in Move's resource model
/// Unlike Solidity's external call reentrancy, Move has different attack vectors

module move_security_lab::reentrancy_vulnerabilities {
    use std::vector;

    // Error codes
    const E_INSUFFICIENT_BALANCE: u64 = 2001;
    const E_INVALID_AMOUNT: u64 = 2002;
    const E_UNAUTHORIZED: u64 = 2003;
    const E_REENTRANCY_DETECTED: u64 = 2004;
    const E_INVALID_STATE: u64 = 2005;
    const E_CALLBACK_FAILED: u64 = 2006;

    // ================================
    // VULNERABILITY 1: STATE INCONSISTENCY THROUGH CALLBACKS
    // ================================

    struct Bank has key { // Does NOT have 'drop' ability
        balances: vector<Balance>,
        total_deposits: u64,
        reentrancy_guard: bool,
    }

    struct Balance has store, drop { // Does have 'drop' ability
        owner: address,
        amount: u64,
    }

    /// VULNERABLE: State is modified before callback completion
    /// This creates window for reentrancy through callback mechanisms
    public fun withdraw_vulnerable(
        bank: &mut Bank,
        owner: address,
        amount: u64,
        callback_enabled: bool
    ) {
        let balance_idx = find_balance_index(&bank.balances, owner);
        assert!(balance_idx < vector::length(&bank.balances), E_INSUFFICIENT_BALANCE);

        let balance = vector::borrow_mut(&mut bank.balances, balance_idx);
        assert!(balance.amount >= amount, E_INSUFFICIENT_BALANCE);

        // VULNERABLE: Update state BEFORE callback
        balance.amount = balance.amount - amount;  // State changed early
        bank.total_deposits = bank.total_deposits - amount;

        // VULNERABLE: If callback somehow triggers another withdrawal...
        if (callback_enabled) {
            // Simulated callback - in real Move this might be a module call
            // that eventually leads back to this contract
            execute_withdrawal_callback(bank, owner, amount);
        }
    }

    spec withdraw_vulnerable {
        requires exists_balance(bank.balances, owner);
        requires get_balance_amount(bank.balances, owner) >= amount;

        ensures bank.total_deposits == old(bank.total_deposits) - amount;

        aborts_if !exists_balance(bank.balances, owner);
        aborts_if get_balance_amount(bank.balances, owner) < amount;
    }

    /// SECURE: Checks-Effects-Interactions pattern with reentrancy guard
    public fun withdraw_secure(
        bank: &mut Bank,
        owner: address,
        amount: u64,
        callback_enabled: bool
    ) {
        // REENTRANCY GUARD
        assert!(!bank.reentrancy_guard, E_REENTRANCY_DETECTED);
        bank.reentrancy_guard = true;

        // CHECKS: Validate all conditions first
        let balance_idx = find_balance_index(&bank.balances, owner);
        assert!(balance_idx < vector::length(&bank.balances), E_INSUFFICIENT_BALANCE);

        let balance = vector::borrow(&bank.balances, balance_idx);
        assert!(balance.amount >= amount, E_INSUFFICIENT_BALANCE);

        // EFFECTS: Update state
        let balance_mut = vector::borrow_mut(&mut bank.balances, balance_idx);
        balance_mut.amount = balance_mut.amount - amount;
        bank.total_deposits = bank.total_deposits - amount;

        // INTERACTIONS: External calls after state changes
        if (callback_enabled) {
            execute_withdrawal_callback(bank, owner, amount);
        };

        // Reset reentrancy guard
        bank.reentrancy_guard = false;
    }

    spec withdraw_secure {
        requires exists_balance(bank.balances, owner);
        requires get_balance_amount(bank.balances, owner) >= amount;
        requires !bank.reentrancy_guard;

        ensures bank.total_deposits == old(bank.total_deposits) - amount;
        ensures !bank.reentrancy_guard;  // Guard is reset

        aborts_if bank.reentrancy_guard with E_REENTRANCY_DETECTED;
        aborts_if !exists_balance(bank.balances, owner);
        aborts_if get_balance_amount(bank.balances, owner) < amount;
    }

    // ================================
    // VULNERABILITY 2: CROSS-MODULE REENTRANCY
    // ================================

    struct LendingPool has key { // Does NOT have 'drop' ability
        total_borrowed: u64,
        total_collateral: u64,
        liquidation_threshold: u64,  // Basis points (7500 = 75%)
    }

    struct UserPosition has store, drop { // Does have 'drop' ability
        user: address,
        borrowed: u64,
        collateral: u64,
        active: bool,
    }

    /// VULNERABLE: Cross-module call creates reentrancy opportunity
    public fun liquidate_position_vulnerable(
        pool: &mut LendingPool,
        positions: &mut vector<UserPosition>,
        user: address,
        liquidator: address
    ) {
        let position_idx = find_position_index(positions, user);
        assert!(position_idx < vector::length(positions), E_INVALID_STATE);

        let position = vector::borrow_mut(positions, position_idx);
        assert!(position.active, E_INVALID_STATE);

        // Check if position is underwater
        let collateral_value = position.collateral * 100;  // Simplified pricing
        let required_collateral = (position.borrowed * pool.liquidation_threshold) / 10000;
        assert!(collateral_value < required_collateral, E_INVALID_STATE);

        // VULNERABLE: Update state before external interactions
        pool.total_borrowed = pool.total_borrowed - position.borrowed;
        pool.total_collateral = pool.total_collateral - position.collateral;
        position.active = false;

        // VULNERABLE: External call to liquidator (could reenter)
        // In practice, this might call a liquidation callback that somehow
        // triggers another liquidation or position modification
        notify_liquidation_callback(liquidator, user, position.borrowed, position.collateral);
    }

    spec liquidate_position_vulnerable {
        requires exists_position(positions, user);
        requires get_position(positions, user).active;

        ensures pool.total_borrowed == old(pool.total_borrowed) - old(get_position(positions, user).borrowed);

        aborts_if !exists_position(positions, user);
        aborts_if !get_position(positions, user).active;
    }

    /// SECURE: State machine with explicit locking
    public fun liquidate_position_secure(
        pool: &mut LendingPool,
        positions: &mut vector<UserPosition>,
        user: address,
        liquidator: address
    ) {
        let position_idx = find_position_index(positions, user);
        assert!(position_idx < vector::length(positions), E_INVALID_STATE);

        let position = vector::borrow_mut(positions, position_idx);
        assert!(position.active, E_INVALID_STATE);

        // Check if position is underwater
        let collateral_value = position.collateral * 100;
        let required_collateral = (position.borrowed * pool.liquidation_threshold) / 10000;
        assert!(collateral_value < required_collateral, E_INVALID_STATE);

        // SECURE: Lock position first to prevent reentrancy
        position.active = false;  // Immediate lock

        // Store values for cleanup
        let borrowed_amount = position.borrowed;
        let collateral_amount = position.collateral;

        // External interaction while position is locked
        notify_liquidation_callback(liquidator, user, borrowed_amount, collateral_amount);

        // Update global state after external call
        pool.total_borrowed = pool.total_borrowed - borrowed_amount;
        pool.total_collateral = pool.total_collateral - collateral_amount;
    }

    spec liquidate_position_secure {
        requires exists_position(positions, user);
        requires get_position(positions, user).active;

        ensures pool.total_borrowed == old(pool.total_borrowed) - old(get_position(positions, user).borrowed);
        ensures !get_position(positions, user).active;

        aborts_if !exists_position(positions, user);
        aborts_if !get_position(positions, user).active;
    }

    // ================================
    // VULNERABILITY 3: RECURSIVE FUNCTION CALLS
    // ================================

    struct GameState has key { // Does NOT have 'drop' ability
        player_scores: vector<PlayerScore>,
        game_active: bool,
        processing_turn: bool,
    }

    struct PlayerScore has store, drop { // Does have 'drop' ability
        player: address,
        score: u64,
        bonus_multiplier: u64,
    }

    /// VULNERABLE: Recursive scoring system can be exploited
    /// NOTE: This function demonstrates a reentrancy pattern that *would* be
    /// problematic in languages like Solidity. However, in Move, the borrow checker
    /// explicitly prevents the unsafe mutable aliasing that would enable this
    /// reentrancy. The line causing the compile error is commented out.
    public fun calculate_bonus_vulnerable(
        game: &mut GameState,
        player: address,
        base_points: u64,
        depth: u64  // Recursion depth
    ): u64 {
        if (depth == 0) return base_points;

        let player_idx = find_player_index(&game.player_scores, player);
        if (player_idx >= vector::length(&game.player_scores)) return base_points;

        let player_score_ref = vector::borrow_mut(&mut game.player_scores, player_idx);

        // The following line attempts a recursive call to `calculate_bonus_vulnerable`
        // while `player_score_ref` holds a mutable reference to `game.player_scores`.
        // This is mutable aliasing and is strictly forbidden by the Move compiler.
        // It's commented out to allow the module to compile.
        // let bonus = calculate_bonus_vulnerable(game, player, base_points / 2, depth - 1);

        let bonus = 0; // Placeholder to allow compilation if the above line is commented out.
                       // In a real scenario, this function should be refactored like `calculate_bonus_secure`.

        // VULNERABLE: State modification after (simulated) recursive call
        player_score_ref.score = player_score_ref.score + bonus;
        base_points + bonus
    }

    spec calculate_bonus_vulnerable {
        requires depth <= 10;  // Prevent infinite recursion
        ensures result >= base_points;

        aborts_if depth > 10;
    }

    /// SECURE: Non-recursive iterative approach with state protection
    public fun calculate_bonus_secure(
        game: &mut GameState,
        player: address,
        base_points: u64,
        max_depth: u64
    ): u64 {
        assert!(!game.processing_turn, E_REENTRANCY_DETECTED);
        game.processing_turn = true;  // Lock state

        let player_idx = find_player_index(&game.player_scores, player);
        if (player_idx >= vector::length(&game.player_scores)) {
            game.processing_turn = false;
            return base_points
        };

        // Iterative calculation instead of recursive
        let total_bonus = base_points;
        let current_points = base_points;
        let i = 0;

        while (i < max_depth && current_points > 0) {
            current_points = current_points / 2;
            total_bonus = total_bonus + current_points;
            i = i + 1;
        };

        // Update state once at the end
        let player_score = vector::borrow_mut(&mut game.player_scores, player_idx);
        player_score.score = player_score.score + total_bonus;

        game.processing_turn = false;  // Unlock state
        total_bonus
    }

    spec calculate_bonus_secure {
        requires !game.processing_turn;
        requires max_depth <= 10;

        ensures result >= base_points;
        ensures !game.processing_turn;  // State unlocked

        aborts_if game.processing_turn with E_REENTRANCY_DETECTED;
        aborts_if max_depth > 10;
    }

    // ================================
    // VULNERABILITY 4: RESOURCE TRANSFER REENTRANCY
    // ================================

    struct ResourceVault has key { // Does NOT have 'drop' ability
        resource_count: u64,  // Track number of resources instead of storing them directly
        pending_transfers: vector<PendingTransfer>,
        transfer_lock: bool,
    }

    struct PendingTransfer has store, drop { // Does have 'drop' ability
        from: address,
        to: address,
        amount: u64,
        confirmed: bool,
    }

    /// VULNERABLE: Resource transfer with callback creates reentrancy
    public fun transfer_with_callback_vulnerable(
        vault: &mut ResourceVault,
        from: address,
        to: address,
        amount: u64,
        notify_recipient: bool
    ) {
        // Check sufficient resources (simplified)
        assert!(vault.resource_count >= amount, E_INSUFFICIENT_BALANCE);

        // VULNERABLE: Create pending transfer before completion
        let transfer = PendingTransfer {
            from,
            to,
            amount,
            confirmed: false,  // Not yet confirmed
        };
        vector::push_back(&mut vault.pending_transfers, transfer);

        // VULNERABLE: If notification somehow triggers another transfer...
        if (notify_recipient) {
            notify_transfer_recipient(to, from, amount);
        };

        // Mark as confirmed after callback
        let last_idx = vector::length(&vault.pending_transfers) - 1;
        let pending = vector::borrow_mut(&mut vault.pending_transfers, last_idx);
        pending.confirmed = true;
    }

    spec transfer_with_callback_vulnerable {
        ensures len(vault.pending_transfers) == len(old(vault.pending_transfers)) + 1;

        aborts_if vault.resource_count < amount;
    }

    /// SECURE: Atomic transfer with proper locking
    public fun transfer_with_callback_secure(
        vault: &mut ResourceVault,
        from: address,
        to: address,
        amount: u64,
        notify_recipient: bool
    ) {
        assert!(!vault.transfer_lock, E_REENTRANCY_DETECTED);
        vault.transfer_lock = true;

        // Check sufficient resources
        assert!(vault.resource_count >= amount, E_INSUFFICIENT_BALANCE);

        // Complete transfer immediately (no pending state)
        let transfer = PendingTransfer {
            from,
            to,
            amount,
            confirmed: true,  // Immediately confirmed
        };
        vector::push_back(&mut vault.pending_transfers, transfer);

        // External notification after state is consistent
        if (notify_recipient) {
            notify_transfer_recipient(to, from, amount);
        };

        vault.transfer_lock = false;
    }

    spec transfer_with_callback_secure {
        requires !vault.transfer_lock;

        ensures len(vault.pending_transfers) == len(old(vault.pending_transfers)) + 1;
        ensures !vault.transfer_lock;

        aborts_if vault.transfer_lock with E_REENTRANCY_DETECTED;
        aborts_if vault.resource_count < amount;
    }

    // ================================
    // ATTACK SIMULATION FUNCTIONS
    // ================================

    /// Simulate reentrancy attack on withdrawal
    public fun simulate_withdrawal_reentrancy(): (u64, u64) {
        let bank = Bank {
            balances: vector[
                Balance { owner: @0x123, amount: 1000 },
                Balance { owner: @0x456, amount: 500 }
            ],
            total_deposits: 1500,
            reentrancy_guard: false,
        };

        let initial_total = bank.total_deposits;

        // Attempt withdrawal that could trigger reentrancy
        withdraw_vulnerable(&mut bank, @0x123, 100, true);

        let final_total = bank.total_deposits;

        // Explicitly drop the bank resource at the end of the test function
        drop_bank(bank);

        (initial_total, final_total)
    }

    spec simulate_withdrawal_reentrancy {
        aborts_if false;
    }

    /// Test recursive bonus exploitation
    public fun test_recursive_bonus_attack(): (u64, u64) {
        let game = GameState {
            player_scores: vector[
                PlayerScore { player: @0x123, score: 100, bonus_multiplier: 2 }
            ],
            game_active: true,
            processing_turn: false,
        };

        let initial_score = vector::borrow(&game.player_scores, 0).score;

        // Using secure version for compilation. The vulnerable version, if enabled,
        // would cause a compile-time error due to Move's borrow checker.
        let _bonus = calculate_bonus_secure(&mut game, @0x123, 50, 3);

        let final_score = vector::borrow(&game.player_scores, 0).score;

        // Explicitly drop the game state resource at the end of the test function
        drop_game_state(game);

        (initial_score, final_score)
    }

    spec test_recursive_bonus_attack {
        aborts_if false;
    }

    // ================================
    // HELPER FUNCTIONS (Implementation Details)
    // ================================

    fun find_balance_index(balances: &vector<Balance>, owner: address): u64 {
        let i = 0;
        let len = vector::length(balances);

        while (i < len) {
            let balance = vector::borrow(balances, i);
            if (balance.owner == owner) return i;
            i = i + 1;
        };

        len  // Return length if not found
    }

    fun find_position_index(positions: &vector<UserPosition>, user: address): u64 {
        let i = 0;
        let len = vector::length(positions);

        while (i < len) {
            let position = vector::borrow(positions, i);
            if (position.user == user) return i;
            i = i + 1;
        };

        len
    }

    fun find_player_index(scores: &vector<PlayerScore>, player: address): u64 {
        let i = 0;
        let len = vector::length(scores);

        while (i < len) {
            let score = vector::borrow(scores, i);
            if (score.player == player) return i;
            i = i + 1;
        };

        len
    }

    // Simulated external callbacks (in real Move these would be cross-module calls)
    fun execute_withdrawal_callback(bank: &Bank, owner: address, amount: u64) {
        // Simulate external callback that might somehow trigger reentrancy
        // In practice, this could be a call to another module that eventually
        // calls back into this contract
        let _ = bank;
        let _ = owner;
        let _ = amount;
    }

    fun notify_liquidation_callback(liquidator: address, user: address, borrowed: u64, collateral: u64) {
        // Simulate liquidation notification that could trigger reentrancy
        let _ = liquidator;
        let _ = user;
        let _ = borrowed;
        let _ = collateral;
    }

    fun notify_transfer_recipient(to: address, from: address, amount: u64) {
        // Simulate transfer notification
        let _ = to;
        let _ = from;
        let _ = amount;
    }

    // New helper functions to explicitly drop resources for testing
    fun drop_bank(bank: Bank) {
        let Bank { balances, total_deposits: _, reentrancy_guard: _ } = bank;
        // Drop each element in the balances vector.
        // Balance has `drop` ability, so it's implicitly dropped when `balance` goes out of scope.
        while (vector::length(&balances) > 0) {
            let _balance = vector::pop_back(&mut balances);
            // No explicit drop needed here for `_balance`
        };
        // The `balances` vector itself will be dropped implicitly now, and since it holds `drop` types, that's fine.
    }

    fun drop_game_state(game: GameState) {
        let GameState { player_scores, game_active: _, processing_turn: _ } = game;
        // Drop each element in the player_scores vector.
        // PlayerScore has `drop` ability, so it's implicitly dropped when `player_score` goes out of scope.
        while (vector::length(&player_scores) > 0) {
            let _player_score = vector::pop_back(&mut player_scores);
            // No explicit drop needed here for `_player_score`
        };
        // The `player_scores` vector itself will be dropped implicitly now.
    }

    // ================================
    // SPECIFICATION HELPERS
    // ================================

    spec fun exists_balance(balances: vector<Balance>, owner: address): bool;

    spec fun get_balance_amount(balances: vector<Balance>, owner: address): u64;

    spec fun exists_position(positions: vector<UserPosition>, user: address): bool;

    spec fun get_position(positions: vector<UserPosition>, user: address): UserPosition;
}