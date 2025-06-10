/// Phase 1.1: Integer Overflow/Underflow Vulnerability Patterns in Move
/// These examples show how arithmetic issues manifest differently in Move

module move_security_lab::integer_vulnerabilities {
    
    const MAX_U64: u64 = 18446744073709551615;
    const MAX_U128: u128 = 340282366920938463463374607431768211455;
    
    // Error codes
    const E_OVERFLOW: u64 = 1001;
    const E_UNDERFLOW: u64 = 1002;
    const E_DIVISION_BY_ZERO: u64 = 1003;
    const E_PRECISION_LOSS: u64 = 1004;
    const E_INVALID_CONVERSION: u64 = 1005;
    
    // ================================
    // VULNERABILITY 1: PRECISION LOSS IN CALCULATIONS
    // ================================
    
    struct Token has drop {
        total_supply: u64,
        decimals: u8,
    }
    
    /// VULNERABLE: Division before multiplication causes precision loss
    /// This can be exploited to get MORE rewards than deserved
    public fun calculate_reward_vulnerable(
        user_balance: u64,
        total_rewards: u64,
        total_supply: u64
    ): u64 {
        // VULNERABLE: Calculate individual reward rate first (loses precision)
        let reward_per_token = total_rewards / total_supply;  // Precision loss here
        user_balance * reward_per_token
    }
    
    spec calculate_reward_vulnerable {
        // This will give LESS than the correct amount due to precision loss
        ensures result <= (user_balance * total_rewards) / total_supply;
        
        requires total_supply > 0;
        aborts_if total_supply == 0;
    }
    
    /// SECURE: Multiplication before division preserves precision
    public fun calculate_reward_secure(
        user_balance: u64,
        total_rewards: u64,
        total_supply: u64
    ): u64 {
        assert!(total_supply > 0, E_DIVISION_BY_ZERO);
        
        // CORRECT ORDER: Multiplication first, then division
        (user_balance * total_rewards) / total_supply
    }
    
    spec calculate_reward_secure {
        ensures result == (user_balance * total_rewards) / total_supply;
        ensures result <= user_balance * total_rewards;  // Can't exceed max possible
        
        requires total_supply > 0;
        requires user_balance <= MAX_U64 / total_rewards;  // Prevent overflow
        aborts_if total_supply == 0 with E_DIVISION_BY_ZERO;
    }
    
    /// EXPLOITABLE: Attacker can manipulate reward calculation
    /// by inflating total_supply right before reward calculation
    public fun calculate_reward_exploitable(
        user_balance: u64,
        total_rewards: u64,
        total_supply: u64
    ): u64 {
        // Attacker strategy: 
        // 1. Make large deposit to inflate total_supply
        // 2. Call this function (gets tiny reward due to large denominator)
        // 3. Withdraw large deposit
        // 4. Now legitimate users get disproportionately large rewards
        (user_balance * total_rewards) / total_supply
    }
    
    spec calculate_reward_exploitable {
        ensures result == (user_balance * total_rewards) / total_supply;
        
        // The vulnerability is in the USAGE pattern, not the math
        // Attacker can manipulate total_supply to affect others' rewards
        requires total_supply > 0;
        requires user_balance <= MAX_U64 / total_rewards;
        aborts_if total_supply == 0;
    }
    
    // ================================
    // VULNERABILITY 2: TYPE CONVERSION ISSUES
    // ================================
    
    /// VULNERABLE: Unsafe downcast from u128 to u64
    public fun unsafe_downcast(large_value: u128): u64 {
        // This will abort if large_value > MAX_U64, but doesn't handle it gracefully
        large_value as u64  // Can abort unexpectedly
    }
    
    spec unsafe_downcast {
        ensures result == large_value;
        aborts_if large_value > MAX_U64;  // Prover shows this can abort
    }
    
    /// SECURE: Safe downcast with explicit checks
    public fun safe_downcast(large_value: u128): u64 {
        assert!(large_value <= (MAX_U64 as u128), E_INVALID_CONVERSION);
        large_value as u64
    }
    
    spec safe_downcast {
        ensures result == large_value;
        requires large_value <= MAX_U64;
        aborts_if large_value > MAX_U64 with E_INVALID_CONVERSION;
    }
    
    // ================================
    // VULNERABILITY 3: TIMESTAMP ARITHMETIC VULNERABILITIES
    // ================================
    
    struct TimeLock has drop {
        unlock_time: u64,
        locked_amount: u64,
    }
    
    /// VULNERABLE: Timestamp arithmetic without overflow protection
    public fun create_timelock_vulnerable(
        amount: u64, 
        lock_duration: u64, 
        current_time: u64
    ): TimeLock {
        // VULNERABLE: No check for timestamp overflow
        let unlock_time = current_time + lock_duration;  // Can overflow
        
        TimeLock {
            unlock_time,
            locked_amount: amount,
        }
    }
    
    spec create_timelock_vulnerable {
        ensures result.unlock_time == current_time + lock_duration;
        ensures result.locked_amount == amount;
        
        // Prover will show this can abort on overflow
        aborts_if current_time + lock_duration > MAX_U64;
    }
    
    /// SECURE: Protected timestamp arithmetic
    public fun create_timelock_secure(
        amount: u64, 
        lock_duration: u64, 
        current_time: u64
    ): TimeLock {
        assert!(current_time <= MAX_U64 - lock_duration, E_OVERFLOW);
        
        let unlock_time = current_time + lock_duration;
        
        TimeLock {
            unlock_time,
            locked_amount: amount,
        }
    }
    
    spec create_timelock_secure {
        ensures result.unlock_time == current_time + lock_duration;
        ensures result.locked_amount == amount;
        
        requires current_time <= MAX_U64 - lock_duration;
        aborts_if current_time > MAX_U64 - lock_duration with E_OVERFLOW;
    }
    
    // ================================
    // VULNERABILITY 4: FEE CALCULATION EXPLOITS
    // ================================
    
    /// SECURE: Fee calculation with minimum fee protection
    public fun calculate_fee_secure(amount: u64, fee_rate_bps: u64): u64 {
        assert!(fee_rate_bps <= 10000, E_INVALID_CONVERSION);  // Max 100%
        
        let calculated_fee = (amount * fee_rate_bps) / 10000;
        
        // Ensure minimum fee of 1 if any fee should be charged
        if (amount > 0 && fee_rate_bps > 0 && calculated_fee == 0) {
            1  // Minimum fee to prevent rounding exploitation
        } else {
            calculated_fee
        }
    }
    
    spec calculate_fee_secure {
        ensures fee_rate_bps == 0 ==> result == 0;
        ensures amount == 0 ==> result == 0;
        ensures amount > 0 && fee_rate_bps > 0 ==> result > 0;  // No zero fees
        ensures result <= amount;
        
        requires fee_rate_bps <= 10000;
        requires amount <= MAX_U64 / (fee_rate_bps + 1);
        aborts_if fee_rate_bps > 10000;
    }
    
    /// REAL ATTACK: Fee calculation that can be gamed
    public fun calculate_fee_exploitable(amount: u64, fee_rate_bps: u64): u64 {
        // Attacker can use amounts that result in zero fees
        // Example: amount=99, fee_rate=1 -> (99*1)/10000 = 0
        (amount * fee_rate_bps) / 10000
    }
    
    spec calculate_fee_exploitable {
        ensures result == (amount * fee_rate_bps) / 10000;
        
        // Shows the exploit: small amounts can have zero fees
        ensures amount * fee_rate_bps < 10000 ==> result == 0;
        
        requires amount <= MAX_U64 / (fee_rate_bps + 1);
        aborts_if false;
    }
    
    // ================================
    // VULNERABILITY 5: SUPPLY CAP EDGE CASES
    // ================================
    
    struct TokenSupply has drop {
        current_supply: u64,
        max_supply: u64,
    }
    
    /// VULNERABLE: Near-limit minting without proper checks
    public fun mint_tokens_vulnerable(
        supply: &mut TokenSupply, 
        mint_amount: u64
    ) {
        // VULNERABLE: Only checks exact limit, not overflow
        assert!(supply.current_supply + mint_amount <= supply.max_supply, E_OVERFLOW);
        supply.current_supply = supply.current_supply + mint_amount;  // Can still overflow
    }
    
    spec mint_tokens_vulnerable {
        ensures supply.current_supply == old(supply.current_supply) + mint_amount;
        ensures supply.max_supply == old(supply.max_supply);
        
        requires supply.current_supply + mint_amount <= supply.max_supply;
        
        // Prover shows this can still abort on arithmetic overflow
        aborts_if supply.current_supply + mint_amount > MAX_U64;
    }
    
    /// SECURE: Comprehensive supply cap protection
    public fun mint_tokens_secure(
        supply: &mut TokenSupply, 
        mint_amount: u64
    ) {
        // Check both business logic limit AND arithmetic overflow
        assert!(supply.current_supply <= supply.max_supply, E_OVERFLOW);
        assert!(mint_amount <= supply.max_supply - supply.current_supply, E_OVERFLOW);
        assert!(supply.current_supply <= MAX_U64 - mint_amount, E_OVERFLOW);
        
        supply.current_supply = supply.current_supply + mint_amount;
    }
    
    spec mint_tokens_secure {
        ensures supply.current_supply == old(supply.current_supply) + mint_amount;
        ensures supply.max_supply == old(supply.max_supply);
        ensures supply.current_supply <= supply.max_supply;
        
        requires supply.current_supply <= supply.max_supply;
        requires mint_amount <= supply.max_supply - supply.current_supply;
        requires supply.current_supply <= MAX_U64 - mint_amount;
        
        aborts_if supply.current_supply > supply.max_supply with E_OVERFLOW;
        aborts_if mint_amount > supply.max_supply - supply.current_supply with E_OVERFLOW;
        aborts_if supply.current_supply > MAX_U64 - mint_amount with E_OVERFLOW;
    }
    
    // ================================
    // VULNERABILITY 6: COMPOUND CALCULATION ERRORS
    // ================================
    
    /// VULNERABLE: Compound interest with precision and overflow issues
    public fun compound_interest_vulnerable(
        principal: u64,
        rate_bps: u64,  // Rate in basis points (100 = 1%)
        periods: u64
    ): u64 {
        let amount = principal;
        let i = 0;
        
        while (i < periods) {
            // VULNERABLE: Multiple precision losses and potential overflow
            amount = amount + (amount * rate_bps) / 10000;  // Can overflow
            i = i + 1;
        };
        
        amount
    }
    
    spec compound_interest_vulnerable {
        ensures result >= principal;  // Should always grow
        ensures periods == 0 ==> result == principal;
        ensures rate_bps == 0 ==> result == principal;
        
        // But the prover will show this can abort on overflow
        aborts_if periods > 0 && rate_bps > 0;  // Too broad - shows overflow risk
    }
    
    /// SECURE: Protected compound calculation with overflow checks
    public fun compound_interest_secure(
        principal: u64,
        rate_bps: u64,
        periods: u64
    ): u64 {
        assert!(rate_bps <= 10000, E_INVALID_CONVERSION);  // Max 100% per period
        assert!(periods <= 100, E_OVERFLOW);  // Reasonable period limit
        assert!(principal <= MAX_U64 / 2, E_OVERFLOW);  // Prevent near-overflow starts
        
        let amount = principal;
        let i = 0;
        
        while (i < periods) {
            let interest = (amount * rate_bps) / 10000;
            assert!(amount <= MAX_U64 - interest, E_OVERFLOW);
            amount = amount + interest;
            i = i + 1;
        };
        
        amount
    }
    
    spec compound_interest_secure {
        ensures result >= principal;
        ensures periods == 0 ==> result == principal;
        ensures rate_bps == 0 ==> result == principal;
        
        requires rate_bps <= 10000;
        requires periods <= 100;
        requires principal <= MAX_U64 / 2;
        
        aborts_if rate_bps > 10000 with E_INVALID_CONVERSION;
        aborts_if periods > 100 with E_OVERFLOW;
        aborts_if principal > MAX_U64 / 2 with E_OVERFLOW;
    }
    
    // ================================
    // ATTACK SIMULATION FUNCTIONS
    // ================================
    
    /// Simulate precision loss attack - shows vulnerable gives LESS
    public fun simulate_precision_attack(): (u64, u64) {
        let total_rewards = 100;
        let total_supply = 1000000;  // Large supply
        let small_balance = 1;       // User with tiny balance
        
        let vulnerable_reward = calculate_reward_vulnerable(small_balance, total_rewards, total_supply);
        let secure_reward = calculate_reward_secure(small_balance, total_rewards, total_supply);
        
        (vulnerable_reward, secure_reward)  // vulnerable < secure (precision loss)
    }
    
    spec simulate_precision_attack {
        aborts_if false;
    }
    
    /// Test actual fee exploitation - zero fees on small amounts
    public fun test_fee_exploitation(): (u64, u64) {
        let small_amount = 99;    // Amount that will have zero fee
        let fee_rate = 1;         // 0.01% fee
        
        let exploitable_fee = calculate_fee_exploitable(small_amount, fee_rate);
        let secure_fee = calculate_fee_secure(small_amount, fee_rate);
        
        (exploitable_fee, secure_fee)  // exploitable = 0, secure = 1
    }
    
    spec test_fee_exploitation {
        aborts_if false;
    }
}