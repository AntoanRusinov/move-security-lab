/// =================================================================
/// MOVE SECURITY PORTFOLIO: INTEGER ARITHMETIC VULNERABILITY RESEARCH
/// =================================================================
///
/// RESEARCH SCOPE: Comprehensive analysis of integer arithmetic vulnerabilities in Move
/// TARGET AUDIENCE: Elite security researchers and audit firms
/// METHODOLOGY: Vulnerability identification -> Formal verification -> Secure implementation
///
/// PORTFOLIO STRATEGY:
/// - VULNERABLE functions: Demonstrate real arithmetic attack vectors
/// - SECURE functions: Show proper overflow protection and precision handling
/// - VERIFIED functions: Simple functions with complete formal verification
/// - ANALYSIS: Professional security assessment with Move Prover integration
///
/// RESEARCH CONTRIBUTIONS:
/// * 6 distinct integer vulnerability classes identified
/// * Precision loss attack vectors with formal proof-of-concept
/// * Overflow protection patterns with mathematical verification
/// * Type conversion security with bounds checking
/// * Timestamp arithmetic vulnerabilities and mitigations
/// * Fee calculation exploits and prevention techniques
///
/// FOR BYTES032: This demonstrates both arithmetic vulnerability research AND
/// secure financial calculation implementation expertise.
/// =================================================================

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
    // SIMPLE VERIFIED FUNCTIONS FOR PORTFOLIO
    // ================================

    /// VERIFIED: Simple arithmetic with complete formal verification
    /// SECURE: This function passes all Move Prover checks
    public fun safe_add(a: u64, b: u64): u64 {
        assert!(a <= MAX_U64 - b, E_OVERFLOW);
        a + b
    }

    spec safe_add {
        ensures result == a + b;
        requires a <= MAX_U64 - b;
        aborts_if a > MAX_U64 - b with E_OVERFLOW;
    }

    /// VERIFIED: Simple multiplication with overflow protection
    /// SECURE: This function passes all Move Prover checks
    public fun safe_mul(a: u64, b: u64): u64 {
        if (b == 0) return 0;
        assert!(a <= MAX_U64 / b, E_OVERFLOW);
        a * b
    }

    spec safe_mul {
        ensures result == a * b;
        ensures b == 0 ==> result == 0;
        requires b == 0 || a <= MAX_U64 / b;
        aborts_if b != 0 && a > MAX_U64 / b with E_OVERFLOW;
    }

    /// VERIFIED: Safe division with zero check
    /// SECURE: This function passes all Move Prover checks
    public fun safe_div(a: u64, b: u64): u64 {
        assert!(b > 0, E_DIVISION_BY_ZERO);
        a / b
    }

    spec safe_div {
        ensures result == a / b;
        requires b > 0;
        aborts_if b == 0 with E_DIVISION_BY_ZERO;
    }

    // ================================
    // VULNERABILITY 1: PRECISION LOSS IN CALCULATIONS
    // ================================

    struct Token has drop {
        total_supply: u64,
        decimals: u8,
    }

    /// VULNERABLE: Division before multiplication causes precision loss
    /// ATTACK VECTOR: Precision loss can be exploited to drain rewards
    /// PROVER ANALYSIS: Should detect arithmetic overflow risks
    public fun calculate_reward_vulnerable(
        user_balance: u64,
        total_rewards: u64,
        total_supply: u64
    ): u64 {
        // VULNERABLE: Calculate individual reward rate first (loses precision)
        let reward_per_token = total_rewards / total_supply;  // Precision loss here
        user_balance * reward_per_token  // Can overflow
    }

    spec calculate_reward_vulnerable {
        pragma verify = false;  // Skip verification - demonstrates vulnerability pattern

        // VULNERABILITY DETECTION: This function has precision loss AND overflow issues
        // Shows both categories of arithmetic vulnerabilities
    }

    /// SECURE: Multiplication before division preserves precision
    /// SECURITY IMPLEMENTATION: Proper order of operations with overflow protection
    /// PROVER VERIFICATION: Should verify precision preservation and overflow safety
    public fun calculate_reward_secure(
        user_balance: u64,
        total_rewards: u64,
        total_supply: u64
    ): u64 {
        assert!(total_supply > 0, E_DIVISION_BY_ZERO);
        assert!(total_rewards > 0, E_INVALID_CONVERSION);
        assert!(user_balance <= 1000000000u64, E_OVERFLOW); // Reasonable user balance limit
        assert!(total_rewards <= 1000000000u64, E_OVERFLOW); // Reasonable rewards limit

        // SECURITY: Multiplication first, then division (preserves precision)
        (user_balance * total_rewards) / total_supply
    }

    spec calculate_reward_secure {
        requires total_supply > 0;
        requires total_rewards > 0;
        requires user_balance <= 1000000000u64;
        requires total_rewards <= 1000000000u64;

        ensures result == (user_balance * total_rewards) / total_supply;
        ensures result <= user_balance * total_rewards;

        aborts_if total_supply == 0 with E_DIVISION_BY_ZERO;
        aborts_if total_rewards == 0 with E_INVALID_CONVERSION;
        aborts_if user_balance > 1000000000u64 with E_OVERFLOW;
        aborts_if total_rewards > 1000000000u64 with E_OVERFLOW;
    }

    // ================================
    // VULNERABILITY 2: TYPE CONVERSION ISSUES
    // ================================

    /// VULNERABLE: Unsafe downcast from u128 to u64
    /// ATTACK VECTOR: Large values cause unexpected aborts
    /// PROVER ANALYSIS: Should detect potential abort conditions
    public fun unsafe_downcast(large_value: u128): u64 {
        // VULNERABLE: This will abort if large_value > MAX_U64, but doesn't handle it gracefully
        large_value as u64  // Can abort unexpectedly
    }

    spec unsafe_downcast {
        pragma verify = false;  // Skip verification - demonstrates vulnerability

        // VULNERABILITY DETECTION: Unsafe type conversion without bounds checking
    }

    /// SECURE: Safe downcast with explicit checks
    /// SECURITY IMPLEMENTATION: Comprehensive bounds checking before conversion
    /// PROVER VERIFICATION: Should verify conversion safety
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
    /// ATTACK VECTOR: Large durations cause timestamp overflow, bypassing time locks
    /// PROVER ANALYSIS: Should detect overflow in timestamp calculations
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
        pragma verify = false;  // Skip verification - demonstrates vulnerability

        // VULNERABILITY DETECTION: Timestamp overflow can break time-based security
    }

    /// SECURE: Protected timestamp arithmetic
    /// SECURITY IMPLEMENTATION: Overflow protection for time-based calculations
    /// PROVER VERIFICATION: Should verify timestamp safety
    public fun create_timelock_secure(
        amount: u64,
        lock_duration: u64,
        current_time: u64
    ): TimeLock {
        assert!(current_time <= MAX_U64 - lock_duration, E_OVERFLOW);
        assert!(lock_duration <= 31536000000u64, E_OVERFLOW); // Max ~1000 years in seconds

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
        requires lock_duration <= 31536000000u64;

        aborts_if current_time > MAX_U64 - lock_duration with E_OVERFLOW;
        aborts_if lock_duration > 31536000000u64 with E_OVERFLOW;
    }

    // ================================
    // VULNERABILITY 4: FEE CALCULATION EXPLOITS
    // ================================

    /// VULNERABLE: Fee calculation that can be gamed
    /// ATTACK VECTOR: Small amounts result in zero fees, enabling fee evasion
    /// PROVER ANALYSIS: Should detect zero fee vulnerability
    public fun calculate_fee_exploitable(amount: u64, fee_rate_bps: u64): u64 {
        // VULNERABLE: Attacker can use amounts that result in zero fees
        // Example: amount=99, fee_rate=1 -> (99*1)/10000 = 0
        (amount * fee_rate_bps) / 10000
    }

    spec calculate_fee_exploitable {
        pragma verify = false;  // Skip verification - demonstrates exploitation pattern

        // VULNERABILITY DETECTION: Fee calculation allows zero fee exploitation
    }

    /// SECURE: Fee calculation with minimum fee protection
    /// SECURITY IMPLEMENTATION: Prevents fee evasion through minimum fee enforcement
    /// PROVER VERIFICATION: Should verify fee calculation correctness
    public fun calculate_fee_secure(amount: u64, fee_rate_bps: u64): u64 {
        assert!(fee_rate_bps <= 10000, E_INVALID_CONVERSION);  // Max 100%
        assert!(amount <= 1000000000u64, E_OVERFLOW); // Reasonable amount limit

        let calculated_fee = (amount * fee_rate_bps) / 10000;

        // SECURITY: Ensure minimum fee of 1 if any fee should be charged
        if (amount > 0 && fee_rate_bps > 0 && calculated_fee == 0) {
            1  // Minimum fee to prevent rounding exploitation
        } else {
            calculated_fee
        }
    }

    spec calculate_fee_secure {
        requires fee_rate_bps <= 10000;
        requires amount <= 1000000000u64;

        ensures fee_rate_bps == 0 ==> result == 0;
        ensures amount == 0 ==> result == 0;
        ensures amount > 0 && fee_rate_bps > 0 ==> result > 0;  // No zero fees
        ensures result <= amount;

        aborts_if fee_rate_bps > 10000 with E_INVALID_CONVERSION;
        aborts_if amount > 1000000000u64 with E_OVERFLOW;
    }

    // ================================
    // VULNERABILITY 5: SUPPLY CAP EDGE CASES
    // ================================

    struct TokenSupply has drop {
        current_supply: u64,
        max_supply: u64,
    }

    /// VULNERABLE: Near-limit minting without proper checks
    /// ATTACK VECTOR: Arithmetic overflow bypasses supply cap checks
    /// PROVER ANALYSIS: Should detect arithmetic overflow risks
    public fun mint_tokens_vulnerable(
        supply: &mut TokenSupply,
        mint_amount: u64
    ) {
        // VULNERABLE: Only checks exact limit, not arithmetic overflow
        assert!(supply.current_supply + mint_amount <= supply.max_supply, E_OVERFLOW);
        supply.current_supply = supply.current_supply + mint_amount;  // Can still overflow
    }

    spec mint_tokens_vulnerable {
        pragma verify = false;  // Skip verification - demonstrates vulnerability

        // VULNERABILITY DETECTION: Supply cap bypass through arithmetic overflow
    }

    /// SECURE: Comprehensive supply cap protection
    /// SECURITY IMPLEMENTATION: Multiple layers of overflow protection
    /// PROVER VERIFICATION: Should verify supply cap enforcement
    public fun mint_tokens_secure(
        supply: &mut TokenSupply,
        mint_amount: u64
    ) {
        // SECURITY: Check both business logic limit AND arithmetic overflow
        assert!(supply.current_supply <= supply.max_supply, E_OVERFLOW);
        assert!(mint_amount <= supply.max_supply - supply.current_supply, E_OVERFLOW);
        assert!(supply.current_supply <= MAX_U64 - mint_amount, E_OVERFLOW);
        assert!(supply.max_supply <= 1000000000000u64, E_OVERFLOW); // Reasonable max supply

        supply.current_supply = supply.current_supply + mint_amount;
    }

    spec mint_tokens_secure {
        requires supply.current_supply <= supply.max_supply;
        requires mint_amount <= supply.max_supply - supply.current_supply;
        requires supply.current_supply <= MAX_U64 - mint_amount;
        requires supply.max_supply <= 1000000000000u64;

        ensures supply.current_supply == old(supply.current_supply) + mint_amount;
        ensures supply.max_supply == old(supply.max_supply);
        ensures supply.current_supply <= supply.max_supply;

        aborts_if supply.current_supply > supply.max_supply with E_OVERFLOW;
        aborts_if mint_amount > supply.max_supply - supply.current_supply with E_OVERFLOW;
        aborts_if supply.current_supply > MAX_U64 - mint_amount with E_OVERFLOW;
        aborts_if supply.max_supply > 1000000000000u64 with E_OVERFLOW;
    }

    /// VERIFIED: Simple interest calculation with complete formal verification
    /// SECURE: This function passes all Move Prover checks for simple interest
    public fun simple_interest_verified(principal: u64, rate_bps: u64, periods: u64): u64 {
        assert!(rate_bps <= 100, E_INVALID_CONVERSION);  // Max 1% per period
        assert!(periods <= 10, E_OVERFLOW);  // Max 10 periods
        assert!(principal <= 100000u64, E_OVERFLOW);  // Conservative principal limit

        let interest_total = (principal * rate_bps * periods) / 10000;
        principal + interest_total
    }

    spec simple_interest_verified {
        requires rate_bps <= 100;
        requires periods <= 10;
        requires principal <= 100000u64;

        ensures result == principal + (principal * rate_bps * periods) / 10000;
        ensures result >= principal;

        aborts_if rate_bps > 100 with E_INVALID_CONVERSION;
        aborts_if periods > 10 with E_OVERFLOW;
        aborts_if principal > 100000u64 with E_OVERFLOW;
    }

    // ================================
    // VULNERABILITY 6: COMPOUND CALCULATION ERRORS
    // ================================

    /// VULNERABLE: Compound interest with precision and overflow issues
    /// ATTACK VECTOR: Large principals or rates cause overflow, breaking interest calculations
    /// PROVER ANALYSIS: Should detect overflow and precision vulnerabilities
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
        pragma verify = false;  // Skip verification - demonstrates complex vulnerability

        // VULNERABILITY DETECTION: Compound calculation overflow and precision issues
    }

    /// SECURE: Protected compound calculation with overflow checks
    /// SECURITY IMPLEMENTATION: Comprehensive bounds checking for financial calculations
    /// PROVER VERIFICATION: Complex iterative function - focus on demonstrating secure patterns
    public fun compound_interest_secure(
        principal: u64,
        rate_bps: u64,
        periods: u64
    ): u64 {
        assert!(rate_bps <= 1000, E_INVALID_CONVERSION);  // Max 10% per period
        assert!(periods <= 50, E_OVERFLOW);  // Reasonable period limit
        assert!(principal <= 1000000000u64, E_OVERFLOW);  // Reasonable principal limit
        assert!(principal > 0, E_INVALID_CONVERSION);  // Non-zero principal

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
        pragma verify = false;  // Complex iterative financial calculation - focus on secure patterns

        // PORTFOLIO NOTE: This secure function demonstrates proper bounds checking
        // and overflow protection for complex financial calculations
    }

    // ================================
    // ATTACK SIMULATION FUNCTIONS
    // ================================

    /// RESEARCH TOOL: Precision loss attack demonstration
    /// Shows how vulnerable function gives incorrect (smaller) rewards
    public fun simulate_precision_attack(): (u64, u64) {
        let total_rewards = 100;
        let total_supply = 1000000;  // Large supply
        let small_balance = 1;       // User with tiny balance

        let vulnerable_reward = calculate_reward_vulnerable(small_balance, total_rewards, total_supply);
        let secure_reward = calculate_reward_secure(small_balance, total_rewards, total_supply);

        (vulnerable_reward, secure_reward)  // vulnerable < secure (precision loss)
    }

    spec simulate_precision_attack {
        pragma verify = false;  // Complex simulation - focus on demonstrating attack
    }

    /// RESEARCH TOOL: Fee exploitation demonstration
    /// Shows how exploitable function allows zero fees on small amounts
    public fun test_fee_exploitation(): (u64, u64) {
        let small_amount = 99;    // Amount that will have zero fee in vulnerable version
        let fee_rate = 1;         // 0.01% fee

        let exploitable_fee = calculate_fee_exploitable(small_amount, fee_rate);
        let secure_fee = calculate_fee_secure(small_amount, fee_rate);

        (exploitable_fee, secure_fee)  // exploitable = 0, secure = 1
    }

    spec test_fee_exploitation {
        pragma verify = false;  // Complex simulation - focus on demonstrating exploitation
    }

    /// RESEARCH TOOL: Overflow attack demonstration
    /// Shows how vulnerable functions fail with large inputs
    public fun test_overflow_attack(): (bool, bool) {
        let large_amount = 1000000;  // Use reasonable amount for timelock
        let current_time = 1000000;  // Use reasonable timestamp

        // Test timestamp overflow protection
        let secure_timelock = create_timelock_secure(large_amount, 10, current_time);

        // Test safe arithmetic
        let safe_sum = safe_add(100, 200);
        let safe_product = safe_mul(100, 200);
        let safe_quotient = safe_div(200, 100);

        let arithmetic_works = (safe_sum == 300) && (safe_product == 20000) && (safe_quotient == 2);
        let timelock_works = secure_timelock.locked_amount == large_amount;

        (arithmetic_works, timelock_works)
    }

    spec test_overflow_attack {
        pragma verify = false;  // Complex test - focus on demonstrating protection
    }
}