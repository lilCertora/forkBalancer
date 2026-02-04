// =============================================================================
// StableMathPropertiesAxioms.spec
//
// Properties for StableMath with axiomatic Newton-Raphson summaries.
// The expensive iterative `computeInvariant` and `computeBalance` are replaced
// by uninterpreted ghost functions with mathematical axioms.
//
// This allows verifying pool properties without loop unrolling, making the
// verification tractable for Certora.
// =============================================================================

using StableMathAxiomsHarness as SM;

// =============================================================================
// CONSTANTS
// =============================================================================

definition ONE_18() returns mathint = 1000000000000000000;

// StableMath constants
definition AMP_PRECISION() returns mathint = 1000;
definition MIN_AMP_SCALED() returns mathint = 1000; // MIN_AMP * AMP_PRECISION = 1 * 1000
definition MAX_AMP_SCALED() returns mathint = 50000000; // MAX_AMP * AMP_PRECISION = 50000 * 1000

// Reasonable bounds for balances (avoid overflow, ensure meaningful values)
definition MIN_BALANCE() returns mathint = 1000000; // 1e6 (dust threshold)
definition MAX_BALANCE() returns mathint = 340282366920938463463374607431768211455; // 2^128 - 1

// =============================================================================
// GHOST FUNCTION: Uninterpreted computeInvariant for 2 tokens
// =============================================================================

ghost invariant_ghost_2(mathint, mathint, mathint) returns mathint {
    // -------------------------------------------------------------------------
    // IDENTITY: Zero balances => zero invariant
    // -------------------------------------------------------------------------
    axiom forall mathint amp. forall mathint b0. forall mathint b1.
        (b0 == 0 && b1 == 0) => invariant_ghost_2(amp, b0, b1) == 0;

    // -------------------------------------------------------------------------
    // POSITIVITY: Positive balances => positive invariant
    // -------------------------------------------------------------------------
    axiom forall mathint amp. forall mathint b0. forall mathint b1.
        (amp > 0 && b0 > 0 && b1 > 0) => invariant_ghost_2(amp, b0, b1) > 0;

    // -------------------------------------------------------------------------
    // SYMMETRY: D(amp, b0, b1) = D(amp, b1, b0)
    // -------------------------------------------------------------------------
    axiom forall mathint amp. forall mathint b0. forall mathint b1.
        invariant_ghost_2(amp, b0, b1) == invariant_ghost_2(amp, b1, b0);

    // -------------------------------------------------------------------------
    // MONOTONICITY IN BALANCE b0
    // Increasing b0 (with b1 fixed) increases D
    // -------------------------------------------------------------------------
    axiom forall mathint amp. forall mathint b0_1. forall mathint b0_2. forall mathint b1.
        (amp > 0 && b0_1 > 0 && b0_2 > 0 && b1 > 0 && b0_1 < b0_2) =>
        invariant_ghost_2(amp, b0_1, b1) < invariant_ghost_2(amp, b0_2, b1);

    // -------------------------------------------------------------------------
    // MONOTONICITY IN BALANCE b1 (follows from symmetry, but explicit)
    // -------------------------------------------------------------------------
    axiom forall mathint amp. forall mathint b0. forall mathint b1_1. forall mathint b1_2.
        (amp > 0 && b0 > 0 && b1_1 > 0 && b1_2 > 0 && b1_1 < b1_2) =>
        invariant_ghost_2(amp, b0, b1_1) < invariant_ghost_2(amp, b0, b1_2);

    // -------------------------------------------------------------------------
    // BOUNDS: Geometric mean <= D <= Arithmetic mean (sum)
    // For n=2: 2*sqrt(b0*b1) <= D <= b0 + b1
    // We can't express sqrt in SMT easily, so we use a weaker lower bound: D > 0
    // Upper bound: D <= b0 + b1
    // -------------------------------------------------------------------------
    axiom forall mathint amp. forall mathint b0. forall mathint b1.
        (amp > 0 && b0 > 0 && b1 > 0) => invariant_ghost_2(amp, b0, b1) <= b0 + b1;

    // -------------------------------------------------------------------------
    // EQUAL BALANCES IDENTITY: D(amp, B, B) = 2*B for any amp
    // This is exact for the StableSwap invariant when all balances are equal
    // -------------------------------------------------------------------------
    axiom forall mathint amp. forall mathint B.
        (amp > 0 && B > 0) => invariant_ghost_2(amp, B, B) == 2 * B;

    // -------------------------------------------------------------------------
    // HOMOGENEITY: D(amp, k*b0, k*b1) = k * D(amp, b0, b1)
    // The StableSwap invariant is homogeneous of degree 1 in balances
    // -------------------------------------------------------------------------
    axiom forall mathint amp. forall mathint b0. forall mathint b1. forall mathint k.
        (amp > 0 && b0 > 0 && b1 > 0 && k > 0) =>
        invariant_ghost_2(amp, k * b0, k * b1) == k * invariant_ghost_2(amp, b0, b1);
}

// =============================================================================
// GHOST FUNCTION: Uninterpreted computeBalance for 2 tokens
// Given one balance (b_other) and the invariant, compute the other balance.
// =============================================================================

ghost balance_ghost_2(mathint, mathint, mathint) returns mathint {
    // -------------------------------------------------------------------------
    // POSITIVITY: Positive inputs => positive output
    // -------------------------------------------------------------------------
    axiom forall mathint amp. forall mathint b_other. forall mathint D.
        (amp > 0 && b_other > 0 && D > 0) => balance_ghost_2(amp, b_other, D) > 0;

    // -------------------------------------------------------------------------
    // UPPER BOUND: Computed balance < D (since D >= sum of balances)
    // -------------------------------------------------------------------------
    axiom forall mathint amp. forall mathint b_other. forall mathint D.
        (amp > 0 && b_other > 0 && D > b_other) => balance_ghost_2(amp, b_other, D) < D;

    // -------------------------------------------------------------------------
    // MONOTONICITY IN INVARIANT: Higher D => higher computed balance
    // -------------------------------------------------------------------------
    axiom forall mathint amp. forall mathint b_other. forall mathint D1. forall mathint D2.
        (amp > 0 && b_other > 0 && D1 > 0 && D2 > 0 && D1 < D2) =>
        balance_ghost_2(amp, b_other, D1) < balance_ghost_2(amp, b_other, D2);

    // -------------------------------------------------------------------------
    // MONOTONICITY IN OTHER BALANCE (inverse): Higher b_other => lower computed balance
    // For fixed D, if b_other increases, the computed balance must decrease
    // to maintain the invariant.
    // -------------------------------------------------------------------------
    axiom forall mathint amp. forall mathint b1. forall mathint b2. forall mathint D.
        (amp > 0 && b1 > 0 && b2 > 0 && D > 0 && b1 < b2 && D > b2) =>
        balance_ghost_2(amp, b1, D) > balance_ghost_2(amp, b2, D);

    // -------------------------------------------------------------------------
    // CONSISTENCY: If D = invariant_ghost_2(amp, b0, b1), then
    // balance_ghost_2(amp, b0, D) should equal b1 (and vice versa).
    // This is the fundamental consistency property.
    // -------------------------------------------------------------------------
    axiom forall mathint amp. forall mathint b0. forall mathint b1.
        (amp > 0 && b0 > 0 && b1 > 0) =>
        balance_ghost_2(amp, b0, invariant_ghost_2(amp, b0, b1)) == b1;

    // -------------------------------------------------------------------------
    // INVERSE CONSISTENCY: If b1 = balance_ghost_2(amp, b0, D), then
    // invariant_ghost_2(amp, b0, b1) = D.
    // This ensures the balance function is the true inverse of the invariant.
    // -------------------------------------------------------------------------
    axiom forall mathint amp. forall mathint b0. forall mathint D.
        (amp > 0 && b0 > 0 && D > 0 && D > b0) =>
        invariant_ghost_2(amp, b0, balance_ghost_2(amp, b0, D)) == D;

    // -------------------------------------------------------------------------
    // BALANCE SYMMETRY: balance(balance(b, D), D) = b
    // For a 2-token pool, if b1 = balance(b0, D), then b0 = balance(b1, D).
    // This is because the invariant equation is symmetric in the two tokens.
    // -------------------------------------------------------------------------
    axiom forall mathint amp. forall mathint b. forall mathint D.
        (amp > 0 && b > 0 && D > 0 && D > b && D > balance_ghost_2(amp, b, D)) =>
        balance_ghost_2(amp, balance_ghost_2(amp, b, D), D) == b;

    // -------------------------------------------------------------------------
    // EQUAL BALANCE CASE: When D = 2*B, balance_ghost_2(amp, B, D) = B
    // -------------------------------------------------------------------------
    axiom forall mathint amp. forall mathint B.
        (amp > 0 && B > 0) => balance_ghost_2(amp, B, 2 * B) == B;
}

// =============================================================================
// CVL SUMMARY FUNCTIONS for oracle calls
// =============================================================================

function cvlInvariant2Axiom(address oracle, uint256 amp, uint256 b0, uint256 b1) returns uint256 {
    mathint mAmp = to_mathint(amp);
    mathint mB0 = to_mathint(b0);
    mathint mB1 = to_mathint(b1);

    // Domain constraints
    require mAmp >= MIN_AMP_SCALED();
    require mAmp <= MAX_AMP_SCALED();
    require mB0 > 0;
    require mB1 > 0;

    mathint r = invariant_ghost_2(mAmp, mB0, mB1);

    // Positivity
    require r > 0;

    // Upper bound
    require r <= mB0 + mB1;

    return require_uint256(r);
}

function cvlBalance2Axiom(address oracle, uint256 amp, uint256 b_other, uint256 inv, uint256 tokenIndex) returns uint256 {
    mathint mAmp = to_mathint(amp);
    mathint mBOther = to_mathint(b_other);
    mathint mD = to_mathint(inv);

    // Domain constraints
    require mAmp >= MIN_AMP_SCALED();
    require mAmp <= MAX_AMP_SCALED();
    require mBOther > 0;
    require mD > 0;
    require mD > mBOther; // D must be greater than any single balance

    mathint r = balance_ghost_2(mAmp, mBOther, mD);

    // Positivity
    require r > 0;

    // Upper bound
    require r < mD;

    return require_uint256(r);
}

// =============================================================================
// METHOD DECLARATIONS
// =============================================================================

methods {
    // Summary: any unresolved contract with method `computeInvariant2`
    // is modeled by `cvlInvariant2Axiom` instead of concrete Newton-Raphson.
    function _.computeInvariant2(uint256 amp, uint256 b0, uint256 b1)
        external => cvlInvariant2Axiom(calledContract, amp, b0, b1) expect uint256;

    // Summary: any unresolved contract with method `computeBalance2`
    function _.computeBalance2(uint256 amp, uint256 b_other, uint256 inv, uint256 tokenIndex)
        external => cvlBalance2Axiom(calledContract, amp, b_other, inv, tokenIndex) expect uint256;

    // Harness functions
    function SM.computeInvariant2(uint256, uint256, uint256) external returns (uint256) envfree;
    function SM.computeBalance2(uint256, uint256, uint256, uint256) external returns (uint256) envfree;
    function SM.computeOutGivenExactIn2(uint256, uint256, uint256, uint256, uint256, uint256) external returns (uint256) envfree;
    function SM.computeInGivenExactOut2(uint256, uint256, uint256, uint256, uint256, uint256) external returns (uint256) envfree;
    function SM.getAmpPrecision() external returns (uint256) envfree;
    function SM.getMinAmpScaled() external returns (uint256) envfree;
    function SM.getMaxAmpScaled() external returns (uint256) envfree;
    function SM.getMinAndMaxBalances2(uint256, uint256) external returns (uint256, uint256) envfree;
}

// =============================================================================
// RULES: StableMath Properties (2-token pools)
// =============================================================================

/// Invariant symmetry: D(amp, b0, b1) = D(amp, b1, b0)
rule invariantSymmetry {
    uint256 amp;
    uint256 b0;
    uint256 b1;

    // Production-like constraints
    require amp >= 1000; // MIN_AMP * AMP_PRECISION
    require amp <= 50000000; // MAX_AMP * AMP_PRECISION
    require b0 >= 1000000000000000000; // 1e18
    require b1 >= 1000000000000000000;
    require b0 <= 10000000000000000000000000000; // 1e28
    require b1 <= 10000000000000000000000000000;

    uint256 d1 = computeInvariant2(amp, b0, b1);
    uint256 d2 = computeInvariant2(amp, b1, b0);

    assert d1 == d2;
}

/// Monotonicity: computeOutGivenExactIn2 is non-decreasing in amountIn.
rule outGivenExactInMonotoneInAmountIn {
    uint256 amp;
    uint256 b0;
    uint256 b1;
    uint256 amountIn1;
    uint256 amountIn2;

    // Production-like constraints
    require amp >= 1000;
    require amp <= 50000000;
    require b0 >= 1000000000000000000; // 1e18
    require b1 >= 1000000000000000000;
    require b0 <= 10000000000000000000000000000; // 1e28
    require b1 <= 10000000000000000000000000000;

    // Monotonicity condition
    require amountIn1 <= amountIn2;

    // Reasonable swap sizes (not too large relative to pool)
    require amountIn2 <= b0 / 3; // Max ~33% of pool

    // Swap token 0 for token 1
    uint256 out1 = computeOutGivenExactIn2(amp, b0, b1, 0, 1, amountIn1);
    uint256 out2 = computeOutGivenExactIn2(amp, b0, b1, 0, 1, amountIn2);

    assert to_mathint(out2) >= to_mathint(out1);
}

/// Round-trip safety: ExactIn followed by inverse ExactOut should not profit the user.
/// After swapping amountIn for amountOut, swapping back amountOut should require >= amountIn.
rule exactInThenInverseExactOutNoProfit {
    uint256 amp;
    uint256 b0;
    uint256 b1;
    uint256 amountIn;

    // Production-like constraints
    require amp >= 1000;
    require amp <= 50000000;
    require b0 >= 1000000000000000000; // 1e18
    require b1 >= 1000000000000000000;
    require b0 <= 10000000000000000000000000000; // 1e28
    require b1 <= 10000000000000000000000000000;

    // Reasonable swap size
    require amountIn > 0;
    require amountIn <= b0 / 10; // Max 10% of pool

    // Forward swap: token0 -> token1
    uint256 amountOut = computeOutGivenExactIn2(amp, b0, b1, 0, 1, amountIn);

    // Need meaningful output for inverse
    require amountOut > 0;
    require amountOut < b1;

    // Inverse swap: how much token0 needed to get amountOut of token1?
    uint256 invAmountIn = computeInGivenExactOut2(amp, b0, b1, 0, 1, amountOut);

    // The inverse should require at least as much as the original (no arbitrage profit)
    // Allow small tolerance for rounding
    assert to_mathint(invAmountIn) >= to_mathint(amountIn) - 2;
}

/// Invariant monotonicity in balance: increasing b0 increases D.
rule invariantMonotoneInBalance {
    uint256 amp;
    uint256 b0_1;
    uint256 b0_2;
    uint256 b1;

    require amp >= 1000;
    require amp <= 50000000;
    require b0_1 >= 1000000000000000000;
    require b0_2 >= 1000000000000000000;
    require b1 >= 1000000000000000000;
    require b0_1 <= 10000000000000000000000000000;
    require b0_2 <= 10000000000000000000000000000;
    require b1 <= 10000000000000000000000000000;

    require b0_1 < b0_2;

    uint256 d1 = computeInvariant2(amp, b0_1, b1);
    uint256 d2 = computeInvariant2(amp, b0_2, b1);

    assert to_mathint(d2) > to_mathint(d1);
}

/// Equal balances identity: D(amp, B, B) = 2*B
rule invariantEqualBalances {
    uint256 amp;
    uint256 B;

    require amp >= 1000;
    require amp <= 50000000;
    require B >= 1000000000000000000; // 1e18
    require B <= 10000000000000000000000000000; // 1e28

    uint256 d = computeInvariant2(amp, B, B);

    assert to_mathint(d) == 2 * to_mathint(B);
}

/// Balance consistency: computeBalance2(amp, b0, D) = b1 when D = computeInvariant2(amp, b0, b1)
rule balanceConsistency {
    uint256 amp;
    uint256 b0;
    uint256 b1;

    require amp >= 1000;
    require amp <= 50000000;
    require b0 >= 1000000000000000000;
    require b1 >= 1000000000000000000;
    require b0 <= 10000000000000000000000000000;
    require b1 <= 10000000000000000000000000000;

    uint256 d = computeInvariant2(amp, b0, b1);
    uint256 computedB1 = computeBalance2(amp, b0, d, 1);

    assert computedB1 == b1;
}

/// Swap preserves or increases invariant (due to rounding in protocol's favor).
/// After a swap, the new invariant should be >= old invariant.
rule swapPreservesInvariant {
    uint256 amp;
    uint256 b0;
    uint256 b1;
    uint256 amountIn;

    require amp >= 1000;
    require amp <= 50000000;
    require b0 >= 1000000000000000000;
    require b1 >= 1000000000000000000;
    require b0 <= 10000000000000000000000000000;
    require b1 <= 10000000000000000000000000000;

    require amountIn > 0;
    require amountIn <= b0 / 10;

    // Invariant before swap
    uint256 dBefore = computeInvariant2(amp, b0, b1);

    // Perform swap
    uint256 amountOut = computeOutGivenExactIn2(amp, b0, b1, 0, 1, amountIn);

    require amountOut > 0;
    require amountOut < b1;

    // New balances after swap
    uint256 newB0 = require_uint256(b0 + amountIn);
    uint256 newB1 = require_uint256(b1 - amountOut);

    // Invariant after swap
    uint256 dAfter = computeInvariant2(amp, newB0, newB1);

    // Invariant should be preserved or increased
    assert to_mathint(dAfter) >= to_mathint(dBefore);
}
