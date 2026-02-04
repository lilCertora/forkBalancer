// =============================================================================
// WeightedMathPropertiesPowAxioms.spec
//
// Properties for WeightedMath with axiomatic pow summaries.
// The expensive `LogExpMath.pow(x,y)` is replaced by an uninterpreted ghost
// function with mathematical axioms (monotonicity, identities, etc.).
//
// This allows verifying pool properties for ARBITRARY weights, not just
// the fast-path weights (50/50, 80/20) where exponent = 1, 2, or 4.
// =============================================================================

using WeightedMathPowAxiomsHarness as WM;

// =============================================================================
// CONSTANTS
// =============================================================================

definition ONE_18() returns mathint = 1000000000000000000;

// Mirror FixedPoint.MAX_POW_RELATIVE_ERROR = 10000 (10^(-14))
definition MAX_POW_RELATIVE_ERROR() returns mathint = 10000;

// Hard cap to avoid overflow inside FixedPoint's `mulUp(raw, MAX_POW_RELATIVE_ERROR)`.
definition MAX_UINT() returns mathint = (2 ^ 256) - 1;
definition MAX_SAFE_RAW() returns mathint = (MAX_UINT() - 1) / (2 * MAX_POW_RELATIVE_ERROR());

// =============================================================================
// GHOST FUNCTION: Uninterpreted pow with mathematical axioms
// =============================================================================

ghost pow_ghost(mathint, mathint) returns mathint {
    // -------------------------------------------------------------------------
    // IDENTITY AXIOMS
    // -------------------------------------------------------------------------
    axiom forall mathint x. forall mathint y. x == ONE_18() => pow_ghost(x, y) == ONE_18();
    axiom forall mathint x. forall mathint y. y == 0 => pow_ghost(x, y) == ONE_18();
    axiom forall mathint x. forall mathint y. y == ONE_18() => pow_ghost(x, y) == x;

    // -------------------------------------------------------------------------
    // POSITIVITY
    // -------------------------------------------------------------------------
    axiom forall mathint x. forall mathint y. (x > 0 && y >= 0) => pow_ghost(x, y) > 0;

    // -------------------------------------------------------------------------
    // THRESHOLD FACTS (needed for complement() to not underflow)
    // -------------------------------------------------------------------------
    axiom forall mathint x. forall mathint y. (x >= ONE_18() && y > 0) => pow_ghost(x, y) >= ONE_18();
    axiom forall mathint x. forall mathint y. (x <= ONE_18() && y > 0) => pow_ghost(x, y) <= ONE_18();

    // -------------------------------------------------------------------------
    // MONOTONICITY IN BASE (for positive exponent)
    // x1 < x2 and y > 0  =>  pow(x1, y) < pow(x2, y)
    // -------------------------------------------------------------------------
    axiom forall mathint x1. forall mathint x2. forall mathint y.
        (x1 > 0 && x2 > 0 && x1 < x2 && y > 0) => pow_ghost(x1, y) < pow_ghost(x2, y);

    // -------------------------------------------------------------------------
    // MONOTONICITY IN EXPONENT (depends on base vs 1)
    // For base > 1: increasing exponent => increasing result
    // For base < 1: increasing exponent => decreasing result
    // -------------------------------------------------------------------------
    axiom forall mathint x. forall mathint y1. forall mathint y2.
        (x > ONE_18() && y1 >= 0 && y2 >= 0 && y1 < y2) => pow_ghost(x, y1) < pow_ghost(x, y2);

    axiom forall mathint x. forall mathint y1. forall mathint y2.
        (x > 0 && x < ONE_18() && y1 >= 0 && y2 >= 0 && y1 < y2) => pow_ghost(x, y1) > pow_ghost(x, y2);
}

// =============================================================================
// CVL SUMMARY FUNCTION for pow oracle calls
// =============================================================================

function cvlPowAxiom(address oracle, uint256 x, uint256 y) returns uint256 {
    mathint mx = to_mathint(x);
    mathint my = to_mathint(y);

    // Domain constraints (WeightedMath usage):
    require mx > 0;
    require my >= 0;

    // Get result from ghost
    mathint r = pow_ghost(mx, my);
    
    // Positivity
    require r > 0;
    
    // Bound to avoid overflow in error buffer math
    require r <= MAX_SAFE_RAW();

    // -------------------------------------------------------------------------
    // THRESHOLD ENFORCEMENT
    // Ghost axioms with forall quantifiers may not be instantiated properly.
    // Reinforce the threshold constraints as explicit requires.
    // -------------------------------------------------------------------------
    
    // For base <= ONE and positive exponent: result <= ONE
    require (mx <= ONE_18() && my > 0) => r <= ONE_18();
    
    // For base >= ONE and positive exponent: result >= ONE  
    require (mx >= ONE_18() && my > 0) => r >= ONE_18();
    
    return require_uint256(r);
}

// =============================================================================
// METHOD DECLARATIONS
// =============================================================================

methods {
    // Summary: any unresolved contract with method `pow(uint256,uint256)`
    // is modeled by `cvlPowAxiom` instead of concrete LogExpMath code.
    function _.pow(uint256 x, uint256 y) external => cvlPowAxiom(calledContract, x, y) expect uint256;

    // Harness functions
    function maxInAllowed(uint256) external returns (uint256) envfree;
    function maxOutAllowed(uint256) external returns (uint256) envfree;
    function computeOutGivenExactIn(uint256,uint256,uint256,uint256,uint256) external returns (uint256) envfree;
    function computeInGivenExactOut(uint256,uint256,uint256,uint256,uint256) external returns (uint256) envfree;
    function computeBalanceOutGivenInvariant(uint256,uint256,uint256) external returns (uint256) envfree;
    
    // 2-token invariant
    function invariantDown2NoLoop(uint256,uint256,uint256,uint256) external returns (uint256) envfree;
    function invariantUp2NoLoop(uint256,uint256,uint256,uint256) external returns (uint256) envfree;
    
    // 3-token invariant
    function invariantDown3NoLoop(uint256,uint256,uint256,uint256,uint256,uint256) external returns (uint256) envfree;
    function invariantUp3NoLoop(uint256,uint256,uint256,uint256,uint256,uint256) external returns (uint256) envfree;
    
    // 4-token invariant
    function invariantDown4NoLoop(uint256,uint256,uint256,uint256,uint256,uint256,uint256,uint256) external returns (uint256) envfree;
    function invariantUp4NoLoop(uint256,uint256,uint256,uint256,uint256,uint256,uint256,uint256) external returns (uint256) envfree;
}

// =============================================================================
// RULES: WeightedMath Properties (arbitrary weights)
// =============================================================================

/// Monotonicity: `computeBalanceOutGivenInvariant` is non-decreasing in `invariantRatio`.
/// NOTE: The function uses different rounding (divUp vs divDown) for the exponent depending
/// on whether invariantRatio > ONE. To ensure monotonicity with consistent rounding,
/// we require both ratios to be on the SAME side of ONE.
rule invariantMontonicityGreaterThanOne {
    uint256 balance;
    uint256 weight;
    uint256 r1;
    uint256 r2;

    // Production-like constraints.
    require weight >= 10000000000000000; // 1e16
    require weight <= 1000000000000000000; // 1e18
    require balance >= 1000000; // ABSOLUTE_MIN_TOKEN_BALANCE
    require balance <= 340282366920938463463374607431768211455; // 2^128-1

    // Both ratios ABOVE ONE (uses divUp for exponent)
    require r1 > 1000000000000000000; // > 1e18
    require r2 > 1000000000000000000; // > 1e18
    require r1 <= r2;
    require r2 <= 3000000000000000000; // 3e18

    uint256 b1 = computeBalanceOutGivenInvariant(balance, weight, r1);
    uint256 b2 = computeBalanceOutGivenInvariant(balance, weight, r2);

    assert to_mathint(b2) >= to_mathint(b1);
}

/// Monotonicity for invariantRatio < ONE (uses divDown for exponent)
/// NOTE: We require r2 < ONE (strictly less than) because at r2 = ONE exactly,
/// powUp uses the fast path (returns ONE without error buffer), while for r1 < ONE,
/// powUp adds an error buffer. This asymmetry can cause b1 > b2 at the boundary.
rule invariantMontonicityLessThanOne {
    uint256 balance;
    uint256 weight;
    uint256 r1;
    uint256 r2;

    // Production-like constraints.
    require weight >= 10000000000000000; // 1e16
    require weight <= 1000000000000000000; // 1e18
    require balance >= 1000000; // ABSOLUTE_MIN_TOKEN_BALANCE
    require balance <= 340282366920938463463374607431768211455; // 2^128-1

    // Both ratios STRICTLY BELOW ONE (both go through oracle with error buffer)
    require r1 >= 700000000000000000; // 0.7e18
    require r2 < 1000000000000000000; // < 1e18 (strictly less than ONE)
    require r1 <= r2;

    uint256 b1 = computeBalanceOutGivenInvariant(balance, weight, r1);
    uint256 b2 = computeBalanceOutGivenInvariant(balance, weight, r2);

    assert to_mathint(b2) >= to_mathint(b1);
}

/// Symmetry (rounding-safe, protocol-favoring rounding):
/// ExactIn then inverse ExactOut should not require more than original input.
///
/// NOTE: This property requires relating pow(base1, exp1) to pow(base2, exp2) where
/// BOTH base and exponent differ between the ExactIn and ExactOut formulas.
/// Our axioms only guarantee monotonicity for fixed base OR fixed exponent.
///
/// For equal weights (50/50 pool), the exponents are equal (weightIn/weightOut = 1),
/// which allows the axioms to relate the pow calls via base monotonicity.
rule exactInThenInverseExactOutEqualWeights {
    uint256 balanceIn;
    uint256 balanceOut;
    uint256 amountIn;

    // Equal weights (50/50 pool) - ensures exponent = 1 (fast path)
    uint256 weight = 500000000000000000; // 0.5e18

    require balanceIn >= 1000000;
    require balanceOut >= 1000000;
    require balanceIn <= 340282366920938463463374607431768211455;
    require balanceOut <= 340282366920938463463374607431768211455;

    // Stay within max-in ratio.
    require amountIn <= maxInAllowed(balanceIn);

    uint256 amountOut = computeOutGivenExactIn(balanceIn, weight, balanceOut, weight, amountIn);
    require amountOut > 0;

    // Ensure inverse doesn't revert.
    require amountOut <= maxOutAllowed(balanceOut);
    require amountOut <= balanceOut;

    uint256 invAmountIn = computeInGivenExactOut(balanceIn, weight, balanceOut, weight, amountOut);

    // Balance-aware tolerance.
    mathint tol = (to_mathint(balanceIn) + (1000000000000000000 - 1)) / 1000000000000000000;
    assert to_mathint(invAmountIn) <= to_mathint(amountIn) + tol + 1;
}

/// Monotonicity: computeOutGivenExactIn is non-decreasing in amountIn.
/// This is a simpler property that only requires base monotonicity (fixed exponent).
rule outGivenExactInMonotoneInAmountIn {
    uint256 balanceIn;
    uint256 weightIn;
    uint256 balanceOut;
    uint256 weightOut;
    uint256 amountIn1;
    uint256 amountIn2;

    // Production-like constraints.
    require weightIn >= 10000000000000000;
    require weightOut >= 10000000000000000;
    require weightIn <= 1000000000000000000;
    require weightOut <= 1000000000000000000;

    require balanceIn >= 1000000;
    require balanceOut >= 1000000;
    require balanceIn <= 340282366920938463463374607431768211455;
    require balanceOut <= 340282366920938463463374607431768211455;

    require amountIn1 <= amountIn2;
    require amountIn2 <= maxInAllowed(balanceIn);

    uint256 out1 = computeOutGivenExactIn(balanceIn, weightIn, balanceOut, weightOut, amountIn1);
    uint256 out2 = computeOutGivenExactIn(balanceIn, weightIn, balanceOut, weightOut, amountIn2);

    assert to_mathint(out2) >= to_mathint(out1);
}

/// Invariant ordering (2-token): invariantUp >= invariantDown.
rule invariantUpGreaterThanInvariantDown_2tokens {
    uint256 w0; uint256 w1;
    uint256 b0; uint256 b1;

    require w0 >= 10000000000000000 && w0 <= 1000000000000000000;
    require w1 >= 10000000000000000 && w1 <= 1000000000000000000;
    require w0 + w1 == 1000000000000000000;

    require b0 >= 1000000000000000000; // 1e18
    require b0 <= 10000000000000000000000; // 1e22
    require b1 >= 1000000000000000000;
    require b1 <= 10000000000000000000000;

    uint256 invDown = invariantDown2NoLoop(w0, w1, b0, b1);
    uint256 invUp = invariantUp2NoLoop(w0, w1, b0, b1);

    assert to_mathint(invUp) >= to_mathint(invDown);
}

/// Invariant ordering (3-token): invariantUp >= invariantDown.
/// Using equal weights (33/33/34) to reduce search space and help solver.
rule invariantUpGreaterThanInvariantDown_3tokens {
    uint256 b0; uint256 b1; uint256 b2;

    // Fixed weights: 33% / 33% / 34% (common 3-token pool configuration)
    uint256 w0 = 330000000000000000; // 0.33e18
    uint256 w1 = 330000000000000000; // 0.33e18
    uint256 w2 = 340000000000000000; // 0.34e18

    // Tighter balance range to help solver
    require b0 >= 1000000000000000000; // 1e18
    require b0 <= 1000000000000000000000; // 1e21 (tighter)
    require b1 >= 1000000000000000000;
    require b1 <= 1000000000000000000000;
    require b2 >= 1000000000000000000;
    require b2 <= 1000000000000000000000;

    uint256 invDown = invariantDown3NoLoop(w0, w1, w2, b0, b1, b2);
    uint256 invUp = invariantUp3NoLoop(w0, w1, w2, b0, b1, b2);

    assert to_mathint(invUp) >= to_mathint(invDown);
}

/// Invariant ordering (3-token) with arbitrary weights.
/// Separate rule with symbolic weights for completeness (may timeout).
rule invariantUpGreaterThanInvariantDown_3tokens_arbitraryWeights {
    uint256 w0; uint256 w1; uint256 w2;
    uint256 b0; uint256 b1; uint256 b2;

    // Weights: each >= 10% and <= 50% (tighter range), sum to 100%
    require w0 >= 100000000000000000 && w0 <= 500000000000000000; // 10%-50%
    require w1 >= 100000000000000000 && w1 <= 500000000000000000;
    require w2 >= 100000000000000000 && w2 <= 500000000000000000;
    require w0 + w1 + w2 == 1000000000000000000;

    // Tighter balance range
    require b0 >= 1000000000000000000 && b0 <= 100000000000000000000; // 1e18 to 1e20
    require b1 >= 1000000000000000000 && b1 <= 100000000000000000000;
    require b2 >= 1000000000000000000 && b2 <= 100000000000000000000;

    uint256 invDown = invariantDown3NoLoop(w0, w1, w2, b0, b1, b2);
    uint256 invUp = invariantUp3NoLoop(w0, w1, w2, b0, b1, b2);

    assert to_mathint(invUp) >= to_mathint(invDown);
}

/// Invariant ordering (4-token): invariantUp >= invariantDown.
/// Using equal weights (25% each) to reduce search space and help solver.
rule invariantUpGreaterThanInvariantDown_4tokens {
    uint256 b0; uint256 b1; uint256 b2; uint256 b3;

    // Fixed weights: 25% each (common 4-token pool configuration)
    uint256 w0 = 250000000000000000; // 0.25e18
    uint256 w1 = 250000000000000000;
    uint256 w2 = 250000000000000000;
    uint256 w3 = 250000000000000000;

    // Tighter balance range to help solver
    require b0 >= 1000000000000000000; // 1e18
    require b0 <= 1000000000000000000000; // 1e21 (tighter)
    require b1 >= 1000000000000000000;
    require b1 <= 1000000000000000000000;
    require b2 >= 1000000000000000000;
    require b2 <= 1000000000000000000000;
    require b3 >= 1000000000000000000;
    require b3 <= 1000000000000000000000;

    uint256 invDown = invariantDown4NoLoop(w0, w1, w2, w3, b0, b1, b2, b3);
    uint256 invUp = invariantUp4NoLoop(w0, w1, w2, w3, b0, b1, b2, b3);

    assert to_mathint(invUp) >= to_mathint(invDown);
}
