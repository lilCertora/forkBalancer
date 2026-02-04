// =============================================================================
// expSol.spec - Testing the REAL Solidity LogExpMath.exp() implementation
//
// PURPOSE: Demonstrate SMT solver limitations when verifying properties of
// the actual Solidity exp() implementation from LogExpMath.sol.
//
// Unlike expCVL.spec (which uses a ghosted target), this spec calls the real
// Solidity bytecode. The complex control flow (12 Taylor terms, multiple
// conditionals, 20-decimal intermediate precision) makes SMT reasoning
// extremely difficult.
//
// Expected outcome: Most rules will timeout, demonstrating that formal
// verification of complex nonlinear arithmetic in Solidity is intractable
// for current SMT technology.
// =============================================================================

import "mathSummaries.spec";

methods {
    // Real Solidity implementation via LogExpMathPowPartsHarness
    function exp(int256 x) external returns (int256) envfree;
}

// =============================================================================
// PROPERTY 1: POSITIVITY - exp(x) > 0 for all x
// =============================================================================

rule exp_solidity_positivity_positive_x {
    mathint x;
    require x >= 0;
    require x <= MAX_NATURAL_EXPONENT();

    mathint result = to_mathint(exp(require_int256(x)));
    assert result > 0, "Solidity exp(x) > 0 for x >= 0";
}

rule exp_solidity_positivity_negative_x {
    mathint x;
    require x >= MIN_NATURAL_EXPONENT();
    require x < 0;

    mathint result = to_mathint(exp(require_int256(x)));
    assert result > 0, "Solidity exp(x) > 0 for x < 0";
}

// =============================================================================
// PROPERTY 2: THRESHOLD - exp(x) > 1 for x > 0, exp(x) < 1 for x < 0
// =============================================================================

rule exp_solidity_gt_one_for_positive {
    mathint x;
    require x > MIN_DISTANCE();
    require x <= MAX_NATURAL_EXPONENT();

    mathint result = to_mathint(exp(require_int256(x)));
    assert result > ONE_18(), "Solidity exp(x) > 1 for x > 0";
}

rule exp_solidity_lt_one_for_negative {
    mathint x;
    require x >= MIN_NATURAL_EXPONENT();
    require x < -MIN_DISTANCE();

    mathint result = to_mathint(exp(require_int256(x)));
    assert result < ONE_18(), "Solidity exp(x) < 1 for x < 0";
}

// =============================================================================
// PROPERTY 3: MONOTONICITY - exp is strictly increasing
// This is the hardest property for SMT solvers.
// =============================================================================

rule exp_solidity_monotonic {
    mathint x1;
    mathint x2;

    require x1 >= MIN_NATURAL_EXPONENT();
    require x2 <= MAX_NATURAL_EXPONENT();
    require x1 < x2;

    mathint r1 = to_mathint(exp(require_int256(x1)));
    mathint r2 = to_mathint(exp(require_int256(x2)));

    assert r1 < r2, "Solidity exp monotonic across full domain";
}

// =============================================================================
// PROPERTY 4: CVL APPROXIMATION vs SOLIDITY - Bounded error
// Compares the CVL Taylor series approximation against real Solidity.
// This tests whether our simplified CVL model is a valid abstraction.
// =============================================================================

definition CVL_VS_SOLIDITY_TOLERANCE() returns mathint = 100000000000000000; // 1e17 (10%)

rule exp_cvl_vs_solidity_positive {
    mathint x;
    require x >= 0;
    require x <= 20 * ONE_18();                     // [0, 20]

    mathint cvl_result = exp_simple(x);
    mathint solidity_result = to_mathint(exp(assert_int256(x)));

    mathint diff = cvl_result > solidity_result
        ? cvl_result - solidity_result
        : solidity_result - cvl_result;

    assert diff <= CVL_VS_SOLIDITY_TOLERANCE(), "CVL exp_simple ≈ Solidity exp in [0, 20]";
}

rule exp_cvl_vs_solidity_negative {
    mathint x;
    require x >= -20 * ONE_18();
    require x <= 0;                                  // [-20, 0]

    mathint cvl_result = exp_simple(x);
    mathint solidity_result = to_mathint(exp(assert_int256(x)));

    mathint diff = cvl_result > solidity_result
        ? cvl_result - solidity_result
        : solidity_result - cvl_result;

    assert diff <= CVL_VS_SOLIDITY_TOLERANCE(), "CVL exp_simple ≈ Solidity exp in [-20, 0]";
}
