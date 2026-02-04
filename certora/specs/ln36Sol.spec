// =============================================================================
// ln36Sol.spec - Testing the REAL Solidity LogExpMath._ln_36() implementation
//
// Domain constraint: x must be in (0.9, 1.1) = (LN_36_LOWER_BOUND, LN_36_UPPER_BOUND)
//
// =============================================================================

import "mathSummaries.spec";

methods {
    // Real Solidity implementation via LogExpMathPowPartsHarness
    function ln_36(int256 x) external returns (int256) envfree;
}

// =============================================================================
// PROPERTY 1: SIGN CORRECTNESS - ln(x) > 0 for x > 1, ln(x) < 0 for x < 1
// =============================================================================

rule ln36_positive_above_one {
    mathint x;
    require x > ONE_18();
    require x < LN_36_UPPER_BOUND();

    mathint r = to_mathint(ln_36(require_int256(x)));
    assert r > 0, "Solidity ln_36(x) > 0 for x > 1";
}

rule ln36_negative_below_one {
    mathint x;
    require x > LN_36_LOWER_BOUND();
    require x < ONE_18();

    mathint r = to_mathint(ln_36(require_int256(x)));
    assert r < 0, "Solidity ln_36(x) < 0 for x < 1";
}

// =============================================================================
// PROPERTY 2: MONOTONICITY - ln is strictly increasing
// Full domain (0.9, 1.1) - this is the maximum valid range for ln_36.
// =============================================================================

rule ln36_monotonic {
    mathint a1;
    mathint a2;
    
    require a1 > LN_36_LOWER_BOUND();
    require a2 < LN_36_UPPER_BOUND();
    require a1 < a2;

    mathint r1 = to_mathint(ln_36(require_int256(a1)));
    mathint r2 = to_mathint(ln_36(require_int256(a2)));

    assert r1 < r2, "Solidity ln_36 monotonic in (0.9, 1.1)";
}

// =============================================================================
// PROPERTY 3: CVL APPROXIMATION vs SOLIDITY - Bounded error
// Compares the CVL Taylor series approximation against real Solidity.
// This tests whether our simplified CVL model is a valid abstraction.
// =============================================================================

definition CVL_VS_SOLIDITY_TOLERANCE() returns mathint = 100000000000000000000000000000000;  // 1e32

rule ln36_cvl_vs_solidity {
    mathint x;
    require x > LN_36_LOWER_BOUND();
    require x < LN_36_UPPER_BOUND();

    mathint cvl_result = ln_36_cvl(x);
    mathint solidity_result = to_mathint(ln_36(require_int256(x)));

    mathint diff = cvl_result > solidity_result
        ? cvl_result - solidity_result
        : solidity_result - cvl_result;

    assert diff <= CVL_VS_SOLIDITY_TOLERANCE(), "CVL ln_36_cvl ≈ Solidity ln_36 in (0.9, 1.1)";
}
