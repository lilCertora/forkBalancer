// =============================================================================
// lnSol.spec - Testing the REAL Solidity LogExpMath.ln() implementation
//
// =============================================================================

import "mathSummaries.spec";

methods {
    // Real Solidity implementation via LogExpMathPowPartsHarness
    function ln(int256 a) external returns (int256) envfree;
}

// =============================================================================
// PROPERTY 1: SIGN CORRECTNESS - ln(x) > 0 for x > 1, ln(x) < 0 for x < 1
// =============================================================================

rule ln_solidity_positive_above_one {
    mathint a;
    require a > ONE_18() + MIN_DISTANCE();
    require a <= 1000 * ONE_18();

    mathint result = to_mathint(ln(require_int256(a)));
    assert result > 0, "Solidity ln(x) > 0 for x > 1";
}

rule ln_solidity_negative_below_one {
    mathint a;
    require a >= 1;
    require a < ONE_18() - MIN_DISTANCE();

    mathint result = to_mathint(ln(require_int256(a)));
    assert result < 0, "Solidity ln(x) < 0 for 0 < x < 1";
}

// =============================================================================
// PROPERTY 2: MONOTONICITY - ln is strictly increasing
// This is the hardest property for SMT solvers.
// =============================================================================

rule ln_solidity_monotonic {
    mathint a1;
    mathint a2;
    
    require a1 > 0;
    require a2 <= 1000 * ONE_18();
    require a1 < a2;

    mathint r1 = to_mathint(ln(require_int256(a1)));
    mathint r2 = to_mathint(ln(require_int256(a2)));

    assert r1 < r2, "Solidity ln monotonic in (0, 1000]";
}

// =============================================================================
// PROPERTY 3: CVL APPROXIMATION vs SOLIDITY - Bounded error
// Compares the CVL Taylor series approximation against real Solidity.
// This tests whether our simplified CVL model is a valid abstraction.
// =============================================================================

definition CVL_VS_SOLIDITY_TOLERANCE() returns mathint = 50000000000000000;  // 5e16 (5%)


// VIOLATED : For large inputs, the 4-term Taylor series loses all precision, range is too wide
rule ln_cvl_vs_solidity {
    mathint x;
    require x > 0;
    require x <= 1000 * ONE_18();

    mathint cvl_result = ln_simple(x);
    mathint solidity_result = to_mathint(ln(require_int256(x)));

    mathint diff = cvl_result > solidity_result
        ? cvl_result - solidity_result
        : solidity_result - cvl_result;

    assert diff <= CVL_VS_SOLIDITY_TOLERANCE(), "CVL ln_simple ≈ Solidity ln in (0, 1000]";
}
