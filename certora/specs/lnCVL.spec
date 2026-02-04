// =============================================================================
// lnCVL.spec - Testing properties of the CVL ln_simple() approximation
//
// PURPOSE: Demonstrate SMT solver limitations when verifying properties of
// nonlinear Taylor series implementations in CVL.
//
// ln_simple() is a 4-term Taylor series: ln(x) ≈ 2*(z + z³/3 + z⁵/5 + z⁷/7)
// where z = (x-1)/(x+1)
//
// Properties tested:
//   - Sign: ln(x) > 0 for x > 1, ln(x) < 0 for x < 1
//   - Monotonicity: ln is strictly increasing
// =============================================================================

import "mathSummaries.spec";

// =============================================================================
// PROPERTY 1: SIGN CORRECTNESS - ln(x) > 0 for x > 1, ln(x) < 0 for x < 1
// =============================================================================

rule ln_simple_positive_above_one {
    mathint a;
    require a > ONE_18() + MIN_DISTANCE();
    require a <= 1000 * ONE_18();

    mathint result = ln_simple(a);
    assert result > 0, "ln_simple(x) > 0 for x > 1";
}

rule ln_simple_negative_below_one {
    mathint a;
    require a >= 1;                                  // avoid division by zero
    require a < ONE_18() - MIN_DISTANCE();

    mathint result = ln_simple(a);
    assert result < 0, "ln_simple(x) < 0 for 0 < x < 1";
}

// =============================================================================
// PROPERTY 2: MONOTONICITY - ln is strictly increasing
// Requires minimum gap between inputs to account for CVL approximation precision.
// =============================================================================

// VIOLATION : For large inputs, the 4-term Taylor series loses all precision
rule ln_simple_monotonic {
    mathint a1;
    mathint a2;
    
    require a1 > 0;
    require a2 <= 1000 * ONE_18();
    require a2 > a1 + 1;                             // minimum gap for precision

    mathint r1 = ln_simple(a1);
    mathint r2 = ln_simple(a2);

    assert r1 < r2, "ln_simple monotonic in (0, 1000]";
}
