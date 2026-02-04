// =============================================================================
// ln36CVL.spec - Testing properties of the CVL ln_36_cvl() approximation
//
// ln_36_cvl() is a 3-term Taylor series: ln(1+t) ≈ t - t²/2 + t³/3
// for x close to 1 (range: 0.9 to 1.1).
//
// Domain constraint: x must be in (0.9, 1.1) = (LN_36_LOWER_BOUND, LN_36_UPPER_BOUND)
//
// Properties tested:
//   - Sign: ln(x) > 0 for x > 1, ln(x) < 0 for x < 1
//   - Monotonicity: ln is strictly increasing
// =============================================================================

import "mathSummaries.spec";

// =============================================================================
// PROPERTY 1: SIGN CORRECTNESS - ln(x) > 0 for x > 1, ln(x) < 0 for x < 1
// =============================================================================

rule ln36_positive_above_one {
    mathint x;
    require x > ONE_18();
    require x < LN_36_UPPER_BOUND();

    assert ln_36_cvl(x) > 0, "ln_36_cvl(x) > 0 for x > 1";
}

rule ln36_negative_below_one {
    mathint x;
    require x > LN_36_LOWER_BOUND();
    require x < ONE_18();

    assert ln_36_cvl(x) < 0, "ln_36_cvl(x) < 0 for x < 1";
}

// =============================================================================
// PROPERTY 2: MONOTONICITY - ln is strictly increasing
//
// Requires minimum gap between inputs to account for CVL approximation precision.
// =============================================================================

rule ln36_monotonic {
    mathint a1;
    mathint a2;
    
    require a1 > LN_36_LOWER_BOUND();
    require a2 < LN_36_UPPER_BOUND();
    require a2 > a1 + 1;                             // minimum gap for precision

    mathint r1 = ln_36_cvl(a1);
    mathint r2 = ln_36_cvl(a2);

    assert r1 < r2, "ln_36_cvl monotonic in (0.9, 1.1)";
}
