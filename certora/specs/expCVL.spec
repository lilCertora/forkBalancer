// =============================================================================
// expCVL.spec - Testing properties of the CVL exp_simple() approximation
//
// PURPOSE: Demonstrate SMT solver limitations when verifying properties of
// nonlinear Taylor series implementations in CVL.
//
// exp_simple() is a 5-term Taylor series: e^x ≈ 1 + x + x²/2! + x³/3! + x⁴/4!
//
// LIMITATION: This CVL approximation has limited precision due to:
//   1. Fixed-point arithmetic with division truncation
//   2. Only 5 Taylor terms (vs 12 in Solidity)
//   3. Taylor series diverges for large |x|
//
// Properties tested:
//   - Positivity: exp(x) > 0 for all x
//   - Threshold: exp(x) > 1 for x > 0, exp(x) < 1 for x < 0
//   - Monotonicity: exp is strictly increasing
//   - Product rule: exp(x+y) ≈ exp(x) * exp(y)
// =============================================================================

import "mathSummaries.spec";

// =============================================================================
// PROPERTY 1: POSITIVITY - exp(x) > 0 for all x
// Tests if the CVL Taylor series maintains positivity across the full domain.
// =============================================================================

rule exp_simple_positivity {
    mathint x;
    require x >= MIN_NATURAL_EXPONENT();
    require x <= MAX_NATURAL_EXPONENT();

    mathint result = exp_simple(x);
    assert result > 0, "exp_simple(x) > 0 for all x in domain";
}

// =============================================================================
// PROPERTY 2: THRESHOLD - exp(x) > 1 for x > 0, exp(x) < 1 for x < 0
// Tests the fundamental threshold behavior of exponential.
// =============================================================================

rule exp_simple_gt_one_for_positive {
    mathint x;
    require x > MIN_DISTANCE();
    require x <= MAX_NATURAL_EXPONENT();

    mathint result = exp_simple(x);
    assert result > ONE_18(), "exp_simple(x) > 1 for x > 0";
}


// VIOLATION : 5-term Taylor series 1 - x + x²/2 - x³/6 + x⁴/24 diverges for large |x|
rule exp_simple_lt_one_for_negative {
    mathint x;
    require x >= MIN_NATURAL_EXPONENT();
    require x < -MIN_DISTANCE();

    mathint result = exp_simple(x);
    assert result < ONE_18(), "exp_simple(x) < 1 for x < 0";
}

// =============================================================================
// PROPERTY 3: MONOTONICITY - exp is strictly increasing
// This is the hardest property for SMT solvers with nonlinear arithmetic.
// =============================================================================


// VIOLATION : 5-term Taylor series 1 - x + x²/2 - x³/6 + x⁴/24 diverges for large |x|
rule exp_simple_monotonic {
    mathint x1;
    mathint x2;

    require x1 >= MIN_NATURAL_EXPONENT();
    require x2 <= MAX_NATURAL_EXPONENT();
    require x2 > x1 + 1;                             // minimum gap for precision

    mathint r1 = exp_simple(x1);
    mathint r2 = exp_simple(x2);

    assert r1 < r2, "exp_simple monotonic across full domain";
}

// =============================================================================
// PROPERTY 4: PRODUCT RULE - exp(x+y) ≈ exp(x) * exp(y)
// Fundamental exponential identity. Uses tolerance due to Taylor approximation.
// =============================================================================

definition EXP_TOLERANCE() returns mathint = 200000000000000000;  // 2e17 (20%)


// VIOLATION : 5-term Taylor series 1 - x + x²/2 - x³/6 + x⁴/24 diverges for large |x|
rule exp_simple_product_rule {
    mathint x;
    mathint y;
    
    require x >= 100000000000000000;                // 0.1
    require x <= 2000000000000000000;               // 2.0
    require y >= 100000000000000000;                // 0.1
    require y <= 2000000000000000000;               // 2.0

    mathint exp_x = exp_simple(x);
    mathint exp_y = exp_simple(y);
    mathint exp_xy = exp_simple(x + y);

    mathint product = (exp_x * exp_y) / ONE_18();
    mathint diff = exp_xy > product ? exp_xy - product : product - exp_xy;

    assert diff <= EXP_TOLERANCE(), "exp_simple(x+y) ≈ exp_simple(x) * exp_simple(y)";
}
