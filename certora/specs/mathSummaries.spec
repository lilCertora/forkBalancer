// =============================================================================
// mathSummaries.spec - CVL implementations of LogExpMath functions
//
// This file provides CVL (Certora Verification Language) implementations of
// the core mathematical functions from LogExpMath.sol:
//   - ln_simple:  Natural logarithm (4-term Taylor series)
//   - ln_36_cvl:  High-precision ln for x near 1 (3-term Taylor series)
//   - exp_simple: Natural exponential (5-term Taylor series)
//   - pow_cvl:    Power function via exp(y * ln(x))
//
// These CVL functions use fewer Taylor terms than Solidity for two reasons:
//   1. Efficiency: More terms = harder for SMT solvers
//   2. Demonstration: Even simplified versions cause SMT timeouts
//
// Also provides utility functions and constants matching LogExpMath.sol.
// =============================================================================

// =============================================================================
// CONSTANTS (matching LogExpMath.sol)
// =============================================================================

definition ONE_18() returns mathint = 1000000000000000000;   // 1e18
definition ONE_36() returns mathint = 1000000000000000000000000000000000000;  // 1e36

// =============================================================================
// div_sol - Solidity-compatible signed integer division
//
// CVL mathint uses floor division (truncates toward negative infinity).
// Solidity uses truncation toward zero for signed division.
// This function mimics Solidity's behavior.
//
// =============================================================================

function div_sol(mathint a, mathint b) returns mathint {
    // Solidity truncates toward zero
    // For negative results, we need to adjust CVL's floor division
    mathint quotient = a / b;
    mathint remainder = a - quotient * b;
    
    // If there's a remainder and the signs of a and b differ (negative result),
    // CVL floored too far negative, so add 1 to truncate toward zero
    if (remainder != 0 && ((a < 0 && b > 0) || (a > 0 && b < 0))) {
        return quotient + 1;
    }
    return quotient;
}

// Domain bounds for ln_36
definition LN_36_LOWER_BOUND() returns mathint = 900000000000000000;   // 0.9e18
definition LN_36_UPPER_BOUND() returns mathint = 1100000000000000000;  // 1.1e18

// Minimum distance from 1 to avoid precision loss in ln_simple
definition MIN_DISTANCE() returns mathint = 1000000000000000;  // 1e15 (0.1% buffer)

// exp domain bounds
definition MAX_NATURAL_EXPONENT() returns mathint = 130000000000000000000;   // 130e18
definition MIN_NATURAL_EXPONENT() returns mathint = -41000000000000000000;   // -41e18

// =============================================================================
// ln_36_cvl - For x in (0.9, 1.1), returns 36-decimal result
//
// Taylor series: ln(x) = 2 * (z + z³/3 + z⁵/5)
// where z = (x - 1) / (x + 1)
// 3 terms - efficient for prover while preserving mathematical properties.
//
// IMPORTANT: Uses div_sol for Solidity-compatible division semantics.
// When x < 1, intermediate values are negative, and CVL's floor division
// differs from Solidity's truncation-toward-zero.
// =============================================================================


function ln_36_cvl(mathint x) returns mathint {
    // t is 18-decimal (can be negative)
    mathint t = x - ONE_18();

    // Compute powers in 18-decimal fixed point:
    // t2 = t^2 (18-dec), t3 = t^3 (18-dec)
    mathint t2 = div_sol(t * t, ONE_18());
    mathint t3 = div_sol(t2 * t, ONE_18());

    // ln(1+t) ≈ t - t^2/2 + t^3/3   (18-dec)
    mathint ln_18 = t - div_sol(t2, 2) + div_sol(t3, 3);

    // Upscale to 36-decimal result
    return ln_18 * ONE_18();
}

// =============================================================================
// ln_simple - For any x > 0, returns 18-decimal result
//
// Taylor series: ln(x) = 2 * (z + z³/3 + z⁵/5 + z⁷/7)
// where z = (x - 1) / (x + 1)
// Handles x < 1 via: ln(a) = -ln(1/a)
// 4 terms, works for general domain.
// =============================================================================

function ln_simple(mathint a) returns mathint {
    // For a < 1, use ln(a) = -ln(1/a)
    bool isLessThanOne = a < ONE_18();
    mathint x = isLessThanOne ? (ONE_18() * ONE_18()) / a : a;
    
    // z = (x - 1) / (x + 1)
    mathint z = ((x - ONE_18()) * ONE_18()) / (x + ONE_18());
    mathint z_squared = (z * z) / ONE_18();
    
    // Series terms
    mathint term1 = z;                                    // z
    mathint term3 = (term1 * z_squared) / ONE_18() / 3;   // z³/3
    mathint term5 = (term3 * z_squared) / ONE_18() * 3 / 5;  // z⁵/5
    mathint term7 = (term5 * z_squared) / ONE_18() * 5 / 7;  // z⁷/7
    
    mathint series = term1 + term3 + term5 + term7;
    mathint result = series * 2;
    
    return isLessThanOne ? -result : result;
}

// =============================================================================
// exp_simple - For any x, returns 18-decimal result
//
// Taylor series: e^x = 1 + x + x²/2! + x³/3! + x⁴/4!
// For negative x: alternating signs
// 5 terms - efficient for prover while preserving mathematical properties.
// =============================================================================

function exp_simple(mathint x) returns mathint {
    bool isNegative = x < 0;
    mathint abs_x = isNegative ? -x : x;
    
    // Taylor series terms (working in 18 decimals)
    mathint term0 = ONE_18();                                           // 1
    mathint term1 = abs_x;                                              // x
    mathint term2 = (term1 * abs_x) / ONE_18() / 2;                     // x²/2
    mathint term3 = (term2 * abs_x) / ONE_18() / 3;                     // x³/6
    mathint term4 = (term3 * abs_x) / ONE_18() / 4;                     // x⁴/24
    
    if (isNegative) {
        return term0 - term1 + term2 - term3 + term4;
    } else {
        return term0 + term1 + term2 + term3 + term4;
    }
}

// =============================================================================
// pow_cvl - pow(x, y) = exp(y * ln(x)) for x in ln_36 window
// =============================================================================

function pow_cvl(mathint x, mathint y) returns mathint {
    // x must be in (0.9e18, 1.1e18)
    mathint ln_x_36 = ln_36_cvl(x);
    
    // Split multiply (matches Solidity LogExpMath.pow)
    mathint logx_times_y = (ln_x_36 / ONE_18()) * y + ((ln_x_36 % ONE_18()) * y) / ONE_18();
    mathint exponent = logx_times_y / ONE_18();
    
    return exp_simple(exponent);
}


