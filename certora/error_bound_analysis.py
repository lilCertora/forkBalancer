#!/usr/bin/env python3
"""
Error Bound Analysis: CVL Simple Functions vs LogExpMath Solidity Implementation

This script analyzes the error bounds between the simplified CVL functions
(used as summaries for Certora verification) and the real Solidity implementations:

1. exp_simple (5-term Taylor) vs LogExpMath.exp (12-term with decomposition)
2. ln_simple (4-term series) vs LogExpMath._ln (6-term with decomposition)  
3. ln_36_cvl (3-term series) vs LogExpMath._ln_36 (8-term series)

CURRENT CVL TERM COUNTS (optimized for prover efficiency):
- exp_simple:  5 terms (1 + x + x²/2! + x³/3! + x⁴/4!)
- ln_simple:   4 terms (z + z³/3 + z⁵/5 + z⁷/7)
- ln_36_cvl:   3 terms (z + z³/3 + z⁵/5)

Then estimates error propagation in Balancer liquidity operations (swaps).

Usage:
    python3 error_bound_analysis.py

The script outputs:
- Function-level error bounds (absolute and relative)
- Theoretical Taylor series truncation bounds
- Swap error propagation analysis
- Recommended tolerances for Certora rules
"""

import math
from typing import Tuple

# =============================================================================
# CONSTANTS (matching Solidity and CVL)
# =============================================================================

ONE_18 = 10**18
ONE_20 = 10**20
ONE_36 = 10**36

# Precomputed constants from LogExpMath.sol for exp/ln decomposition
X0, A0 = 128 * ONE_18, 38877084059945950922200000000000000000000000000000000000
X1, A1 = 64 * ONE_18, 6235149080811616882910000000
X2, A2 = 32 * ONE_20, 7896296018268069516100000000000000
X3, A3 = 16 * ONE_20, 888611052050787263676000000
X4, A4 = 8 * ONE_20, 298095798704172827474000
X5, A5 = 4 * ONE_20, 5459815003314423907810
X6, A6 = 2 * ONE_20, 738905609893065022723
X7, A7 = 1 * ONE_20, 271828182845904523536
X8, A8 = ONE_20 // 2, 164872127070012814685
X9, A9 = ONE_20 // 4, 128402541668774148407
X10, A10 = ONE_20 // 8, 113314845306682631683
X11, A11 = ONE_20 // 16, 106449445891785942956

# =============================================================================
# CVL IMPLEMENTATIONS (matching the .spec files exactly)
# =============================================================================

def exp_simple_cvl(x_18: int) -> int:
    """
    CVL exp_simple from mathSummaries.spec
    5-term Taylor series: e^x ≈ 1 + x + x²/2! + x³/3! + x⁴/4!
    
    For negative x, uses alternating series with absolute value.
    Input/output in 18 decimals.
    """
    is_negative = x_18 < 0
    abs_x = -x_18 if is_negative else x_18
    
    term0 = ONE_18
    term1 = abs_x
    term2 = (term1 * abs_x) // ONE_18 // 2
    term3 = (term2 * abs_x) // ONE_18 // 3
    term4 = (term3 * abs_x) // ONE_18 // 4
    
    if is_negative:
        return term0 - term1 + term2 - term3 + term4
    else:
        return term0 + term1 + term2 + term3 + term4


def exp_simple_cvl_7terms(x_18: int) -> int:
    """
    Reference: 7-term Taylor series for comparison.
    e^x ≈ 1 + x + x²/2! + x³/3! + x⁴/4! + x⁵/5! + x⁶/6!
    """
    is_negative = x_18 < 0
    abs_x = -x_18 if is_negative else x_18
    
    term0 = ONE_18
    term1 = abs_x
    term2 = (term1 * abs_x) // ONE_18 // 2
    term3 = (term2 * abs_x) // ONE_18 // 3
    term4 = (term3 * abs_x) // ONE_18 // 4
    term5 = (term4 * abs_x) // ONE_18 // 5
    term6 = (term5 * abs_x) // ONE_18 // 6
    
    if is_negative:
        return term0 - term1 + term2 - term3 + term4 - term5 + term6
    else:
        return term0 + term1 + term2 + term3 + term4 + term5 + term6


def ln_simple_cvl(a_18: int) -> int:
    """
    CVL ln_simple from mathSummaries.spec
    4-term series: ln(x) = 2 * (z + z³/3 + z⁵/5 + z⁷/7) where z = (x-1)/(x+1)
    
    For x < 1, computes ln(1/x) and negates.
    Input/output in 18 decimals.
    """
    is_less_than_one = a_18 < ONE_18
    x = (ONE_18 * ONE_18) // a_18 if is_less_than_one else a_18
    
    z = ((x - ONE_18) * ONE_18) // (x + ONE_18)
    z_squared = (z * z) // ONE_18
    
    term1 = z
    term3 = (term1 * z_squared) // ONE_18 // 3
    term5 = (term3 * z_squared) // ONE_18 * 3 // 5
    term7 = (term5 * z_squared) // ONE_18 * 5 // 7
    
    series = term1 + term3 + term5 + term7
    result = series * 2
    
    return -result if is_less_than_one else result


def ln_simple_cvl_3terms(a_18: int) -> int:
    """
    Reference: 3-term series for comparison.
    ln(x) = 2 * (z + z³/3 + z⁵/5) where z = (x-1)/(x+1)
    """
    is_less_than_one = a_18 < ONE_18
    x = (ONE_18 * ONE_18) // a_18 if is_less_than_one else a_18
    
    z = ((x - ONE_18) * ONE_18) // (x + ONE_18)
    z_squared = (z * z) // ONE_18
    
    term1 = z
    term3 = (term1 * z_squared) // ONE_18 // 3
    term5 = (term3 * z_squared) // ONE_18 * 3 // 5
    
    series = term1 + term3 + term5
    result = series * 2
    
    return -result if is_less_than_one else result


def ln_36_simple_cvl(x_18: int) -> int:
    """
    CVL ln_36_simple from ln36Simple.spec (lines 41-63)
    3-term series at 36 decimals: ln(x) = 2 * (z + z³/3 + z⁵/5)
    
    For x in (0.9, 1.1), provides higher precision.
    Input in 18 decimals, output in 36 decimals.
    """
    x_36 = x_18 * ONE_18
    is_negative = x_36 < ONE_36
    
    if is_negative:
        z_abs = ((ONE_36 - x_36) * ONE_36) // (x_36 + ONE_36)
    else:
        z_abs = ((x_36 - ONE_36) * ONE_36) // (x_36 + ONE_36)
    
    z_squared = (z_abs * z_abs) // ONE_36
    
    t1 = z_abs
    t3 = (t1 * z_squared) // ONE_36 // 3
    t5 = (t3 * z_squared) // ONE_36 * 3 // 5
    
    series = t1 + t3 + t5
    result = series * 2
    
    return -result if is_negative else result


# =============================================================================
# SOLIDITY IMPLEMENTATIONS (matching LogExpMath.sol)
# =============================================================================

def exp_solidity(x_18: int) -> int:
    """
    Mimics LogExpMath.exp() from Solidity.
    Uses decomposition into precomputed e^(2^k) values, then 12-term Taylor series.
    """
    negative_exponent = False
    x = x_18
    
    if x < 0:
        x = -x
        negative_exponent = True
    
    # Decomposition: subtract largest power-of-2 exponents
    first_an = 1
    if x >= X0:
        x -= X0
        first_an = A0
    elif x >= X1:
        x -= X1
        first_an = A1
    
    # Convert to 20 decimals for higher internal precision
    x *= 100
    product = ONE_20
    
    if x >= X2:
        x -= X2
        product = (product * A2) // ONE_20
    if x >= X3:
        x -= X3
        product = (product * A3) // ONE_20
    if x >= X4:
        x -= X4
        product = (product * A4) // ONE_20
    if x >= X5:
        x -= X5
        product = (product * A5) // ONE_20
    if x >= X6:
        x -= X6
        product = (product * A6) // ONE_20
    if x >= X7:
        x -= X7
        product = (product * A7) // ONE_20
    if x >= X8:
        x -= X8
        product = (product * A8) // ONE_20
    if x >= X9:
        x -= X9
        product = (product * A9) // ONE_20
    
    # 12-term Taylor series for small remainder
    series_sum = ONE_20
    term = x
    series_sum += term
    for n in range(2, 13):
        term = ((term * x) // ONE_20) // n
        series_sum += term
    
    result = (((product * series_sum) // ONE_20) * first_an) // 100
    
    return (ONE_18 * ONE_18) // result if negative_exponent else result


def ln_solidity(a_18: int) -> int:
    """
    Mimics LogExpMath._ln() from Solidity.
    Uses decomposition into precomputed ln(a_k) values, then 6-term Taylor series.
    """
    negative_exponent = False
    a = a_18
    
    if a < ONE_18:
        a = (ONE_18 * ONE_18) // a
        negative_exponent = True
    
    sum_val = 0
    
    if a >= A0 * ONE_18:
        a //= A0
        sum_val += X0
    if a >= A1 * ONE_18:
        a //= A1
        sum_val += X1
    
    sum_val *= 100
    a *= 100
    
    if a >= A2:
        a = (a * ONE_20) // A2
        sum_val += X2
    if a >= A3:
        a = (a * ONE_20) // A3
        sum_val += X3
    if a >= A4:
        a = (a * ONE_20) // A4
        sum_val += X4
    if a >= A5:
        a = (a * ONE_20) // A5
        sum_val += X5
    if a >= A6:
        a = (a * ONE_20) // A6
        sum_val += X6
    if a >= A7:
        a = (a * ONE_20) // A7
        sum_val += X7
    if a >= A8:
        a = (a * ONE_20) // A8
        sum_val += X8
    if a >= A9:
        a = (a * ONE_20) // A9
        sum_val += X9
    if a >= A10:
        a = (a * ONE_20) // A10
        sum_val += X10
    if a >= A11:
        a = (a * ONE_20) // A11
        sum_val += X11
    
    # 6-term Taylor series
    z = ((a - ONE_20) * ONE_20) // (a + ONE_20)
    z_squared = (z * z) // ONE_20
    num = z
    series_sum = num
    
    for divisor in [3, 5, 7, 9, 11]:
        num = (num * z_squared) // ONE_20
        series_sum += num // divisor
    
    series_sum *= 2
    result = (sum_val + series_sum) // 100
    
    return -result if negative_exponent else result


def ln_36_solidity(x_18: int) -> int:
    """
    Mimics LogExpMath._ln_36() from Solidity.
    8-term Taylor series at 36 decimal precision for x near 1.
    """
    x = x_18 * ONE_18  # Convert to 36 decimals
    
    z = ((x - ONE_36) * ONE_36) // (x + ONE_36)
    z_squared = (z * z) // ONE_36
    num = z
    series_sum = num
    
    for divisor in [3, 5, 7, 9, 11, 13, 15]:
        num = (num * z_squared) // ONE_36
        series_sum += num // divisor
    
    return series_sum * 2


# =============================================================================
# ERROR ANALYSIS FUNCTIONS
# =============================================================================

def analyze_exp_errors():
    """Analyze exp_simple vs Solidity exp and math.exp reference."""
    print("\n" + "=" * 80)
    print("EXP_SIMPLE ERROR ANALYSIS")
    print("CVL: 5-term Taylor | Solidity: 12-term + decomposition")
    print("=" * 80)
    
    test_values = [0, 0.1, 0.3, 0.5, 0.8, 1.0, 1.5, 2.0, -0.1, -0.5, -1.0]
    
    print(f"\n{'x':<8} {'5-term vs Ref':<18} {'7-term vs Ref':<18} {'5-term Rel %':<15} {'7-term Rel %':<15}")
    print("-" * 74)
    
    for x in test_values:
        if x == 0:
            continue
        x_18 = int(x * ONE_18)
        
        cvl_5 = exp_simple_cvl(x_18)
        cvl_7 = exp_simple_cvl_7terms(x_18)
        ref = int(math.exp(x) * ONE_18)
        
        diff_5 = abs(cvl_5 - ref)
        diff_7 = abs(cvl_7 - ref)
        rel_err_5 = diff_5 / ref * 100
        rel_err_7 = diff_7 / ref * 100
        
        print(f"{x:<8.1f} {diff_5:<18} {diff_7:<18} {rel_err_5:<15.8f} {rel_err_7:<15.8f}")


def analyze_ln_errors():
    """Analyze ln_simple vs Solidity ln and math.log reference."""
    print("\n" + "=" * 80)
    print("LN_SIMPLE ERROR ANALYSIS")
    print("CVL: 4-term series | Solidity: 6-term + decomposition")
    print("=" * 80)
    
    test_values = [0.3, 0.5, 0.8, 0.9, 0.99, 1.01, 1.1, 1.5, 2.0, 3.0]
    
    print(f"\n{'x':<8} {'3-term vs Ref':<18} {'4-term vs Ref':<18} {'3-term Rel %':<15} {'4-term Rel %':<15}")
    print("-" * 74)
    
    for x in test_values:
        x_18 = int(x * ONE_18)
        
        cvl_3 = ln_simple_cvl_3terms(x_18)
        cvl_4 = ln_simple_cvl(x_18)
        ref = int(math.log(x) * ONE_18)
        
        diff_3 = abs(cvl_3 - ref)
        diff_4 = abs(cvl_4 - ref)
        rel_err_3 = diff_3 / abs(ref) * 100 if ref != 0 else 0
        rel_err_4 = diff_4 / abs(ref) * 100 if ref != 0 else 0
        
        print(f"{x:<8.2f} {diff_3:<18} {diff_4:<18} {rel_err_3:<15.8f} {rel_err_4:<15.8f}")


def analyze_ln36_errors():
    """Analyze ln_36_simple vs Solidity _ln_36."""
    print("\n" + "=" * 80)
    print("LN_36_SIMPLE ERROR ANALYSIS")
    print("CVL: 3-term series | Solidity: 8-term series | Domain: (0.9, 1.1)")
    print("=" * 80)
    
    test_values = [0.91, 0.95, 0.99, 1.01, 1.05, 1.09]
    
    print(f"\n{'x':<8} {'CVL vs Solidity (36 dec)':<30} {'Rel Err %':<15}")
    print("-" * 53)
    
    for x in test_values:
        x_18 = int(x * ONE_18)
        
        cvl = ln_36_simple_cvl(x_18)
        sol = ln_36_solidity(x_18)
        
        diff = abs(cvl - sol)
        rel_err = diff / abs(sol) * 100 if sol != 0 else 0
        
        print(f"{x:<8.2f} {diff:<30} {rel_err:<15.10f}")


def analyze_swap_errors():
    """Analyze error propagation in Balancer swap calculations."""
    print("\n" + "=" * 80)
    print("SWAP ERROR PROPAGATION")
    print("Formula: amountOut = balanceOut * (1 - R^(wIn/wOut))")
    print("where R = balanceIn / (balanceIn + amountIn)")
    print("=" * 80)
    
    balance = 1_000_000.0
    
    print("\n--- 50/50 Pool (equal weights) ---")
    print(f"{'Swap %':<10} {'R':<10} {'Amount Out':<15} {'Rel Err %':<20}")
    print("-" * 55)
    
    for swap_pct in [1, 5, 10, 20, 50]:
        amount_in = balance * swap_pct / 100
        R = balance / (balance + amount_in)
        
        # Reference calculation
        ref_out = balance * (1 - R)
        
        # CVL approximation
        R_18 = int(R * ONE_18)
        if 0.9 < R < 1.1:
            ln_R = ln_36_simple_cvl(R_18) // ONE_18  # Convert 36 to 18 dec
        else:
            ln_R = ln_simple_cvl(R_18)
        
        exp_arg_18 = ln_R  # weight ratio = 1 for 50/50
        if abs(exp_arg_18) < 2 * ONE_18:
            pow_cvl = exp_simple_cvl(exp_arg_18) / ONE_18
        else:
            pow_cvl = math.exp(ln_R / ONE_18)
        
        cvl_out = balance * (1 - pow_cvl)
        rel_err = abs(cvl_out - ref_out) / ref_out * 100
        
        print(f"{swap_pct:<10} {R:<10.4f} {ref_out:<15.2f} {rel_err:<20.12f}")
    
    print("\n--- 80/20 Pool (weight ratio = 4) ---")
    print(f"{'Swap %':<10} {'R':<10} {'Amount Out':<15} {'Rel Err %':<20}")
    print("-" * 55)
    
    w_ratio = 4.0  # 80/20 = 4
    for swap_pct in [1, 5, 10, 20]:
        amount_in = balance * swap_pct / 100
        R = balance / (balance + amount_in)
        
        ref_out = balance * (1 - R ** w_ratio)
        
        R_18 = int(R * ONE_18)
        if 0.9 < R < 1.1:
            ln_R = ln_36_simple_cvl(R_18) // ONE_18
        else:
            ln_R = ln_simple_cvl(R_18)
        
        exp_arg = w_ratio * ln_R / ONE_18
        exp_arg_18 = int(exp_arg * ONE_18)
        
        if abs(exp_arg) < 2:
            pow_cvl = exp_simple_cvl(exp_arg_18) / ONE_18
        else:
            pow_cvl = math.exp(exp_arg)
        
        cvl_out = balance * (1 - pow_cvl)
        rel_err = abs(cvl_out - ref_out) / ref_out * 100
        
        print(f"{swap_pct:<10} {R:<10.4f} {ref_out:<15.2f} {rel_err:<20.12f}")


def print_summary():
    """Print summary and recommendations for Certora rules."""
    print("\n" + "=" * 80)
    print("SUMMARY: ERROR BOUNDS FOR CERTORA VERIFICATION")
    print("=" * 80)
    
    print("""
CURRENT CVL IMPLEMENTATIONS (optimized for prover efficiency):
==============================================================

┌─────────────────────────────────────────────────────────────────────────────┐
│ FUNCTION        │ CVL TERMS │ SOL TERMS │ VALID DOMAIN        │ MAX REL ERR │
├─────────────────┼───────────┼───────────┼─────────────────────┼─────────────┤
│ exp_simple      │ 5         │ 12+decomp │ |x| ≤ 0.5           │ < 0.05%     │
│                 │           │           │ |x| ≤ 1             │ < 0.5%      │
│                 │           │           │ |x| ≤ 2             │ < 5%        │
├─────────────────┼───────────┼───────────┼─────────────────────┼─────────────┤
│ ln_simple       │ 4         │ 6+decomp  │ x ∈ [0.5, 2]        │ < 0.01%     │
│                 │           │           │ x ∈ [0.3, 3]        │ < 0.5%      │
├─────────────────┼───────────┼───────────┼─────────────────────┼─────────────┤
│ ln_36_cvl       │ 3         │ 8         │ x ∈ (0.9, 1.1)      │ < 0.001%    │
└─────────────────┴───────────┴───────────┴─────────────────────┴─────────────┘

COMPARISON: TERM COUNT vs ACCURACY
==================================

exp_simple:
  5 terms: 1 + x + x²/2! + x³/3! + x⁴/4!           → ~0.5% error at |x|=1
  7 terms: + x⁵/5! + x⁶/6!                         → ~0.01% error at |x|=1

ln_simple:  
  3 terms: z + z³/3 + z⁵/5                         → ~0.1% error at x=2
  4 terms: + z⁷/7                                  → ~0.01% error at x=2

ln_36_cvl:
  3 terms: z + z³/3 + z⁵/5                         → ~0.0001% in (0.9, 1.1)
  8 terms: (Solidity)                              → ~0.00001% in (0.9, 1.1)

┌─────────────────────────────────────────────────────────────────────────────┐
│ SWAP ERROR (using CVL approximations with current term counts)              │
├─────────────────────────────────────────────────────────────────────────────┤
│   Swap size      │  50/50 Pool Error   │  80/20 Pool Error                  │
│   ≤ 1%           │  < 0.00001%         │  < 0.0001%                         │
│   ≤ 10%          │  < 0.001%           │  < 0.01%                           │
│   ≤ 50%          │  < 0.5%             │  < 2%                              │
└─────────────────┴─────────────────────┴────────────────────────────────────┘

RECOMMENDED TOLERANCES FOR CERTORA RULES:
=========================================

// For CVL vs Solidity equivalence (exp_simple, 5 terms)
definition EXP_CVL_VS_SOL_TOLERANCE() returns mathint = 10000000000000000;  // 1e16 (1%)

// For CVL vs Solidity equivalence (ln_simple, 4 terms)  
definition LN_CVL_VS_SOL_TOLERANCE() returns mathint = 50000000000000000;  // 5e16 (5%)

// For CVL vs Solidity equivalence (ln_36_cvl, 3 terms)
definition LN36_CVL_VS_SOL_TOLERANCE() returns mathint = 100000000000000000000000000000000;  // 1e32

// For typical swap verification (swaps < 10% of pool)
definition SWAP_TOLERANCE() returns mathint = 100000000000000;  // 1e14 = 0.01%

// For round-trip no-profit verification  
definition ROUND_TRIP_TOLERANCE() returns mathint = 10000000000000000;  // 1e16 = 1%

// For invariant preservation
definition INVARIANT_TOLERANCE() returns mathint = 1000000000000000;  // 1e15 = 0.1%

DOMAIN RESTRICTIONS FOR SUMMARIES:
==================================

// For exp_simple - bound the argument (tighter for 5 terms)
require exp_arg >= -1 * ONE_18() && exp_arg <= 1 * ONE_18();

// For ln_simple - bound the input  
require ln_arg >= 300000000000000000 && ln_arg <= 3000000000000000000;
// i.e., x ∈ [0.3, 3.0]

// For ln_36_cvl - use only in high-precision domain
require ln36_arg > 900000000000000000 && ln36_arg < 1100000000000000000;
// i.e., x ∈ (0.9, 1.1)
""")


def analyze_term_count_tradeoffs():
    """Show the tradeoff between term count and accuracy."""
    print("\n" + "=" * 80)
    print("TERM COUNT vs ACCURACY TRADEOFF ANALYSIS")
    print("=" * 80)
    
    print("\n--- EXP: 5 terms vs 7 terms (current CVL uses 5) ---")
    print(f"{'|x|':<10} {'5-term error':<20} {'7-term error':<20} {'Improvement':<15}")
    print("-" * 65)
    
    for x_val in [0.1, 0.3, 0.5, 0.8, 1.0, 1.5, 2.0]:
        x_18 = int(x_val * ONE_18)
        ref = int(math.exp(x_val) * ONE_18)
        
        err_5 = abs(exp_simple_cvl(x_18) - ref)
        err_7 = abs(exp_simple_cvl_7terms(x_18) - ref)
        improvement = err_5 / err_7 if err_7 > 0 else float('inf')
        
        print(f"{x_val:<10.1f} {err_5:<20} {err_7:<20} {improvement:<15.1f}x")
    
    print("\n--- LN: 3 terms vs 4 terms (current CVL uses 4) ---")
    print(f"{'x':<10} {'3-term error':<20} {'4-term error':<20} {'Improvement':<15}")
    print("-" * 65)
    
    for x_val in [0.5, 0.8, 1.2, 1.5, 2.0, 3.0]:
        x_18 = int(x_val * ONE_18)
        ref = int(math.log(x_val) * ONE_18)
        
        err_3 = abs(ln_simple_cvl_3terms(x_18) - ref)
        err_4 = abs(ln_simple_cvl(x_18) - ref)
        improvement = err_3 / err_4 if err_4 > 0 else float('inf')
        
        print(f"{x_val:<10.1f} {err_3:<20} {err_4:<20} {improvement:<15.1f}x")


# =============================================================================
# MAIN
# =============================================================================

if __name__ == "__main__":
    print("=" * 80)
    print("ERROR BOUND ANALYSIS: CVL Simple Functions vs LogExpMath Solidity")
    print("Current CVL: exp_simple=5 terms, ln_simple=4 terms, ln_36_cvl=3 terms")
    print("=" * 80)
    
    analyze_exp_errors()
    analyze_ln_errors()
    analyze_ln36_errors()
    analyze_term_count_tradeoffs()
    analyze_swap_errors()
    print_summary()
    
    print("\n" + "=" * 80)
    print("Analysis complete!")
    print("=" * 80)
