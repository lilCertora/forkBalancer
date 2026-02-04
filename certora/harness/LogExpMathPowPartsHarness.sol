// SPDX-License-Identifier: GPL-3.0-or-later
pragma solidity ^0.8.24;

import { LogExpMath } from "@balancer-labs/v3-solidity-utils/contracts/math/LogExpMath.sol";

/// @notice Harness exposing small parts of `LogExpMath.pow` to CVL.
/// @dev This is intentionally minimal: it only exposes helper computations used by the spec.
contract LogExpMathPowPartsHarness {
    int256 private constant ONE_18 = 1e18;
    int256 private constant ONE_20 = 1e20;

    // Keep in sync with `LogExpMath`.
    int256 private constant MAX_NATURAL_EXPONENT = 130e18;
    int256 private constant MIN_NATURAL_EXPONENT = -41e18;
    int256 private constant LN_36_LOWER_BOUND = ONE_18 - 1e17; // 0.9e18
    int256 private constant LN_36_UPPER_BOUND = ONE_18 + 1e17; // 1.1e18
    uint256 private constant MILD_EXPONENT_BOUND = 2 ** 254 / uint256(ONE_20);

    function pow(uint256 x, uint256 y) external pure returns (uint256) {
        return LogExpMath.pow(x, y);
    }

    /// @dev Exposes LogExpMath.exp for testing exp() function
    function exp(int256 x) external pure returns (int256) {
        return LogExpMath.exp(x);
    }

    /// @dev Exposes LogExpMath.ln for testing _ln (used outside the ln_36 window)
    function ln(int256 a) external pure returns (int256) {
        return LogExpMath.ln(a);
    }

    /// @dev Matches the ln_36 multiply trick in `LogExpMath.pow` (computes `ln36 * y / 1e18` without a full multiply).
    function splitMulLn36(int256 ln36, int256 y) external pure returns (int256) {
        // `ln36` is a 36-decimal fixed point number, and `y` is 18-decimal fixed point.
        // This returns a 36-decimal fixed point number (ln*y).
        return ((ln36 / ONE_18) * y + ((ln36 % ONE_18) * y) / ONE_18);
    }

    /// @dev Direct computation of `ln36 * y / 1e18` (used to prove `splitMulLn36` is equivalent when no overflow occurs).
    function directMulDivLn36(int256 ln36, int256 y) external pure returns (int256) {
        return (ln36 * y) / ONE_18;
    }

    /// @notice A refactor-style implementation of `pow` that uses `ln` directly.
    /// @dev This is intended to match `LogExpMath.pow` *outside* the `ln_36` window, where `ln(a) == _ln(a)`.
    function powViaLnExp(uint256 x, uint256 y) external pure returns (uint256) {
        if (y == 0) {
            return uint256(ONE_18);
        }
        if (x == 0) {
            return 0;
        }
        if (x >> 255 != 0) {
            revert();
        }
        if (y >= MILD_EXPONENT_BOUND) {
            revert();
        }

        int256 xInt = int256(x);
        int256 yInt = int256(y);

        // Outside the LN_36 window, `LogExpMath.ln(xInt)` returns `_ln(xInt)` (18 decimals),
        // so this matches the else-branch computation in `LogExpMath.pow`.
        int256 logxTimesY;
        unchecked {
            logxTimesY = (LogExpMath.ln(xInt) * yInt) / ONE_18;
        }

        if (!(MIN_NATURAL_EXPONENT <= logxTimesY && logxTimesY <= MAX_NATURAL_EXPONENT)) {
            revert();
        }

        return uint256(LogExpMath.exp(logxTimesY));
    }

    function isInLn36Window(uint256 x) external pure returns (bool) {
        if (x >> 255 != 0) return false;
        int256 xInt = int256(x);
        return (LN_36_LOWER_BOUND < xInt && xInt < LN_36_UPPER_BOUND);
    }

    // -------------------------------------------------------------------------
    // Step 4: expose _ln_36 Taylor series for equivalence proof
    // -------------------------------------------------------------------------

    int256 private constant ONE_36 = 1e36;

    /// @dev Exposes the _ln_36 calculation from LogExpMath.
    /// This is the Taylor series: ln(x) = 2 * (z + z^3/3 + z^5/5 + ... + z^15/15)
    /// where z = (x - 1) / (x + 1) in 36-decimal fixed point.
    function ln_36(int256 x) external pure returns (int256) {
        // x must be in the LN_36 window
        require(LN_36_LOWER_BOUND < x && x < LN_36_UPPER_BOUND, "x out of ln36 bounds");

        unchecked {
            // Transform x to 36-decimal fixed point
            x *= ONE_18;

            int256 z = ((x - ONE_36) * ONE_36) / (x + ONE_36);
            int256 z_squared = (z * z) / ONE_36;

            int256 num = z;
            int256 seriesSum = num;

            num = (num * z_squared) / ONE_36;
            seriesSum += num / 3;

            num = (num * z_squared) / ONE_36;
            seriesSum += num / 5;

            num = (num * z_squared) / ONE_36;
            seriesSum += num / 7;

            num = (num * z_squared) / ONE_36;
            seriesSum += num / 9;

            num = (num * z_squared) / ONE_36;
            seriesSum += num / 11;

            num = (num * z_squared) / ONE_36;
            seriesSum += num / 13;

            num = (num * z_squared) / ONE_36;
            seriesSum += num / 15;

            return seriesSum * 2;
        }
    }

    /// @dev Exposes just the z transformation for isolated verification.
    /// z = (x_36 - ONE_36) * ONE_36 / (x_36 + ONE_36)
    function computeZ(int256 x) external pure returns (int256) {
        require(LN_36_LOWER_BOUND < x && x < LN_36_UPPER_BOUND, "x out of ln36 bounds");
        unchecked {
            int256 x_36 = x * ONE_18;
            return ((x_36 - ONE_36) * ONE_36) / (x_36 + ONE_36);
        }
    }

    /// @dev Implementation of pow for INSIDE the ln_36 window using ln_36.
    /// This matches the if-branch in LogExpMath.pow.
    function powViaLn36(uint256 x, uint256 y) external pure returns (uint256) {
        if (y == 0) {
            return uint256(ONE_18);
        }
        if (x == 0) {
            return 0;
        }
        if (x >> 255 != 0) {
            revert();
        }
        if (y >= MILD_EXPONENT_BOUND) {
            revert();
        }

        int256 xInt = int256(x);
        int256 yInt = int256(y);

        // Inside the LN_36 window, LogExpMath.pow uses _ln_36 with the split multiply.
        require(LN_36_LOWER_BOUND < xInt && xInt < LN_36_UPPER_BOUND, "not in ln36 window");

        int256 logxTimesY;
        unchecked {
            // Compute _ln_36 directly (matches LogExpMath._ln_36):
            int256 x_36 = xInt * ONE_18;
            int256 z = ((x_36 - ONE_36) * ONE_36) / (x_36 + ONE_36);
            int256 z_squared = (z * z) / ONE_36;

            int256 num = z;
            int256 seriesSum = num;

            num = (num * z_squared) / ONE_36;
            seriesSum += num / 3;

            num = (num * z_squared) / ONE_36;
            seriesSum += num / 5;

            num = (num * z_squared) / ONE_36;
            seriesSum += num / 7;

            num = (num * z_squared) / ONE_36;
            seriesSum += num / 9;

            num = (num * z_squared) / ONE_36;
            seriesSum += num / 11;

            num = (num * z_squared) / ONE_36;
            seriesSum += num / 13;

            num = (num * z_squared) / ONE_36;
            seriesSum += num / 15;

            int256 ln36_x = seriesSum * 2;

            // This is the split multiply from pow():
            // ((ln_36_x / ONE_18) * y_int256 + ((ln_36_x % ONE_18) * y_int256) / ONE_18)
            logxTimesY = ((ln36_x / ONE_18) * yInt + ((ln36_x % ONE_18) * yInt) / ONE_18);
            logxTimesY /= ONE_18;
        }

        if (!(MIN_NATURAL_EXPONENT <= logxTimesY && logxTimesY <= MAX_NATURAL_EXPONENT)) {
            revert();
        }

        return uint256(LogExpMath.exp(logxTimesY));
    }
}

