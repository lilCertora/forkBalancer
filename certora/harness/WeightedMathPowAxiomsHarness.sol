// SPDX-License-Identifier: GPL-3.0-or-later
pragma solidity ^0.8.24;

/// @notice Minimal interface used to model `LogExpMath.pow` as an external call.
/// @dev In Certora, we will summarize calls to `pow()` with axioms (monotonicity, identities, etc).
interface IPowOracle {
    function pow(uint256 x, uint256 y) external view returns (uint256);
}

/// @notice Harness exposing WeightedMath-style computations but with axiomatized pow.
/// @dev This replicates `FixedPoint.powUp/powDown` behavior, except that the raw pow is delegated to an
///      external oracle (`POW_ORACLE.pow`), which is summarized in CVL.
contract WeightedMathPowAxiomsHarness {
    // -------------------------------------------------------------------------
    // FixedPoint constants (copied from pkg/solidity-utils/contracts/math/FixedPoint.sol)
    // -------------------------------------------------------------------------

    uint256 internal constant ONE = 1e18;
    uint256 internal constant TWO = 2 * ONE;
    uint256 internal constant FOUR = 4 * ONE;
    uint256 internal constant MAX_POW_RELATIVE_ERROR = 10000; // 10^(-14)

    // WeightedMath constants (copied from pkg/solidity-utils/contracts/math/WeightedMath.sol)
    uint256 internal constant _MAX_IN_RATIO = 30e16; // 30%
    uint256 internal constant _MAX_OUT_RATIO = 30e16; // 30%

    // Use a fixed, unresolved address so the Prover treats it as an external call target.
    // The actual semantics are provided via CVL summaries, not Solidity bytecode.
    IPowOracle internal constant POW_ORACLE =
        IPowOracle(address(0x0000000000000000000000000000000000000100));

    // -------------------------------------------------------------------------
    // FixedPoint ops (copied from FixedPoint.sol)
    // -------------------------------------------------------------------------

    error ZeroDivision();
    error MaxOutRatio();
    error MaxInRatio();
    error ZeroInvariant();

    function mulDown(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 product = a * b;
        return product / ONE;
    }

    function mulUp(uint256 a, uint256 b) internal pure returns (uint256 result) {
        uint256 product = a * b;
        // result = product == 0 ? 0 : ((product - 1) / ONE) + 1
        assembly ("memory-safe") {
            result := mul(iszero(iszero(product)), add(div(sub(product, 1), ONE), 1))
        }
    }

    function divDown(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 aInflated = a * ONE;
        return aInflated / b;
    }

    function mulDivUp(uint256 a, uint256 b, uint256 c) internal pure returns (uint256 result) {
        if (c == 0) revert ZeroDivision();
        uint256 product = a * b;
        // result = product == 0 ? 0 : (product - 1) / c + 1
        assembly ("memory-safe") {
            result := mul(iszero(iszero(product)), add(div(sub(product, 1), c), 1))
        }
    }

    function divUp(uint256 a, uint256 b) internal pure returns (uint256) {
        return mulDivUp(a, ONE, b);
    }

    function complement(uint256 x) internal pure returns (uint256 result) {
        assembly ("memory-safe") {
            result := mul(lt(x, ONE), sub(ONE, x))
        }
    }

    // -------------------------------------------------------------------------
    // Axiomatized pow: keep FixedPoint wrappers, replace LogExpMath.pow call only.
    // -------------------------------------------------------------------------

    function _powRaw(uint256 x, uint256 y) internal view returns (uint256) {
        return POW_ORACLE.pow(x, y);
    }

    function powDown(uint256 x, uint256 y) internal view returns (uint256) {
        if (x == ONE) return ONE;

        if (y == ONE) {
            return x;
        } else if (y == TWO) {
            return mulDown(x, x);
        } else if (y == FOUR) {
            uint256 square = mulDown(x, x);
            return mulDown(square, square);
        } else {
            uint256 raw = _powRaw(x, y);
            uint256 maxError = mulUp(raw, MAX_POW_RELATIVE_ERROR) + 1;
            if (raw < maxError) {
                return 0;
            } else {
                unchecked {
                    return raw - maxError;
                }
            }
        }
    }

    function powUp(uint256 x, uint256 y) internal view returns (uint256) {
        if (x == ONE) return ONE;

        if (y == ONE) {
            return x;
        } else if (y == TWO) {
            return mulUp(x, x);
        } else if (y == FOUR) {
            uint256 square = mulUp(x, x);
            return mulUp(square, square);
        } else {
            uint256 raw = _powRaw(x, y);
            uint256 maxError = mulUp(raw, MAX_POW_RELATIVE_ERROR) + 1;
            return raw + maxError;
        }
    }

    // -------------------------------------------------------------------------
    // WeightedMath (subset) – same signatures as WeightedMathHarness
    // -------------------------------------------------------------------------

    function maxInAllowed(uint256 balanceIn) external pure returns (uint256) {
        return mulDown(balanceIn, _MAX_IN_RATIO);
    }

    function maxOutAllowed(uint256 balanceOut) external pure returns (uint256) {
        return mulDown(balanceOut, _MAX_OUT_RATIO);
    }

    function computeOutGivenExactIn(
        uint256 balanceIn,
        uint256 weightIn,
        uint256 balanceOut,
        uint256 weightOut,
        uint256 amountIn
    ) external view returns (uint256 amountOut) {
        if (amountIn > mulDown(balanceIn, _MAX_IN_RATIO)) revert MaxInRatio();

        uint256 denominator = balanceIn + amountIn;
        uint256 base = divUp(balanceIn, denominator);
        uint256 exponent = divDown(weightIn, weightOut);
        uint256 power = powUp(base, exponent);

        return mulDown(balanceOut, complement(power));
    }

    function computeInGivenExactOut(
        uint256 balanceIn,
        uint256 weightIn,
        uint256 balanceOut,
        uint256 weightOut,
        uint256 amountOut
    ) external view returns (uint256 amountIn) {
        if (amountOut > mulDown(balanceOut, _MAX_OUT_RATIO)) revert MaxOutRatio();

        uint256 base = divUp(balanceOut, balanceOut - amountOut);
        uint256 exponent = divUp(weightOut, weightIn);
        uint256 power = powUp(base, exponent);

        uint256 ratio = power - ONE;
        return mulUp(balanceIn, ratio);
    }

    function computeBalanceOutGivenInvariant(
        uint256 currentBalance,
        uint256 weight,
        uint256 invariantRatio
    ) external view returns (uint256 newBalance) {
        function(uint256, uint256) internal pure returns (uint256) divUpOrDown = invariantRatio > ONE ? divUp : divDown;
        uint256 balanceRatio = powUp(invariantRatio, divUpOrDown(ONE, weight));
        return mulUp(currentBalance, balanceRatio);
    }

    function invariantDown2NoLoop(uint256 w0, uint256 w1, uint256 b0, uint256 b1) external view returns (uint256 inv) {
        inv = mulDown(ONE, powDown(b0, w0));
        inv = mulDown(inv, powDown(b1, w1));
        if (inv == 0) revert ZeroInvariant();
    }

    function invariantUp2NoLoop(uint256 w0, uint256 w1, uint256 b0, uint256 b1) external view returns (uint256 inv) {
        inv = mulUp(ONE, powUp(b0, w0));
        inv = mulUp(inv, powUp(b1, w1));
        if (inv == 0) revert ZeroInvariant();
    }

    // -------------------------------------------------------------------------
    // 3-TOKEN INVARIANT (no loop)
    // -------------------------------------------------------------------------

    function invariantDown3NoLoop(
        uint256 w0, uint256 w1, uint256 w2,
        uint256 b0, uint256 b1, uint256 b2
    ) external view returns (uint256 inv) {
        inv = mulDown(ONE, powDown(b0, w0));
        inv = mulDown(inv, powDown(b1, w1));
        inv = mulDown(inv, powDown(b2, w2));
        if (inv == 0) revert ZeroInvariant();
    }

    function invariantUp3NoLoop(
        uint256 w0, uint256 w1, uint256 w2,
        uint256 b0, uint256 b1, uint256 b2
    ) external view returns (uint256 inv) {
        inv = mulUp(ONE, powUp(b0, w0));
        inv = mulUp(inv, powUp(b1, w1));
        inv = mulUp(inv, powUp(b2, w2));
        if (inv == 0) revert ZeroInvariant();
    }

    // -------------------------------------------------------------------------
    // 4-TOKEN INVARIANT (no loop)
    // -------------------------------------------------------------------------

    function invariantDown4NoLoop(
        uint256 w0, uint256 w1, uint256 w2, uint256 w3,
        uint256 b0, uint256 b1, uint256 b2, uint256 b3
    ) external view returns (uint256 inv) {
        inv = mulDown(ONE, powDown(b0, w0));
        inv = mulDown(inv, powDown(b1, w1));
        inv = mulDown(inv, powDown(b2, w2));
        inv = mulDown(inv, powDown(b3, w3));
        if (inv == 0) revert ZeroInvariant();
    }

    function invariantUp4NoLoop(
        uint256 w0, uint256 w1, uint256 w2, uint256 w3,
        uint256 b0, uint256 b1, uint256 b2, uint256 b3
    ) external view returns (uint256 inv) {
        inv = mulUp(ONE, powUp(b0, w0));
        inv = mulUp(inv, powUp(b1, w1));
        inv = mulUp(inv, powUp(b2, w2));
        inv = mulUp(inv, powUp(b3, w3));
        if (inv == 0) revert ZeroInvariant();
    }
}

