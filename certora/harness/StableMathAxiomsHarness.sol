// SPDX-License-Identifier: GPL-3.0-or-later
pragma solidity ^0.8.24;

/// @notice Minimal interface used to model `StableMath.computeInvariant` as an external call.
/// @dev In Certora, we will summarize calls to `computeInvariant2()` with axioms (monotonicity, bounds, etc).
interface IInvariantOracle {
    function computeInvariant2(uint256 amp, uint256 b0, uint256 b1) external view returns (uint256);
    function computeInvariant3(uint256 amp, uint256 b0, uint256 b1, uint256 b2) external view returns (uint256);
}

/// @notice Minimal interface used to model `StableMath.computeBalance` as an external call.
/// @dev In Certora, we will summarize calls with axioms (monotonicity, consistency, etc).
interface IBalanceOracle {
    function computeBalance2(
        uint256 amp,
        uint256 b_other,
        uint256 inv,
        uint256 tokenIndex
    ) external view returns (uint256);
    function computeBalance3(
        uint256 amp,
        uint256 b_other0,
        uint256 b_other1,
        uint256 inv,
        uint256 tokenIndex
    ) external view returns (uint256);
}

/// @notice Harness exposing StableMath-style computations but with axiomatized Newton-Raphson.
/// @dev This replicates `StableMath` behavior, except that the iterative computeInvariant and
///      computeBalance are delegated to external oracles, which are summarized in CVL.
contract StableMathAxiomsHarness {
    // -------------------------------------------------------------------------
    // StableMath constants (copied from pkg/solidity-utils/contracts/math/StableMath.sol)
    // -------------------------------------------------------------------------

    uint256 internal constant AMP_PRECISION = 1e3;
    uint256 internal constant MIN_AMP = 1;
    uint256 internal constant MAX_AMP = 50000;
    uint256 internal constant MAX_IMBALANCE_RATIO = 10_000;

    // FixedPoint constants
    uint256 internal constant ONE = 1e18;

    // Use fixed, unresolved addresses so the Prover treats them as external call targets.
    // The actual semantics are provided via CVL summaries, not Solidity bytecode.
    IInvariantOracle internal constant INVARIANT_ORACLE =
        IInvariantOracle(address(0x0000000000000000000000000000000000000200));
    IBalanceOracle internal constant BALANCE_ORACLE =
        IBalanceOracle(address(0x0000000000000000000000000000000000000201));

    // -------------------------------------------------------------------------
    // Errors (mirroring StableMath)
    // -------------------------------------------------------------------------

    error MaxImbalanceRatioExceeded();

    // -------------------------------------------------------------------------
    // FixedPoint helpers
    // -------------------------------------------------------------------------

    function mulDown(uint256 a, uint256 b) internal pure returns (uint256) {
        return (a * b) / ONE;
    }

    function mulUp(uint256 a, uint256 b) internal pure returns (uint256 result) {
        uint256 product = a * b;
        assembly ("memory-safe") {
            result := mul(iszero(iszero(product)), add(div(sub(product, 1), ONE), 1))
        }
    }

    function divDown(uint256 a, uint256 b) internal pure returns (uint256) {
        return (a * ONE) / b;
    }

    function divUp(uint256 a, uint256 b) internal pure returns (uint256 result) {
        uint256 aInflated = a * ONE;
        assembly ("memory-safe") {
            result := mul(iszero(iszero(aInflated)), add(div(sub(aInflated, 1), b), 1))
        }
    }

    // -------------------------------------------------------------------------
    // Invariant computation (delegated to oracle)
    // -------------------------------------------------------------------------

    /// @notice Compute the StableSwap invariant for a 2-token pool.
    /// @dev Delegates to the invariant oracle, which is summarized with axioms in CVL.
    function computeInvariant2(
        uint256 amplificationParameter,
        uint256 b0,
        uint256 b1
    ) public view returns (uint256) {
        return INVARIANT_ORACLE.computeInvariant2(amplificationParameter, b0, b1);
    }

    /// @notice Compute the StableSwap invariant for a 3-token pool.
    function computeInvariant3(
        uint256 amplificationParameter,
        uint256 b0,
        uint256 b1,
        uint256 b2
    ) public view returns (uint256) {
        return INVARIANT_ORACLE.computeInvariant3(amplificationParameter, b0, b1, b2);
    }

    // -------------------------------------------------------------------------
    // Balance computation (delegated to oracle)
    // -------------------------------------------------------------------------

    /// @notice Compute a token balance given the other balance and invariant (2-token).
    /// @dev Delegates to the balance oracle, which is summarized with axioms in CVL.
    /// @param amplificationParameter The amplification parameter (scaled by AMP_PRECISION)
    /// @param b_other The balance of the other token
    /// @param inv The pool invariant
    /// @param tokenIndex The index of the token to compute (0 or 1) - used for symmetry
    function computeBalance2(
        uint256 amplificationParameter,
        uint256 b_other,
        uint256 inv,
        uint256 tokenIndex
    ) public view returns (uint256) {
        return BALANCE_ORACLE.computeBalance2(amplificationParameter, b_other, inv, tokenIndex);
    }

    /// @notice Compute a token balance given the other balances and invariant (3-token).
    function computeBalance3(
        uint256 amplificationParameter,
        uint256 b_other0,
        uint256 b_other1,
        uint256 inv,
        uint256 tokenIndex
    ) public view returns (uint256) {
        return BALANCE_ORACLE.computeBalance3(amplificationParameter, b_other0, b_other1, inv, tokenIndex);
    }

    // -------------------------------------------------------------------------
    // Swap functions (2-token pool)
    // -------------------------------------------------------------------------

    /// @notice Compute amountOut for a swap given exact amountIn (2-token pool).
    /// @dev Uses axiomatized invariant and balance computations.
    function computeOutGivenExactIn2(
        uint256 amplificationParameter,
        uint256 b0,
        uint256 b1,
        uint256 tokenIndexIn,
        uint256 tokenIndexOut,
        uint256 tokenAmountIn
    ) external view returns (uint256) {
        require(tokenIndexIn < 2 && tokenIndexOut < 2 && tokenIndexIn != tokenIndexOut, "Invalid indices");
        
        // Compute the invariant before the swap
        uint256 invariant = computeInvariant2(amplificationParameter, b0, b1);
        
        // Update the input balance
        uint256 newBalanceIn;
        uint256 balanceOut;
        if (tokenIndexIn == 0) {
            newBalanceIn = b0 + tokenAmountIn;
            balanceOut = b1;
        } else {
            newBalanceIn = b1 + tokenAmountIn;
            balanceOut = b0;
        }
        
        // Compute the new output balance that maintains the invariant
        // The oracle computes the balance given the *other* balance and invariant
        uint256 finalBalanceOut = computeBalance2(amplificationParameter, newBalanceIn, invariant, tokenIndexOut);
        
        // Amount out, rounded down (protocol-favoring)
        require(balanceOut > finalBalanceOut, "Insufficient output");
        return balanceOut - finalBalanceOut - 1;
    }

    /// @notice Compute amountIn required for a swap given exact amountOut (2-token pool).
    /// @dev Uses axiomatized invariant and balance computations.
    function computeInGivenExactOut2(
        uint256 amplificationParameter,
        uint256 b0,
        uint256 b1,
        uint256 tokenIndexIn,
        uint256 tokenIndexOut,
        uint256 tokenAmountOut
    ) external view returns (uint256) {
        require(tokenIndexIn < 2 && tokenIndexOut < 2 && tokenIndexIn != tokenIndexOut, "Invalid indices");
        
        // Compute the invariant before the swap
        uint256 invariant = computeInvariant2(amplificationParameter, b0, b1);
        
        // Update the output balance
        uint256 newBalanceOut;
        uint256 balanceIn;
        if (tokenIndexOut == 0) {
            require(b0 > tokenAmountOut, "Insufficient balance");
            newBalanceOut = b0 - tokenAmountOut;
            balanceIn = b1;
        } else {
            require(b1 > tokenAmountOut, "Insufficient balance");
            newBalanceOut = b1 - tokenAmountOut;
            balanceIn = b0;
        }
        
        // Compute the new input balance that maintains the invariant
        uint256 finalBalanceIn = computeBalance2(amplificationParameter, newBalanceOut, invariant, tokenIndexIn);
        
        // Amount in, rounded up (protocol-favoring)
        require(finalBalanceIn > balanceIn, "No input required");
        return finalBalanceIn - balanceIn + 1;
    }

    // -------------------------------------------------------------------------
    // Swap functions (3-token pool)
    // -------------------------------------------------------------------------

    /// @notice Compute amountOut for a swap given exact amountIn (3-token pool).
    function computeOutGivenExactIn3(
        uint256 amplificationParameter,
        uint256 b0,
        uint256 b1,
        uint256 b2,
        uint256 tokenIndexIn,
        uint256 tokenIndexOut,
        uint256 tokenAmountIn
    ) external view returns (uint256) {
        require(tokenIndexIn < 3 && tokenIndexOut < 3 && tokenIndexIn != tokenIndexOut, "Invalid indices");
        
        // Compute the invariant before the swap
        uint256 invariant = computeInvariant3(amplificationParameter, b0, b1, b2);
        
        // Get balances and update input
        uint256[3] memory balances = [b0, b1, b2];
        balances[tokenIndexIn] += tokenAmountIn;
        
        // Get the two "other" balances for computeBalance3
        uint256 other0;
        uint256 other1;
        if (tokenIndexOut == 0) {
            other0 = balances[1];
            other1 = balances[2];
        } else if (tokenIndexOut == 1) {
            other0 = balances[0];
            other1 = balances[2];
        } else {
            other0 = balances[0];
            other1 = balances[1];
        }
        
        uint256 balanceOut = tokenIndexOut == 0 ? b0 : (tokenIndexOut == 1 ? b1 : b2);
        uint256 finalBalanceOut = computeBalance3(amplificationParameter, other0, other1, invariant, tokenIndexOut);
        
        require(balanceOut > finalBalanceOut, "Insufficient output");
        return balanceOut - finalBalanceOut - 1;
    }

    /// @notice Compute amountIn required for a swap given exact amountOut (3-token pool).
    function computeInGivenExactOut3(
        uint256 amplificationParameter,
        uint256 b0,
        uint256 b1,
        uint256 b2,
        uint256 tokenIndexIn,
        uint256 tokenIndexOut,
        uint256 tokenAmountOut
    ) external view returns (uint256) {
        require(tokenIndexIn < 3 && tokenIndexOut < 3 && tokenIndexIn != tokenIndexOut, "Invalid indices");
        
        // Compute the invariant before the swap
        uint256 invariant = computeInvariant3(amplificationParameter, b0, b1, b2);
        
        // Get balances and update output
        uint256[3] memory balances = [b0, b1, b2];
        require(balances[tokenIndexOut] > tokenAmountOut, "Insufficient balance");
        balances[tokenIndexOut] -= tokenAmountOut;
        
        // Get the two "other" balances for computeBalance3
        uint256 other0;
        uint256 other1;
        if (tokenIndexIn == 0) {
            other0 = balances[1];
            other1 = balances[2];
        } else if (tokenIndexIn == 1) {
            other0 = balances[0];
            other1 = balances[2];
        } else {
            other0 = balances[0];
            other1 = balances[1];
        }
        
        uint256 balanceIn = tokenIndexIn == 0 ? b0 : (tokenIndexIn == 1 ? b1 : b2);
        uint256 finalBalanceIn = computeBalance3(amplificationParameter, other0, other1, invariant, tokenIndexIn);
        
        require(finalBalanceIn > balanceIn, "No input required");
        return finalBalanceIn - balanceIn + 1;
    }

    // -------------------------------------------------------------------------
    // Helper functions for verification
    // -------------------------------------------------------------------------

    /// @notice Check if balances are within the max imbalance ratio.
    function ensureBalancesWithinMaxImbalanceRange(uint256 minBalance, uint256 maxBalance) external pure {
        if (maxBalance / minBalance >= MAX_IMBALANCE_RATIO) {
            revert MaxImbalanceRatioExceeded();
        }
    }

    /// @notice Get min and max from two balances.
    function getMinAndMaxBalances2(
        uint256 b0,
        uint256 b1
    ) external pure returns (uint256 minBalance, uint256 maxBalance) {
        if (b0 <= b1) {
            minBalance = b0;
            maxBalance = b1;
        } else {
            minBalance = b1;
            maxBalance = b0;
        }
    }

    /// @notice Expose constants for CVL.
    function getAmpPrecision() external pure returns (uint256) {
        return AMP_PRECISION;
    }

    function getMinAmpScaled() external pure returns (uint256) {
        return MIN_AMP * AMP_PRECISION;
    }

    function getMaxAmpScaled() external pure returns (uint256) {
        return MAX_AMP * AMP_PRECISION;
    }

    function getMaxImbalanceRatio() external pure returns (uint256) {
        return MAX_IMBALANCE_RATIO;
    }
}
