# NEXT-06 / D2-P09 — constructed nonlinear policy boundary

The finite model has two states and two actions. The physical next state is the
chosen action. The initial state is fixed to false. Four deterministic
stationary state-feedback maps are exhaustively classified. Their recurrent
cycle true-state shares are 0, 1, or 1/2. For the predeclared nonlinear
functional F(p) = 1 - |p - 2/3|, the best stationary deterministic score is
5/6, attained by alternating feedback.

A legitimate time-dependent controller commits to the repeating action sequence
true, true, false independently of future observations. The actual forced
physical state has two true values in each three-step block. Exact-fraction
Python tests verify thirty complete blocks and all four stationary policies.

The Lean module proves the physical deterministic recursion, eventual
two-periodicity, all-stationary score bound, the alternating witness,
three-period action schedule, first physical state block and strict
comparison to the nonstationary block score.

## Certification boundary

This PR is a **partial D-09 acceptance witness**, not the unproved general
asymptotic history-policy theorem. No theorem here identifies a generic
infinite-path occupation law with the supplied finite-cycle arithmetic;
a dedicated path-law/limit adapter is still needed. In particular this does
not satisfy all mandatory acceptance obligations of D2-P09, the selected
`ExactClassFunctional` instance, or NEXT-08.

The old deterministic-stationary theorem and all frozen model, application and
release sources remain unchanged. The historical negative examples are retained.
Genuine Lean compilation and source-bound CI are required before acceptance.
