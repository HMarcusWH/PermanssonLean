# Adaptive admitted-block control — numerical profile v1

**Source:** `PermanssonResearch/ReverseSolver/AdaptiveGrammarControl.lean`
(timing: the whole patch block is chosen before each α → P → U stage, and the
history may choose a different block next time), `FiniteMonitor.lean`
(`value`) and `MonitorOptimality.lean` (`monitor_optimal_and_attained`). The
numeric profile is a bounded exact-rational implementation. Its Lean
correspondence is described in
[`ADAPTIVE_LEAN_BRIDGE.md`](ADAPTIVE_LEAN_BRIDGE.md). Application output
reports `lean_status=NOT_EXECUTED`.

## Input

Run `permansson-app finite-adaptive-grammar <input.json> --output <new-directory>`.
The request wraps a complete patch-grammar request
(see [`NUMERIC_GRAMMAR_QUOTIENT.md`](NUMERIC_GRAMMAR_QUOTIENT.md)):
`{"format": "Permansson.App.AdaptiveGrammarRequest.v1", "grammar": {...}}`.
The grammar's admitted blocks are the controls, its region and `value_type`
define the objective (survival in the region through the horizon, or exit by
the horizon), and its comparison states are the start states. Limits: at most
8 admitted blocks and 8 transitions, plus the grammar's own limits.

## Computed objects

- `monitor_table[r][y]`: the optimum with `r` transitions remaining from joint
  state `y`, for the flag "every observed state so far lies in the region"
  false and true. The table starts at the reward and every layer takes the
  maximum over all admitted blocks of `Σ_z K_block(y, z) · table[r−1][z][flag ∧ z ∈ region]`.
- `optimal_blocks`: for each remaining horizon and each in-region state, every
  tied optimal block (indices into `admitted_blocks`).
- `adaptive_values`: the optimum from each start state. The flag is the only
  memory the objective needs, so this is the optimum over every full-history
  behavioral block controller.
- `frozen_block_values`, `best_frozen_values` and `adaptivity_gain`: the value
  of each block applied at every step, the best of them, and the gain from
  adapting the block to the state.

`receipts.adaptive` does not import the producer or the grammar engine's
block application. It rebuilds every block with the grammar checker's
independent reifier and sums its joint kernel directly from α, P and U. It
then recomputes the table, all ties and every frozen value, and checks that
no frozen block beats the adaptive optimum.

## Limits

Only declared blocks are controls: no downward closure, and an unadmitted
joint block is never assumed. Its effect may still be reached adaptively when
the blocks act on different rows. P is never changed. No overlap-model atom
certificate, constitutive or PR certificate, empirical identification,
independent certification or release acceptance.
