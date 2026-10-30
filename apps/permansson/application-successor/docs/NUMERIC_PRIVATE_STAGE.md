# One-stage private-control robust value — numerical profile v1

**Source:** `PermanssonResearch/ReverseSolver/PrivateControlStageModel.lean`
(`stagePayoff`, `privateValue`, the actual draw order `stageLaw`) and
`PrivateControlStageOptimizer.lean` (`solvePrivateStage`,
`returned_actual_strategic_value`). The numeric profile is a bounded
exact-rational implementation; its Lean correspondence is described in
[`PRIVATE_STAGE_LEAN_BRIDGE.md`](PRIVATE_STAGE_LEAN_BRIDGE.md). Application
output reports `lean_status=NOT_EXECUTED`.

## Timing

Nature chooses a parameter θ after seeing the controller's *mixed strategy*
`p`, but before the private control draw `c ~ p`. The private value of `p` is
`min_θ Σ_c p(c) Q(θ, c)`. This differs from the rectangular game of
[`NUMERIC_ROBUST_NATURE.md`](NUMERIC_ROBUST_NATURE.md), where nature observes
the realized control. That revealed-control experiment is reported here only
through its value.

## Input

Run `permansson-app finite-private-stage <input.json> --output <new-directory>`.
`labels.controls` and `labels.nature` each list 1..4 distinct names;
`payoff[θ][c]` is an exact rational of any sign, one row per nature
parameter.

## Computed objects

- `value` `v`: the greatest private value over all mixed controllers, found by
  exhaustive exact vertex enumeration of the controller program
  `max v` subject to `p ≥ 0`, `Σ p = 1`, `v ≤ Σ_c p(c) Q(θ, c)` for every θ;
- `controller_mixture` `p`, an optimal rational vertex, and
  `controller_guarantee_by_nature`, its payoff against every θ;
- `nature_mixture` `q` from the same enumeration of nature's program, and
  `nature_hold_by_control`, its payoff against every pure control;
- `pure_control_worst`, `pure_control_value` `r = max_c min_θ Q(θ, c)` and
  the controls attaining it; `r` is both the private value of the best pure
  control and the value when nature observes the realized control;
- `randomization_gain = v − r`.

`receipts.private_stage` does not import the producer. It checks that `p`
and `q` are probability vectors, that every guarantee is at least `v` and
every hold at most `v`. Together these prove `v` is the greatest private
value, so no minimax theorem or LP duality is assumed. It also recomputes
the pure-control objects in the opposite loop order.

## Limits

Only one stage. No multi-stage private games, committed nature, learning,
empirical identification, independent certification or release acceptance.
