# Rectangular vs committed nature — source-bound Lean bridge candidate

**Development scope:** OPT-06 (robust chronological games),
`feature/application-successor-full`, PR #115. `finite-robust-nature`
evaluates, by remaining steps, the max-min value when nature observes the
realized control and then selects a full physical P row (rectangular,
reselecting at every node), the declared fixed policy's value against
rectangular nature, and its value under each single committed model;
`receipts.robust_nature` independently rechecks it.

## Mathematical contract

`PermanssonResearch/ApplicationBridge/RobustReceipt.lean` over Research's
`RectangularFiniteGame`:

- `rectStep` — computable max over admitted controls of the min over admitted
  nature rows of the one-step score; `minScore_eq_inf'` and
  `maxmin_eq_rectStep` identify Research's `Classical.choose`-based
  `minScore` / `maximizingControl` with it.
- `checkRectangularTable` / `checkRectangularTable_sound` — the table starts
  at the terminal reward and every entry `r + 1` is `rectStep` of entry `r`
  at time `N - (r + 1)`.
- `checked_table_eq_value` — a checked table is Research's `value`.
- `checked_rectangular_saddle` — via `rectangular_game_actual_saddle`: some
  controller guarantees the checked value against every behavioral nature
  strategy, and some nature strategy holds every behavioral controller to it,
  on the actual chronological product law.

The private-stage certificate route, in which nature sees the mixture but not
the realized control, is a separate profile and bridge; see
[`PRIVATE_STAGE_LEAN_BRIDGE.md`](PRIVATE_STAGE_LEAN_BRIDGE.md). Not
implemented: committed-game optimality (the committed comparison is for the
declared fixed policy only).

## Source emission and replay

`proof.robust_emit` runs the independent checker, reflects the baseline and
each nature model and proves `nature_<j>_held_fixed` (feasibility, α and U
unchanged; only P differs). It builds three games from the nature models'
fixed-action P·U rows: `game` (all admitted controls, all nature rows),
`fixedGame` (the declared policy, all nature rows) and `committedGame j`
(the declared policy, nature row `j` only), checks each value table
(`game_checked`, `fixed_checked`, `committed_<j>_checked`) and states the
saddle values per comparison state with exact rationals
(`rectangular_optimum_<y>`, `fixed_rectangular_<y>`, `committed_<j>_<y>`),
plus `rectangular_le_committed`. Scope: the shared literal reflection bound
(the packaged four-world example is refused with `REIFICATION_SCOPE`),
horizon 0..6.

```bash
python3 -B -m permansson_app finite-robust-nature request.json --output /tmp/nature
python3 -B -m permansson_app.proof.robust_emit request.json \
  /tmp/nature/nature_receipt.json --output /tmp/permansson-robust-instance
python3 -B -m permansson_app.proof.control_source_check --family robust-nature \
  request.json /tmp/nature/nature_receipt.json /tmp/permansson-robust-instance
lake env lean /tmp/permansson-robust-instance/ReifiedRobustNature.lean
```

`verification/research/test_application_robust_live_lean.py` compiles a
two-model fixture where rectangular nature is strictly worse for the fixed
policy than any committed model (`1/4` vs `1/2`) and the optimized value is
`4/9`, plus its one-step variant; audits axioms; and requires single-line
mutations to fail at the falsified obligation: a false optimized value
(`game_checked`), the committed value substituted for the rectangular one
(`fixed_checked`), swapped committed models (`committed_0_checked`) and a
nature model that changes α (`nature_0_held_fixed`).

## Trust boundary

Emission and source rechecks report `lean_status: NOT_EXECUTED`. A compiler
pass is not an authenticated proof receipt, independent mathematical
certification, empirical identification or release approval.
