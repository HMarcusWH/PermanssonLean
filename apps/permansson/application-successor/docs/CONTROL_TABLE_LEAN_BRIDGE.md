# Finite Bellman control tables — source-bound Lean bridge candidate

**Development scope:** OPT-01/OPT-02 (fully observed finite-horizon hitting
control), `feature/application-successor-full`, PR #115.
The application's `finite-bellman` profile computes exact rational Bellman
values and argmax sets for a finite α/P/U model, and `receipts.control`
independently rechecks them. This increment binds a checked table to the
existing Research Bellman theorems **for the submitted source model**.

## Mathematical contract

`PermanssonResearch/ApplicationBridge/ControlTableReceipt.lean`:

- `TableChecks` / `checkBellmanReceipt` — a decidable check of the terminal
  row, every remaining-horizon recurrence, admission of every selected control
  and comparison against **all** admitted controls (ties allowed).
- `checked_table_eq_bellman`, `checkBellmanReceipt_sound` — a checked table
  equals `bellmanValue`, bounds every admitted remaining-horizon Markov
  schedule (`policyValue_le_bellman`) and is attained
  (`maximizingSchedule_attains`).
- `boundControlSystem w options hexact hpos` — the `FiniteControlSystem`
  whose control `a` has the fixed-action `P·U` row of the `FiniteWorldInput`
  `w`, with joint states ordered `(s, x) ↦ s * nx + x` (`finProdFinEquiv`).
  `AdmittedExactly` requires admitted controls to be **exactly** the source's
  feasible actions; nonemptiness is derived from `α` (no separate claim).
- `bound_actionScore_eq_primitives` — action scores are the source primitive
  sums `Σ P(x'|s,x,a) U(s'|s,x,a,x') v(s',x')`.
- `checkBellmanReceipt_sound_of_finite_world` — the soundness statement for
  the source-bound system, plus source feasibility of every selected action.

The Bellman target is terminal for evaluation only; P and U are not modified.
The baseline α is not assumed to be optimal or an equilibrium. A tied argmax
does not identify which optimal policy a solver or actor uses.

## Source emission and replay

`proof.control_emit` first runs the independent checker, then reflects the
α/P/U input (shared with `proof.finite_emit`), the feasible-action options,
target, value table and selected controls into `ReifiedControlTable.lean`.
Lean's `chosen t` is applied with `t + 1` transitions remaining; at goal and
forbidden states the receipt selects nothing, so the first declared feasible
action is reflected (`terminal_control_fill`). Infeasible P/U rows are the
documented Dirac extensions of `proof.finite_emit`.

Scope: at most two strategic states, two world states and two actions, and
1..6 transitions. Larger valid problems remain numeric-only.

```bash
python3 -B -m permansson_app.proof.control_emit problem.json receipt.json \
  --output /tmp/permansson-control-instance
python3 -B -m permansson_app.proof.control_source_check problem.json receipt.json \
  /tmp/permansson-control-instance
lake build PermanssonResearch
lake env lean /tmp/permansson-control-instance/ReifiedControlTable.lean
```

The emitted theorems are `options_exact`, `receipt_checked`
(`decide +kernel` on the full table), `bellman_values`,
`schedule_upper_bound`, `optimum_attained`, `selected_feasible` and one
`bellman_value_<y>` per joint state.

`verification/research/test_application_control_table_live_lean.py` compiles
the packaged example and a two-by-two fixture with an infeasible action, a
forbidden state and a strictly suboptimal action, audits every theorem's
transitive axioms against `propext`, `Classical.choice` and `Quot.sound`, and
requires single-line semantic mutations to fail at the falsified obligation:
a false value, a strictly suboptimal admitted action, an infeasible selected
action, a false terminal event, reversed time direction and admitting an
infeasible action.

## Trust boundary

Emission and source rechecks report `lean_status: NOT_EXECUTED`. A local or
CI compiler pass is not an authenticated proof receipt, independent
mathematical certification, empirical identification or release approval;
the historical `E_TOOLING_CLOSURE` archive gate is unchanged.
