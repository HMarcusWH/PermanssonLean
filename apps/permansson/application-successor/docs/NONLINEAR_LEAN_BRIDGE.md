# Nonlinear classwise occupation objective — source-bound Lean bridge candidate

**Development scope:** OPT-10 (nonlinear functional of the random occupation
limit), `feature/application-successor-full`, PR #115.
`nonlinear-stationary` evaluates, for every declared feasible deterministic
stationary policy of a finite α/P/U model, the expectation of the frozen
Boolean functional `1 - |p - 2/3|` of the true-descriptor share `p` of the
random occupation limit under an initial law, and reports the optimum and
the complete tie set; `receipts.nonlinear` independently rechecks it.

## Mathematical contract

`PermanssonResearch/ApplicationBridge/NonlinearReceipt.lean`:

- `lawScore` — the exact initial-law mixture of Research's
  `rationalObjective (booleanClassFunctional h)` (C10 Cramer absorption times
  the C11 class-law Boolean score) on `feedbackMatrix sys f`;
  `actualLawScore` — the same mixture of `actualObjective`, the expectation of
  the functional of the actual random occupation limit (C2).
  `lawScore_eq_actual` uses `rationalObjective_eq_actual`.
- `checkBooleanClassObjective` / `checkBooleanClassObjective_sound` —
  decidable: every `StationaryChoice` of the system has its listed value, the
  optimum bounds them all, the tie set is exactly the optimal policies, and
  it is nonempty. The check enumerates the whole policy class.
- `checked_classwise_objective` — every listed value is the actual objective.
- `checked_stationary_class_optimum` — the optimum is attained and is the
  maximum of the actual objective over every admissible deterministic
  stationary feedback policy; the tie set is exactly the optimal set.

The aggregation order is fixed: expectation of the classwise functional,
never the functional of the expected descriptor. Randomized and
history-dependent policies are not compared.

## Source emission and replay

`proof.nonlinear_emit` runs the independent checker, reflects the model and
binds it with `boundControlSystem` (shared `control_emit.bound_system_lines`,
whose control-table output is byte-identical), so the policies are exactly the
declared feasible action maps with P and U fixed. It emits the descriptor
`h`, the initial law `μ`, a value table over action maps, the optimum and the
tie set, then `receipt_checked`, `stationary_optimum` and one
`policy_value_<i>` per listed policy. Scope: the shared literal reflection
bound and at most 16 policies.

```bash
python3 -B -m permansson_app nonlinear-stationary request.json --output /tmp/nl
python3 -B -m permansson_app.proof.nonlinear_emit request.json \
  /tmp/nl/nonlinear_receipt.json --output /tmp/permansson-nonlinear-instance
python3 -B -m permansson_app.proof.control_source_check --family nonlinear \
  request.json /tmp/nl/nonlinear_receipt.json /tmp/permansson-nonlinear-instance
lake env lean /tmp/permansson-nonlinear-instance/ReifiedNonlinear.lean
```

`verification/research/test_application_nonlinear_live_lean.py` compiles the
packaged request (4 policies) and a 16-policy two-copy model, audits axioms,
and requires single-line mutations to fail at `receipt_checked`: the
functional of the expected descriptor substituted for the classwise
expectation, an over-claimed tie set, a false optimum, a changed descriptor
and a different (normalized) world kernel row.

## Trust boundary

Emission and source rechecks report `lean_status: NOT_EXECUTED`. A compiler
pass is not an authenticated proof receipt, independent mathematical
certification, structural identification, empirical identification or
release approval.
