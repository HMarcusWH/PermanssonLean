# Finite almost-sure safety cores — source-bound Lean bridge candidate

**Development scope:** OPT-08 (finite infinite-horizon safety),
`feature/application-successor-full`, PR #115.
The `finite-safety` profile computes the greatest almost-sure controlled
invariant subset of a declared safe region by descending pruning, and
`receipts.safety` independently rechecks the chain and stationary witness.
This increment binds a checked core to the existing Research infinite-safety
theorems for the submitted source model.

## Mathematical contract

`PermanssonResearch/ApplicationBridge/SafetyReceipt.lean`:

- `CoreChecks` / `checkInvariantCore` — decidable: the reported core equals
  `invariantCore sys G` (the pruning fixed point after `|G|` steps) and each
  witness control on the core is admitted and stays in the core.
- `checked_invariant_core_eq` — the core is contained in `G`, controlled
  invariant and contains every controlled-invariant subset of `G`.
- `checked_core_iff_almostSureSafety` — on the actual path law, `y` is in the
  core iff some full-history behavioral controller keeps the trajectory in
  `G` forever with probability one (`invariantCore_iff_almostSureSafety`).
- `checked_outside_core_not_almost_sure` — outside the core every admitted
  controller is safe with probability strictly below one. Survival there can
  still be positive; no zero-survival claim is made.
- `checked_infinite_safety_optimum` — the core is the value-one set of the
  infinite safety value, which one deterministic stationary controller
  attains at every state against all behavioral pasts.

With `boundControlSystem` (see `CONTROL_TABLE_LEAN_BRIDGE.md`) the control
system is the source's fixed-action `P·U` rows with exactly the declared
feasible actions.

## Source emission and replay

`proof.safety_emit` runs the independent checker, then reflects the α/P/U
input, options, safe region, core and witness into `ReifiedSafetyCore.lean`
with `receipt_checked` (`decide +kernel`), `core_greatest_invariant`,
`core_iff_almost_sure`, `core_iff_value_one`, one `almost_sure_safe_<y>` per
core state and one `not_almost_sure_<y>` per pruned state of the region.
Witness controls are only checked on the core; elsewhere the first declared
feasible action is reflected (`noncore_witness_fill`).

Scope is the shared literal reflection bound (at most two per dimension). The
packaged three-world `finite_safety.v1.json` example therefore remains
numeric-only.

```bash
python3 -B -m permansson_app.proof.safety_emit problem.json receipt.json \
  --output /tmp/permansson-safety-instance
python3 -B -m permansson_app.proof.control_source_check --family safety-core \
  problem.json receipt.json /tmp/permansson-safety-instance
lake env lean /tmp/permansson-safety-instance/ReifiedSafetyCore.lean
```

`verification/research/test_application_safety_core_live_lean.py` compiles a
two-step pruning fixture, audits axioms, and requires single-line mutations to
fail at the falsified obligation: an over-claimed core, an under-claimed core,
a leaking witness, a false safe region and an admitted infeasible action.

## Trust boundary

Emission and source rechecks report `lean_status: NOT_EXECUTED`. A compiler
pass is not an authenticated proof receipt, independent mathematical
certification, empirical identification or release approval.
