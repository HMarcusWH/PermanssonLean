# Residence values (retryable, first-entry, danger-avoid) — source-bound Lean bridge candidate

**Development scope:** OPT-03/OPT-04 (finite residence monitors),
`feature/application-successor-full`, PR #115.
The `finite-residence` profile computes exact optimal probabilities of
monitored residence events by dynamic programming over (time, joint state,
monitor state), and `receipts.residence` independently rechecks the table.
This increment binds the per-start values of all three residence modes to the
existing Research residence theorems for the submitted source model.

## Mathematical contract

`PermanssonResearch/ApplicationBridge/ResidenceReceipt.lean`:

- `ResidenceChecks` / `checkResidenceValues` — decidable: each reported
  start value equals `rollingResidenceValue sys (· ∈ target) dwell latest y`,
  the executable layer-wise table (`RollingResidenceTable.lean`).
- `checkResidenceValues_sound` — via `rollingResidence_optimal_and_attained`,
  the checked value bounds `behavioralResidenceProbability` for every real
  full-history behavioral controller and one controller attains it.
  `behavioralResidenceProbability` is the literal event: some block of
  `dwell + 1` consecutive target observations starts at observation time
  `≤ latest`, over `latest + dwell` transitions.

The application's retryable mode is the same event: `entry_by` deadline `d`
gives `latest = d`; `completion_by` deadline `d` gives `latest = d − dwell`;
in both cases the receipt horizon is `latest + dwell`.

The other two modes use the generic array-backed `rollingMonitorTable` with
explicit computable state enumerations (`firstEntryEnumeration`,
`avoidEnumeration`) and `rollingMonitorTable_eq_value`:

- `first_entry` → `checkFirstEntryValues` / `checkFirstEntryValues_sound`
  (`behavioralFirstEntry_optimal_and_attained`): the first target observation,
  at time `≤ latest`, must start the completed block; a broken run never
  retries.
- `avoid` → `checkAvoidValues` / `checkAvoidValues_sound`
  (`behavioralAvoidResidence_optimal_and_attained`): a retryable block within
  the prefix before the first danger observation; danger at the moment of
  success is failure, danger after success does not undo it.

Values are per start state; the initial-law mixture is not reflected.

## Source emission and replay

`proof.residence_emit` runs the independent residence checker, then reflects
the α/P/U input, options, target set, per-start values and shared `dwell` /
`latest` definitions into `ReifiedResidence.lean`, with `receipt_checked`
(`decide +kernel` on the rolling table) and one `optimal_residence_<y>` per
joint state stated against the literal rational value. Scope: the shared
literal reflection bound and 1..6 transitions; the packaged four-world
example remains numeric-only.

```bash
python3 -B -m permansson_app.proof.residence_emit request.json receipt.json \
  --output /tmp/permansson-residence-instance
python3 -B -m permansson_app.proof.control_source_check --family residence \
  request.json receipt.json /tmp/permansson-residence-instance
lake env lean /tmp/permansson-residence-instance/ReifiedResidence.lean
```

`verification/research/test_application_residence_live_lean.py` compiles
retryable horizons 3 and 6 (the second with dwell 2), a first-entry and a
danger-avoid instance, audits axioms, and requires single-line mutations to
fail at the falsified obligation: a false start value, a wrong dwell, a wrong
latest entry, a false target set, an admitted infeasible action, retryable
values substituted into the first-entry and avoid checks, and an emptied
danger set. On every fixture Lean's tables reproduced the Python per-start
values exactly, including danger taking priority at a target state.

## Trust boundary

Emission and source rechecks report `lean_status: NOT_EXECUTED`. A compiler
pass is not an authenticated proof receipt, independent mathematical
certification, empirical identification or release approval.
