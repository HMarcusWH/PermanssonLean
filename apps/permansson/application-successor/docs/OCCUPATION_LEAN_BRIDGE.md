# Finite recurrent-class occupation — source-bound Lean bridge candidate

**Development scope:** ANA-02 (finite random occupation law),
`feature/application-successor-full`, PR #115.
`finite-occupation` computes the bottom recurrent classes of a finite α/P/U
model's induced chain, exact absorption weights, one stationary law per class
and the per-state mean law; `receipts.occupation` independently rechecks it.
This increment binds a checked receipt to the existing C10, C11 and C2
Research theorems.

## Mathematical contract

`PermanssonResearch/ApplicationBridge/OccupationReceipt.lean`:

- `JointClassChecks` / `checkJointClassReceipt` — decidable, reusing the
  providers: C10 `checkDirichlet` (the class list is exactly `bottomClasses`
  and the weights solve the complete Dirichlet boundary/harmonic system), C11
  `checkClassStationary` for each class law, and the mean law as the
  absorption-weighted mixture.
- `checked_class_absorption_actual` / `checked_class_selection_weight` — each
  weight is the actual infinite-path probability of eventually entering the
  class, equivalently that the canonical selected recurrent class is that
  class (`cramerWeight_eq_canonical_selected_class`, C10 column uniqueness).
- `checked_random_limit_on_class` — on that event, the actual almost-sure
  physical occupation limit (C2 `physicalOccupationLimit`) equals the
  receipt's class law as a probability measure (C11
  `checked_stationary_eq_native`).
- `random_limit_law_eq_receipt` — the whole law of the random occupation limit
  from a start state is the Dirac mixture of the receipt's class laws with the
  receipt's weights (an equality of measures on probability measures).
- `occupation_ae_limit` — the empirical occupation converges almost surely to
  that limit from every start (C2; no irreducibility or aperiodicity).
- `checked_mean_mixture` — the mean law is only the barycenter of the random
  law; it is not the realized limit.
- `checked_law_positive_on_class` — every class law is strictly positive on
  its class.

Not implemented: the planned `original_gr_recovery_of_checked_profile` and
`c10_original_margin_of_checked_protocol` corollaries, which need the
original specification, mode and invariance premises and an admitted
strategic-world factorization; none is synthesized from a numeric receipt.

## Source emission and replay

`proof.occupation_emit` runs the independent occupation checker, reflects the
model as `FiniteWorldInput` (`K := inducedMatrix input`), emits each class as
a `Finset`, the receipt as a `DirichletCertificate`, the class laws and mean
laws, and states: `receipt_checked` (kernel evaluation), `classes_exact`,
per class `class_<c>_stationary` and `random_limit_on_class_<c>`, one
`absorption_<c>_<x>` per class and state with the exact rational weight,
`occupation_limit`, `random_limit_law` and `mean_mixture`. Scope: the shared
literal reflection bound (≤2 strategic states, worlds and actions).

```bash
python3 -B -m permansson_app finite-occupation model.json --output /tmp/occ
python3 -B -m permansson_app.proof.occupation_emit model.json \
  /tmp/occ/occupation_receipt.json --output /tmp/permansson-occupation-instance
python3 -B -m permansson_app.proof.control_source_check --family occupation \
  model.json /tmp/occ/occupation_receipt.json /tmp/permansson-occupation-instance
lake env lean /tmp/permansson-occupation-instance/ReifiedOccupation.lean
```

`verification/research/test_application_occupation_live_lean.py` compiles a
transient state splitting evenly between a periodic two-cycle and an
absorbing state, and the packaged two-class model, audits axioms, and
requires single-line mutations to fail at `receipt_checked`: a false
absorption weight, a missing bottom class, a wrong class membership, a
normalized but non-invariant class law, the mean law replaced by one realized
class law, and a different (normalized) U row in the reflected source.

## Trust boundary

Emission and source rechecks report `lean_status: NOT_EXECUTED`. A compiler
pass is not an authenticated proof receipt, independent mathematical
certification, a GR/PR classification, empirical identification or release
approval.
