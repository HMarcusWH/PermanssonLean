# Exact typed quotients — source-bound Lean bridge candidate

**Development scope:** ROB-03 (finite quotient transport),
`feature/application-successor-full`, PR #115.
`finite-quotient` maps fine strategic/world states to declared coarse states,
checks complete strong lumpability of the induced chain for the baseline and
every declared intervention, and compares fine and coarse finite-horizon
survival (or exit) values on comparison states; `receipts.quotients`
independently rechecks it.

## Mathematical contract

`PermanssonResearch/ApplicationBridge/QuotientReceipt.lean`:

- `Lumpable K Q proj` — every fine state sends exactly `Q (proj x) c` mass
  into fiber `c` (complete, not one representative per fiber);
  `liftRegion proj R` — all fine states over `R`.
- `lumped_exit_value` — by induction on the horizon, the rational recursion
  for leaving the lifted region equals the coarse one at `proj x`;
  `quotient_survival_actual` — the actual fine and coarse region-survival
  probabilities agree (both via `ExitReceipt.survival_actual`).
- `checkQuotientProfile` / `checkQuotientProfile_sound` — decidable:
  lumpability, the region as a union of fibers, and the exact fine and coarse
  objective values on the comparison states.
- `checked_fine_value_actual`, `checked_coarse_value_actual`,
  `checked_quotient_transport`, `checked_fine_eq_coarse`.

This is an exact finite-horizon transport of the induced Markov law. No coarse
α/P/U decomposition, approximate bisimulation, GR/PR status or causal
identification is claimed; the planned Q1–Q3 source-domination and discounted
original-margin statements are not implemented.

## Source emission and replay

`proof.quotient_emit` runs the independent checker, reflects the baseline
(`base`) and each declared intervention (`member_<i>`) with held-fixed proofs
(feasibility, P and the undeclared generator, as in the menu bridge), defines
`K_<p> := inducedMatrix …` and the reported coarse matrix `Q_<p>` (its own
nonnegativity and row sums kernel-checked), and emits per profile
`profile_<p>_checked`, `transport_<p>` and one `value_<p>_<x>` per
comparison state. Scope: the shared literal reflection bound, ≤4 profiles,
horizon 0..6.

```bash
python3 -B -m permansson_app finite-quotient request.json --output /tmp/q
python3 -B -m permansson_app.proof.quotient_emit request.json \
  /tmp/q/quotient_receipt.json --output /tmp/permansson-quotient-instance
python3 -B -m permansson_app.proof.control_source_check --family quotient \
  request.json /tmp/q/quotient_receipt.json /tmp/permansson-quotient-instance
lake env lean /tmp/permansson-quotient-instance/ReifiedQuotient.lean
```

`verification/research/test_application_quotient_live_lean.py` compiles a
geometric-exit fixture (survival `8/27` at horizon 3) and the packaged
three-profile request in its exit variant, audits axioms, and requires
single-line mutations to fail at the falsified obligation: a stochastic but
non-lumping coarse matrix, a region that is not a union of fibers, a false fine
value, a projection merging fibers (all at `profile_0_checked`) and an
intervention that changes the world kernel (`member_0_held_fixed`).

## Trust boundary

Emission and source rechecks report `lean_status: NOT_EXECUTED`. A compiler
pass is not an authenticated proof receipt, independent mathematical
certification, a structural or causal identification, or release approval.
