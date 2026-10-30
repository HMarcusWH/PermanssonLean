# Finite-horizon perturbation (TV budget) — source-bound Lean bridge candidate

**Development scope:** ROB-01 (finite TV budgets), `feature/application-successor-full`,
PR #115. `finite-perturbation` compares a baseline and an alternative finite
α/P/U model on the same joint states: row half-L1 distances and their maximum
`δ`, the half-L1 distance of the two initial laws, both region-survival
tables, both initial-law event probabilities and the budget
`min 1 (TV(μ, ν) + T δ)`; `receipts.robustness` independently rechecks it.

## Mathematical contract

`PermanssonResearch/ApplicationBridge/QuantitativeReceipt.lean`:

- `realized_eventTV_le_rowTV` — for the actual realized kernels, every
  one-step event discrepancy of a row is at most its half-L1 distance
  (`abs_sum_le_half_of_sum_zero`), so a checked `δ` is a
  `HasUniformEventTVBound` (`realized_uniformTV`).
- `survival_difference_le` — from a common start, the region-survival
  probabilities of the two chains differ by at most `T δ`, by the original
  core Proposition 5.4 (`finitePrefix_eventTotalVariation_le_linear`) on the
  prefix laws (prefix marginals from `ExitReceipt.realized_pathLaw_prefix`).
- `checkFiniteTVBudget` / `checkFiniteTVBudget_sound` — decidable: exact row
  distances, their exact maximum, `δ ≤ 1`, normalized initial laws, the
  initial-law distance, the budget, both complete survival tables and both
  initial-law event probabilities.
- `checked_row_eventTV`, `checked_event_probabilities`,
  `checked_perturbation_bound` — the listed row distances bound actual event
  TVs; the event probabilities are actual initial-law mixtures of
  region-survival probabilities; their difference is at most the budget
  (initial-law mixing adds at most `TV(μ, ν)`, `abs_weighted_le_half`).

Equality of event TV and half-L1, localized history budgets and
original-margin lower bounds from the planned spec are not implemented here.

## Source emission and replay

`proof.perturbation_emit` runs the independent checker, reflects both models
(`base`, `alt`; `K`, `L` their induced matrices) and emits the receipt data,
`receipt_checked`, `event_probabilities`, `perturbation_bound` and one
`row_event_tv_<y>` per joint state, each concrete value obtained by kernel
evaluation. Scope: the shared literal reflection bound (the packaged
three-world example is outside it and is rejected with `REIFICATION_SCOPE`),
horizon 0..6.

```bash
python3 -B -m permansson_app finite-perturbation problem.json --output /tmp/pt
python3 -B -m permansson_app.proof.perturbation_emit problem.json \
  /tmp/pt/perturbation_receipt.json --output /tmp/permansson-perturbation-instance
python3 -B -m permansson_app.proof.control_source_check --family perturbation \
  problem.json /tmp/pt/perturbation_receipt.json /tmp/permansson-perturbation-instance
lake env lean /tmp/permansson-perturbation-instance/ReifiedPerturbation.lean
```

`verification/research/test_application_perturbation_live_lean.py` compiles a
2×2 instance whose alternative changes one P row and one initial law, audits
axioms, and requires single-line mutations to fail at `receipt_checked`: an
understated row distance, an understated budget, a dropped initial-law term,
a false event probability and an alternative whose world row reverts to the
baseline.

## Trust boundary

Emission and source rechecks report `lean_status: NOT_EXECUTED`. A compiler
pass is not an authenticated proof receipt, independent mathematical
certification, a long-run stability or GR/PR statement, empirical
identification or release approval.
