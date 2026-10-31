# Source-grade domain intake: safe, read-only inventories

`python -m permansson_app.governance_cli domain-import PATH --case CASE --output NEW_DIR`

Supported source inventories and observed original ZIP assets:

| Case | Expected source artifacts (minimum) | Meaning of output |
| --- | --- | --- |
| `russia_ukraine` | FROZEN_ANALYSIS_SPEC, inputs/events, state_weekly, transition_hindcast_daily | Input/modeled retrospective evidence, **not** certified causal dynamics |
| `hormuz` | FROZEN_SPEC, reproducibility/data/events, outputs/state_weekly | Descriptive states and source chronology, not forward proof |
| `iran` | final-audit structured update, all_measurements_typed, successor summary | Counterfactual/simulation versus measurements remain distinct |
| `midr` | release_spec, support_gain_matrix, transition_semantics, claim_ledger | Support/ranking objects are **not** transition probabilities |
| `brown_mackay` | FROZEN_SPEC, primary_results, INDEPENDENT_CHECK, gate_results | Frozen computational report, not Lean/PRT certificate transfer |
| `cross_conflict` | cross-conflict geometry summary, weekly matrix, refined sync episodes | Correlation/lag geometry not causal synchronization |

Archive intake enforces limits on member count, inflated bytes, per-member bytes,
compression ratio, path normalization, duplicate/casefold collisions, symlinks,
and exact member SHA-256. It reads only data bytes; Python/Notebook/Lean/HTML
programs inside packages are not run. `known_at` is assessed only if a
properly timezone-aware column exists; missing/ambiguous event-vs-known clocks
remain unresolved. Prospective freeze is tested separately by the clock module.

The importer does **not** establish that the input repository has been independently
authenticated, that a companion's own results have been regenerated, or that an
external `alpha/P/U` factorization is identified. Every result sets
`causal_alpha_P_U_identified=false` and `empirical_exact_GR_PR_certified=false`.
