# Numeric residence and nonlinear occupation profiles — implementation status

## Scope and source

These two application-successor profiles are additive, fully exact-rational **numeric** calculations. They are not extensions of the frozen `PermanssonLean/` theory core. Bounded source-bound Lean bridges exist for both: `ResidenceReceipt` (family `residence`, all three modes; [`RESIDENCE_LEAN_BRIDGE.md`](RESIDENCE_LEAN_BRIDGE.md)) and `NonlinearReceipt` (family `nonlinear`; [`NONLINEAR_LEAN_BRIDGE.md`](NONLINEAR_LEAN_BRIDGE.md)). The numeric commands never run Lean, report `lean_status=NOT_EXECUTED`, and carry no imported mathematical certification; general nonlinear or control certificates are not claimed. The underlying research source patterns are the finite monitor and nonlinear Boolean-class constructions (including `PermanssonResearch/ReverseSolver/FirstEntryMonitor.lean`, `AvoidResidenceMonitor.lean`, `NonlinearBooleanClassFunctional.lean`, and `NonlinearMultichainAggregationFixture.lean`).

### `finite.residence_monitor.numeric.v1`

- Input: finite `α/P/U` strategic-world model; fully observed target/danger sets; deadline and its `entry_by` vs `completion_by` semantics; dwell transitions; complete initial law.
- Exhaustively solves a **bounded finite-horizon** dynamic program over state, observation time and literal monitor status; every admissible control action is evaluated using the unchanged physical `P` and update `U`. Baseline `α` is not treated as a certified equilibrium policy.
- Distinguishes **retryable** target residence from **first-ever entry** (a failed first attempt cannot be restarted), and **avoid** monitoring with danger checked before or at success. Success after `m` dwell transitions needs `m+1` consecutive observed target states, including the first. `entry_by T` evaluates through `T+m` where necessary; `completion_by T` evaluates only through `T`.
- `through_horizon_risk` is **NOT_EVALUATED**. A danger event after an already-achieved success does not revoke the success event; it is not covertly counted as a separate through-horizon risk objective.
- Bound: at most 8 joint states, entry/completion deadline 0–8, dwell 0–4. Independent checker reconstitutes original `P/U` action transitions and checks every reported Bellman equality and argmax set.

### `finite.nonlinear_classwise_stationary.numeric.v1`

- Input: exact finite `α/P/U` model, Boolean descriptor set, full initial distribution, frozen functional ID `boolean_one_minus_abs_p_minus_two_thirds.v1` and declared complete deterministic stationary action class.
- Enumerates **every feasible deterministic stationary selector** within the declared bound, replacing only the `α` action-selection table. Physical `P` and strategic update `U` stay unchanged; no equilibrium-selection or external causal-identification assertion follows.
- For each policy, computes bottom recurrent classes, stationary laws, initial absorption weights and the quantity `Σ_C Pr(C) [1 − |Pr(descriptor=True | C) − 2/3|]`. This is **not** obtained by applying the nonlinear functional after averaging class descriptor probabilities.
- Bound: at most 8 joint states and 64 deterministic stationary policies. No arbitrary caller-supplied functional code, history-dependent controls, or extended phase class is accepted.
- Independent checker separately reifies policies, checks actual class structure/stationary/absorption equations and all policy receipts, classwise functional values, exact maxima and tied maximizing policies. A multichain regression produces an expected classwise value of `1/2` and a distinct illegal barycenter value of `5/6`.

## Evidence boundaries

- Both profiles retain `lean_status=NOT_EXECUTED`, `scientific_claims_verified=false`, `empirical_identification=NOT_IDENTIFIED`, and nine separate unassessed scientific dimensions.
- CLI output is a numeric calculation plus independent receipt. `kernel_checked_proof`, independent mathematical certification, application release acceptance and publication approval are separate gates.
- The historical 45-case and 11-claim CERT program is neither implied nor replaced by these Python test counts.
- Unavailable capabilities and unsupported inputs fail closed; resource-limit failures do not prove mathematical infeasibility.

## Running

```bash
permansson-app finite-residence residence.v1.json --output result-residence
permansson-app nonlinear-stationary nonlinear.v1.json --output result-nonlinear
```

For supported exact examples and schemas after installation, use `permansson-app resources --full --output exported-resources`.

## Separate CI issue

The preexisting Research Lean regression runner invoked application tests in a Python environment without `jsonschema` or `referencing`, making all fully validated schema-using CLI calls fail with `SCHEMA_DEPENDENCY`. This change keeps Draft 2020-12 validation mandatory and makes the research discovery shim create a temporary, isolated interpreter environment with explicitly pinned schema dependencies **when missing**. If installation or testing fails, the Research suite fails. Protected workflow YAMLs and the independent historic archive T/T2 trust-profile contract are unchanged.
