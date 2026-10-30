# First-exit routing — source-bound Lean bridge candidate

**Development scope:** ANA-04 (first-exit routing and never-exit mass),
`feature/application-successor-full`, PR #115.
`finite-exit` computes, for every start in a declared region `B` of a finite
α/P/U model's induced chain, the survival table, the first-exit probability
per outside destination and step, the eventual first-exit probability per
destination and the never-exit mass; `receipts.exit` independently rechecks
it. This increment binds a checked receipt to events of the actual infinite
path law.

## Mathematical contract

`PermanssonResearch/ApplicationBridge/ExitReceipt.lean`:

- Events: `staysThrough B t`, `firstExitBy B d t` (the first state outside `B`
  is `d`, reached by time `t`), `firstExitAt B d` (eventually) and
  `staysForever B`. `staysForever_eq_compl` and
  `firstExitAt_pairwise_disjoint` show these partition path space.
- `checkExitRoutingReceipt` / `checkExitRoutingReceipt_sound` — decidable:
  the survival table and the cumulative first-exit table against the rational
  hitting recursion (goal `{d}`, forbidden `Bᶜ \ {d}`), a C10 Dirichlet
  certificate of the exit-stopped matrix `stopOutside K B` (outside rows
  replaced by self-loops), eventual routing equal to its weights for the
  singleton classes `{d}`, and never-exit mass `1 - Σ_d eventual`.
- `checked_survival_actual`, `checked_exit_by_actual` — finite-horizon entries
  are actual path-law probabilities (prefix marginals plus
  `typedHittingValue_eq_rational_all_horizons`).
- `checked_eventual_exit_actual` — `firstExitAt_eq_stopped_everAt` shows the
  eventual first-exit probability under `K` equals the eventual hitting
  probability of `d` under the stopped chain (both are monotone limits of
  equal finite-horizon values), which C10 identifies with the checked weight.
- `checked_never_exit_actual` — never-exit mass is the actual probability of
  never leaving `B`.

Routing is a subprobability; nothing is renormalized. Not implemented: the
planned `switch_retention_of_checked_profile` and restart-law statements
(StoppedFutureRestart / Proposition 4.2f), which need a verified stationary
intervened-model identity and target invariance.

## Source emission and replay

`proof.exit_emit` runs the independent exit checker, reflects the model
(`K := inducedMatrix input`), computes the stopped-chain Dirichlet
certificate as untrusted data, and emits `receipt_checked` plus, per start
`x ∈ B`: `survival_<x>` and `never_exit_<x>`, and per destination `d`:
`exit_within_horizon_<x>_<d>` and `eventual_exit_<x>_<d>`, each with its exact
rational value. Scope: the shared literal reflection bound, horizon 0..6.

```bash
python3 -B -m permansson_app finite-exit model.json region.json --output /tmp/exit
python3 -B -m permansson_app.proof.exit_emit model.json region.json \
  /tmp/exit/exit_receipt.json --output /tmp/permansson-exit-instance
python3 -B -m permansson_app.proof.control_source_check --family exit \
  --region region.json model.json /tmp/exit/exit_receipt.json /tmp/permansson-exit-instance
lake env lean /tmp/permansson-exit-instance/ReifiedExit.lean
```

`verification/research/test_application_exit_live_lean.py` compiles the
packaged single-destination instance, a two-destination split and a region
containing a closed class (never-exit mass 1/2), audits axioms, and requires
single-line mutations to fail at `receipt_checked`: renormalized routing,
dropped never-exit mass, a false survival entry, a false per-step entry, a
wrong stopped-chain class and a wrong exit destination.

## Trust boundary

Emission and source rechecks report `lean_status: NOT_EXECUTED`. A compiler
pass is not an authenticated proof receipt, independent mathematical
certification, a basin-persistence or GR/PR statement, empirical
identification or release approval.
