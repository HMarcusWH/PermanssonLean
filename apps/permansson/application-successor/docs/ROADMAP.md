# Successor application — roadmap and execution status

Branch `feature/application-successor-full`; `main` is untouched. This page
records what has been built, what is planned next and what is deliberately
out of scope for an implementation branch. It is not an acceptance record:
the distinct gates in [`ACCEPTANCE_STATUS.md`](ACCEPTANCE_STATUS.md) stay
authoritative, and nothing here asserts independent certification, release
or empirical identification.

## Evidence tiers kept separate

| Tier | Meaning | How it is produced here |
| --- | --- | --- |
| Numeric | exact rational computation plus an independent checker that does not import the producer | `permansson_app` CLIs; every receipt says `lean_status=NOT_EXECUTED` |
| Source binding | a Lean source candidate re-derived byte-for-byte from the original request and receipt bytes | `proof/*_emit.py` and `proof/control_source_check.py` |
| Instance replay | the pinned Lean v4.34.0 compiler elaborates the candidate; `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`; semantic mutations fail inside the targeted theorem | `verification/research/test_application_*_live_lean.py` |
| Independent acceptance, release, empirical identification | outside this branch | owner-authorized review only |

## Built so far

* 22 additive exact numeric profiles registered in `data/capabilities.json`,
  next to the two closed native providers (C10, C11).
* 20 source-bound Lean bridge families under
  `PermanssonResearch/ApplicationBridge/`, each with an emitter, a byte
  recheck family and a pinned-Lean live replay with semantic mutations:
  finite α/P/U input, LP certificates, Bellman control table, safety core,
  residence monitors, frozen menu, killed-kernel survival, recurrent-class
  occupation, first-exit routing, nonlinear classwise objective,
  finite-horizon perturbation, typed quotient, patch grammar, risk flow,
  rectangular robust nature, observe-then-act belief, CQ-1 finite
  certificate, finite metric contraction, rational algebra witnesses and
  two-player protocols.
* Local evidence at `6b9cf13`: application suite 673/673 (Python 3.13 and
  3.12); full Research verification suite 2156/2156 including every live
  replay. Exact-head GitHub CI is tracked separately on the pull request.

## Planned next (in order)

| Step | Work item | Content | Status |
| --- | --- | --- | --- |
| P0 | REL-02 | this roadmap; reconcile planned inventory paths that implemented modules already supersede | this commit |
| P1 | APP-05 | one `lean-emit` / `lean-recheck` CLI over every emitter family | planned |
| P2 | OPT-06 | one-stage private-control robust profile with a two-sided saddle certificate; `PrivateStageReceipt` identifies Research's `solvePrivateStage` value without evaluating the solver | planned |
| P3 | OPT-09 | adaptive grammar control: admitted patch menus compiled into a shared-P control problem | planned |
| P4 | OPT-05 | risk-flow Farkas infeasibility route: no admissible policy meets the declared cap | planned |
| P5 | ANA-01 | CQ-1 certificate transport under exact TV error budgets | planned |
| P6 | REL-02 | remaining planned documentation set and a final local verification pass | planned |

Each step lands as its own commits: numeric profile and independent checker
first, the Lean bridge second, then the emitter, the byte recheck family and
the live replay.

## Out of scope for this branch

* Activating or relaxing any GitHub Actions workflow or guard; the inherited
  `archive-reproducibility` failure is reported, not relaxed.
* Running or claiming independent research CERT for the original 45 or the
  later 11 claims.
* Empirical identification, publication, merging to `main` or publishing a
  release without explicit owner authorization.
* Editing the protected theory core, the legacy `application/` root, the
  pinned toolchain or Lake configuration, or the existing C10/C11 providers.

## Inventory reconciliation

Planned inventory paths whose content shipped under a different module name
are marked `RECONCILED_SUPERSEDED_BY_IMPLEMENTED_EQUIVALENT` in
`IMPLEMENTATION_MANIFEST.json`, with `superseded_by` naming the implemented
paths, rather than duplicated. For example the planned
`test_application_bridge_<bridge>.py` tests are the
`test_application_<family>_live_lean.py` replays, `engines/metrics.py` is
`engines/metric.py`, `engines/specialized.py` is `engines/algebra.py` and
`engines/occupancy.py` is `engines/risk_occupancy.py`. Planned paths with no
implemented equivalent stay `PLANNED_NOT_IMPLEMENTED`.
