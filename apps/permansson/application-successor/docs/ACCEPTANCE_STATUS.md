# Successor application — source-bound acceptance status

Developed against `main@3492b26707788293ca88c66637b6ba021c7e478d` (tree `9ef00ac4b2d4f928aa6551ef3f0dfeb2d4434452`) in pull requests #115 and #117. The release workflow came with pull request #118, and the archive repair with #116. Status updated 2026-11-01, after version 0.2.0 was released from `main@63a66c82a9ece4361f646ee13b6711192f831406` (tree `3b5e742ef1ee0cf3e1c27cc14500f3a33cfc01bb`) as `permansson-app-v0.2.0`.

## Distinct gates

| Object | This candidate | Evidence type |
| --- | --- | --- |
| C10 fixed six-state numeric | implemented, local installed example | exact native application + independent native receipt checker |
| C11 1..6-state stationary family numeric | implemented, periodic/multichain installed examples | exact native application + independent native checker |
| Exact numeric profiles (26, see `CAPABILITY_SCOPES.md`) | implemented; each with a packaged example, CLI tests and an independent checker | exact rational computation + producer-independent recomputation; no stronger status |
| Finite recurrent occupation and absorption | implemented | exact closed classes and independent stationarity/harmonic checker; random law kept separate from mean |
| Finite first-exit routing and never-exit mass | implemented | exact killed-path and eventual hitting checks; no normalization of never-exit mass |
| Exact finite killed-kernel survival and finite gap | implemented | comparison-state-complete recurrence; **not** Exact GR/PR or QSD |
| Rational LP primal/dual / Farkas checking | implemented | exact independent arithmetic checks; bounded candidate generator; a failed search is never reported as infeasibility |
| Legacy Application Standard v0.1.0 | read-only wrapped, seven historical fixture outcomes tested | retained original validator source pin |
| Offline Draft 2020-12 schemas | implemented as optional dependency, locally tested | packaged schema resources + no network resolution |
| Detached bundles | implemented, locally tested | offline SHA-256 integrity; not origin authentication |
| Domain evidence role / chronology envelopes | implemented, locally tested | noncomputational envelope; **not** empirical identification |
| Frozen-menu exact finite optimization | implemented | tied optimum over the declared menu only; not all controls |
| Fully observed finite hitting Bellman | implemented | full recurrence, admissible selected policy and all tied optimum actions |
| Finite almost-sure safety core | implemented | maximal descending pruning, independent stationary-witness check; excluded states may have positive survival probability |
| Finite-horizon TV perturbation | implemented | separate exact initial-law/kernel error, complete finite killed-survival table; not long-run stability |
| Source-bound Lean correspondence (finite α/P/U, LP, Bellman control table, safety core, residence monitors, frozen menu, killed-kernel survival, recurrent-class occupation, first-exit routing, nonlinear classwise objective, finite-horizon perturbation, typed quotient, patch grammar, risk flow, robust nature, observe-then-act belief, CQ-1 finite certificate, finite metric contraction, rational algebra witnesses, two-player protocols, private-stage saddles, adaptive block control, risk-cap infeasibility, CQ-1 transport) | implemented for bounded reflected instances; library built and instances replayed with pinned Lean v4.34.0 locally | instance theorems + transitive axiom audit + semantic mutations; application outputs still report `lean_status=NOT_EXECUTED` |
| Lean correspondence for every exact numeric profile | implemented for bounded reflected instances | every registered profile has a source-bound candidate family (see `CAPABILITY_SCOPES.md`); reflection bounds per family are in the bridge table below and the bridge documents; instances beyond them stay numeric-only |
| Full planned engine suite | **incomplete** (benchmarks FIX-01 and expert ADV-01 not implemented) | no false registry activation |
| Original 45 acceptance cases | **not newly certified** | independent research CERT remains separate |
| Later 11 mathematical claims | **not newly certified** | independent research CERT remains separate |
| Numeric release 0.2.0 on Linux CPython 3.12/3.13 | **released** 2026-11-01 as `permansson-app-v0.2.0` (see `RELEASE_ACCEPTANCE.md`) | owner-dispatched release workflow run 41313849870 and its gate: the run, its jobs and every artifact authenticated through the GitHub API, 260 evidence records re-derived from raw results; owner-engineering authority, no independent security review claimed; Windows out of scope |
| Release workflow (workflow-contract change) | **installed** (pull request #118) | dispatch-only workflow in the reviewed workflow contract and archive successor policy v2; an owner-approved change, not independently reviewed |
| Independent scholarly/empirical acceptance | **not assessed** | no reviewer/identification approval |

Scientific `numeric verified`, `Lean kernel proof`, `independent mathematical certification`, `release acceptance`, `empirical identification` and `publication` are distinct states. The application does not merge these into a single certified bit.

## Remaining work

What is implemented, planned and out of scope is tracked in
[`ROADMAP.md`](ROADMAP.md) and, path by path, in `IMPLEMENTATION_MANIFEST.json`.
The manifest reconciles the original v2 (217 entries) and v3 (251 entries)
inventories; generated `build/lib`, wheels, `.egg-info` and local logs are
never committed. Still open:

- **Contracts.** The full strict versioned request/report schema families
  and legacy byte/digest roundtrips (P2).
- **Data import.** Source-grade per-case raw-data importers. The current
  domain intake checks evidence envelopes only.
- **Planned profiles without an implementation.** Benchmarks (FIX-01) and
  expert non-finite conditional evidence (ADV-01).
- **Mathematical extensions not covered by the current bridges.**
  Multi-stage private games and occupancy, committed-game optimality,
  overlap-model (`CertifiedMenu`) atom certificates, and Exact GR/PR or QSD
  statements.
- **Evidence promotion.** Authenticated compiler receipts (outputs keep
  `lean_status=NOT_EXECUTED`) and Windows qualification of the bridges.
- **Trust and review gates.** The 30-workflow T2 migration, independent
  45-case/11-claim CERT, empirical identification and publication of
  results. None of the archive repair (pull request #116), the release
  workflow (#118) or the numeric release 0.2.0 claims an independent
  security review. Each is an owner-engineering decision, named as such.

A green local test is not a substitute for any of these. Per-round history
(commit by commit, with the CI results of each head) is in pull request
#115 and the Git log.

### Source-bound Lean bridges (local pinned-Lean evidence)

Every bridge does three things:

- It runs the independent application checker before emitting source.
- Where the request contains an α/P/U model, it reflects that model as a
  `FiniteWorldInput` and proves the structure the theorem needs on the
  literal tables. For control problems this is `boundControlSystem`, whose
  control `a` is the fixed-action `P·U` row and whose admitted controls are
  exactly the declared feasible actions. Other bridges prove held-fixed P and
  feasibility or exact patch rows.
- It has a Research-route live test (`verification/research/test_application_*_live_lean.py`).
  The test compiles real instances, audits every theorem's transitive axioms
  against `propext`, `Classical.choice` and `Quot.sound`, and requires
  single-line semantic mutations to fail at the falsified obligation.

The 24 live replay files contain 182 test methods.

| Profile | Lean module | Instance theorems | Live tests | Scope |
| --- | --- | --- | --- | --- |
| `finite.alpha_P_U.induced_kernel` | `FiniteWorldInput` | reflected rational α/P/U rows with feasibility, normalization and every induced joint atom of the realized Markov kernel | 7 | ≤2 per dimension |
| `lp.exact_rational.optimality` / `lp.exact_rational.independent_verification` | `LinearProgramReceipt` | weak duality, matching primal–dual optimum and strict Farkas infeasibility over all real feasible vectors of the normalized LP | 7 | ≤3 variables, ≤6 normalized constraints |
| `finite.hitting_bellman` | `ControlTableReceipt` | Bellman value, schedule upper bound, attainment, selected-action feasibility | 8 (2 positive, 6 mutations) | ≤2 per dimension, 1..6 transitions |
| `finite.almost_sure_safety_core` | `SafetyReceipt` | greatest invariant core; almost-sure safety iff in core; < 1 outside; stationary optimum | 6 (1 positive, 5 mutations) | ≤2 per dimension |
| `finite.residence_monitor` (retryable, first-entry, avoid) | `ResidenceReceipt` | literal residence optimum of each mode over all behavioral histories, attained | 7 methods (4 positive instances, 9 mutations) | ≤2 per dimension, 1..6 transitions |
| `finite.frozen_menu` | `MenuReceipt` | listed member values as canonical path-law probabilities; tie set exactly the listed optima; P/feasibility and undeclared generator held fixed | 7 methods (2 positive objectives, 5 mutations) | ≤2 per dimension, ≤4 members, 1..6 transitions; optimality over the declared menu only |
| `finite.killed_kernel.survival` | `MenuReceipt` (survival tables) | complete baseline/treated tables as canonical-law survival; horizon effects; P/feasibility and undeclared generator held fixed | 4 methods (1 positive, 3 mutations) | ≤2 per dimension, 1..6 transitions; finite-horizon diagnostic only |
| `finite.random_occupation` | `OccupationReceipt` | exact bottom classes (C10); weights as actual eventual-entry/selected-class probabilities; class laws (C11) as the actual a.s. occupation limit on each class event; whole random-limit law as the receipt's Dirac mixture (C2); mean law only its barycenter | 8 methods (2 positive, 6 mutations) | ≤2 per dimension; no GR/PR recovery or original-margin corollary |
| `finite.first_exit_and_survival` | `ExitReceipt` | survival and cumulative first-exit tables, eventual first exit per destination (via the exit-stopped chain's C10 certificate and a monotone limit) and never-exit mass, all as actual infinite path-law probabilities; routing kept a subprobability | 9 methods (3 positive, 6 mutations) | ≤2 per dimension, horizon 0..6; no restart law, switch retention or GR/PR |
| `finite.nonlinear_classwise_stationary` | `NonlinearReceipt` | every declared deterministic stationary policy's value as the expected Boolean score of the actual random occupation limit (C10/C11/C2 via `rationalObjective_eq_actual`), optimum maximal over the whole class, exact tie set | 7 methods (2 positive, 5 mutations) | ≤2 per dimension, ≤16 policies; no randomized or history-dependent policies |
| `finite.path_perturbation_tv` | `QuantitativeReceipt` | row half-L1 distances bound actual one-step event TV; initial-law event probabilities as actual region-survival mixtures; their difference within `min 1 (TV(μ,ν) + Tδ)` via core Proposition 5.4 | 6 methods (1 positive, 5 mutations) | ≤2 per dimension, horizon 0..6; finite horizon only, no history budgets or original margins |
| `finite.typed_quotient` | `QuotientReceipt` | complete strong lumpability per declared profile; fine and coarse finite-horizon survival/exit as actual path-law probabilities that agree; interventions hold feasibility, P and the undeclared generator fixed | 7 methods (2 positive, 5 mutations) | ≤2 per dimension, ≤4 profiles, horizon 0..6; no coarse α/P/U, Q1–Q3 domination or original margins |
| `finite.patch_grammar` | `GrammarReceipt` | each admitted block proved to be the baseline plus exactly its declared α/U patch rows with P fixed; block values, inclusion-minimal positive blocks and four-corner interactions as actual path-law statements | 8 methods (2 positive, 6 mutations) | ≤2 per dimension, ≤8 blocks, horizon 0..6; no downward closure, constitutive or PR certificate |
| `finite.one_step_risk_occupancy` | `FlowReceipt` | weak duality over every admissible real randomized one-step policy within the risk cap; reconstructed policy attains the optimum and is reflected as its own α/P/U model whose next-state law is the realized one-step law | 7 methods (2 positive, 5 mutations) | ≤2 per dimension; one transition only; no Farkas route, multi-stage, robust or private-information claim |
| `finite.rectangular_vs_committed_nature` | `RobustReceipt` | checked rectangular max-min tables equal Research's `value`; chronological saddle (some controller guarantees, some nature holds) for the optimized game, the fixed policy against rectangular nature and under each committed model; nature models change only P | 6 methods (2 positive, 4 mutations) | ≤2 per dimension, horizon 0..6; no committed-game or private-stage optimality |
| `finite.observation_history_tree` / `finite.one_step_observation_belief` | `BeliefTreeReceipt` | optimum over every real behavioral observation-history policy admitted on the hidden support, on Research's chronological belief law via an explicit time-shifted embedding; selected tree admitted and attaining; terminal law; best admitted blind sequence and `B ≤ D` | 13 methods (4 positive, 9 mutations) | ≤2 per dimension, ≤3 observations, horizon 1..3; no posterior/score restatement, hidden-state controllers or empirical observation model |
| `finite.cq1_constitutive_certificate` | `FiniteScoreReceipt` | Research's `FiniteConstitutiveCertificate` on the realized typed model with the typed admissible strategic intervention: region-wide finite persistence from killed survival at every region state, a comparison set whose states are exactly `B₁`, and the original constitutive margin equal to the checked κ; treated model holds feasibility and P (and the undeclared α/U component) fixed | 8 methods (2 positive, 6 mutations) | ≤2 per dimension, horizon 0..6; prefix-survival property only; no error-budget transport, Exact GR/PR or QSD |
| `finite.metric_contraction_perturbation` | `MetricReceipt` | declared rational metric checked and carried by a genuine metric type; coupling certificates give Research's all-law `IsW1Contraction` for the α/P/U-induced kernel and the row defects as `W1DualLE`; Research's `ContractivePerturbation` gives the A3 bound `W1DualLE π π̃ (δ/(1−ρ))`; a coupling plus attaining potential makes the invariant-law distance exact | 8 methods (1 positive, 7 mutations) | ≤2 per dimension (≤4 joint states); strict contraction only; no Polish-space moment argument, occupation-margin transport or empirical metric |
| `finite.rational_algebra_witness` | `RationalAlgebraReceipt` | rational witnesses decided exactly and cast to ℝ: seam rank ≤ 2 and common mode (rank ≤ 1, quadratic `δ (Σv)²`); LDLᵀ positive semidefiniteness with the shell complement equal to the declared `S`, the block-determinant factorization and shell equations; singular compatibility (bordered-form nonnegativity ⇔ `0 ≤ c − ⟨b,x⟩`, response independence) or incompatibility (no preimage, negative direction); Gram witness negativity under every operator perturbation below the exact threshold | 11 methods (7 positive instances, 10 mutations) | dimension ≤ 4 (shell ≤ 3); feature or operator identification with a strategic source is an explicit unmet premise |
| `finite.two_player_protocol` | `MultiAgentReceipt` | rational tables assemble Research's `FiniteProduct.Generator` (product action kernel, common × private updates) with physical P; the induced kernels of the baseline, closed-loop and open-loop protocols have exactly the declared joint rows (`Generator.actual_atom`); binary reduction of path laws and atoms; Research's matched closed/open-loop margin closures instantiated for the protocol | 8 methods (1 positive, 7 mutations) | each dimension ≤ 2, symmetric player state/action counts; no asymmetric types, mediated or correlated actions, private clocks or empirical game identification |
| `finite.private_control_stage_saddle` | `PrivateStageReceipt` | rational controller and nature mixtures form a two-sided saddle certificate; the value is the greatest `privateValue` over all real mixed controllers, the actual `stageLaw` saddle holds against every real nature row and controller, Research's `solvePrivateStage` returns exactly the value (solver not evaluated), and pure / revealed-control values equal the declared `r` | 8 methods (2 positive over four shapes, 6 mutations) | one stage, at most 4 controls and 4 parameters; no multi-stage private games, committed nature, learning or empirical identification |
| `finite.adaptive_block_control` | `AdaptiveBlockReceipt` | admitted blocks are the controls of `blockSystem` (each block's rows are `inducedMatrix` of a reflected input with feasibility and P held fixed and exactly its patch rows); the region-flag monitor table is Research's `FiniteMonitor.value`, and every full-history behavioral block controller is bounded by it on the actual trace law, with attainment (`monitor_optimal_and_attained`) | 8 methods (2 positive, 6 mutations) | at most 8 blocks, horizon ≤ 6 for Lean; no frozen-block comparison, overlap-model certificate, downward closure or empirical identification |
| `finite.one_step_risk_infeasibility` | `FlowInfeasibilityReceipt` | per-state risk floors (normalized Farkas ray) over the reflected fixed-action P·U rows and exactly-feasible actions; their initial-law total is the least risk mass of every admissible real randomized one-step policy, attained, and every such policy exceeds the cap | 7 methods (2 positive, 5 mutations) | one transition, at most 4 joint states and 5 occupancy variables; no multi-stage occupancy, private information or empirical identification |
| `finite.cq1_certificate_transport` | `CQ1TransportReceipt` | row budgets between the certified and approximate realized pairs (sharing P) and the remaining-margin condition; through `transportFiniteConstitutiveCertificate` the approximate pair carries a genuine `FiniteConstitutiveCertificate` with error `min 1 (η + env δ₀ L)` and margin `κ − env δ₀ L − env δJ L` | 7 methods (2 positive, 5 mutations) | horizon ≤ 6 for Lean, joint states ≤ 12; budgets are exact model distances, not empirical errors; no Exact GR/PR or QSD |

`ControlTableReceipt` failed to compile at `6eda7e9` (missing `Decidable`
instance); it is repaired and the full Research library builds. These are
local and per-commit CI observations, not authenticated proof receipts,
independent mathematical certification, empirical identification or release
approval; packaged examples beyond the reflection bound remain numeric-only.
