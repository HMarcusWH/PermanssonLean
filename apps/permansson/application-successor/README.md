# Permansson application successor — implementation candidate

**Development status (2026-10-29):** independently checkable **numeric foundation**, not a complete 217-/251-file application, release or mathematical certificate. The former recovered C10/C11 seed has been extended with strict finite `α/P/U` kernels, exact rational LP candidate/certificate verification, finite killed-kernel survival comparisons, exact occupation families and first-exit routing, offline schemas, historical legacy import, detached bundle integrity and chronology-aware domain evidence intake. No Lean correspondence module or independent review is claimed for these new components.

The package is additive under `apps/permansson/application-successor/`. The existing `application/`, `PermanssonLean/`, accepted release artifacts, native C10/C11 providers, Lean toolchain and `.github/workflows/` remain untouched. The original Application Standard 0.1.0 and its historical digest profile are **not** reinterpreted as the newer typed-rational identity profile.

## Installation

Python >=3.12. To install with complete offline JSON Schema checking, use the optional dependency:

```bash
python -m pip install './apps/permansson/application-successor[full-schema]'
permansson-app capabilities
permansson-app resources --full --output /tmp/permansson-resources
```

The C10 and C11 numeric routes require an exact audited repository source tree, with their native providers' stored SHA-256 pins. Run from an installed package with an explicit source root:

```bash
permansson-app run /tmp/permansson-resources/examples/c10.request.json \
  --source-root /path/to/PermanssonLean-main \
  --output /tmp/permansson-c10
```

The same `run` command supports the C11 periodic and multiclass example requests. Each output directory must be newly created **outside the source root**. A source ZIP can supply byte-identical numeric providers for local inspection and execution, but does not authenticate a Git commit or enable Lean replay.

## Additional exact numeric profiles

```bash
permansson-app finite-kernel /tmp/permansson-resources/examples/finite_world.v1.model.json \
  --output /tmp/finite-kernel
permansson-app lp-propose /tmp/permansson-resources/examples/lp.v1.model.json \
  --output /tmp/lp-proposal
permansson-app finite-survival /tmp/permansson-resources/examples/finite_survival.v1.json \
  --output /tmp/finite-survival
permansson-app finite-occupation /tmp/permansson-resources/examples/finite_world.v1.model.json \
  --output /tmp/finite-occupation
permansson-app finite-exit /tmp/permansson-resources/examples/finite_world.v1.model.json \
  /tmp/permansson-resources/examples/finite_region.v1.json \
  --output /tmp/finite-exit
```

`finite-kernel` validates finite strategic/world/action spaces and admissible actions, exact rational stochastic `α/P/U` rows, and the induced joint transition kernel in the order **α → P → U**. The independent checker recomputes the full finite kernel; there is no theorem claiming identification of the factors from external data.

`lp-propose` enumerates bounded exact vertices and proposes a primal/dual certificate. The *separate* `lp-check` can verify supplied exact primal/dual certificates or a Farkas infeasibility witness without invoking a producer. An unlocated vertex returns `NO_CERTIFICATE_FOUND`, not a theorem of infeasibility. The checked value does not identify the controller that another solver happens to return. Finite LP correspondence to canonical Lean theorems remains unsupported. `finite-survival` compares a held-fixed strategic intervention against a baseline with an exact killed-kernel recurrence and a complete declared comparison set; it checks every horizon row and the minimum absolute finite difference. It cannot establish Exact GR/PR, infinite-horizon persistence, QSD uniqueness or empirical transition probabilities.

`finite-occupation` computes all bottom recurrent classes, exact stationary laws and start-specific absorption weights. Its `expected_limit_laws` are explicitly the **means of random limiting class laws**, not the law realized on every sample path. The independent checker reconstructs the canonical `α → P → U` kernel and uses separately calculated communication/reachability sets and exact stationarity/harmonic equations.

`finite-exit` accepts an immutable explicit region and finite horizon, checks every survival value and first-exit-by-destination vector, and preserves never-exit mass without renormalization. Eventual exit is an exact finite-state Markov property; it does **not** establish an equilibrium, constitutive intervention or an Exact GR. Both routes are numerical-only and fail closed on false receipts. Proof correspondence to canonical Lean statements is still unimplemented.

## Evidence, legacy import and detached bundles

```bash
permansson-app legacy-validate /path/to/application.json \
  --source-root /path/to/PermanssonLean-main --output /tmp/legacy-check
permansson-app domain-validate /path/to/known_at_evidence.json \
  --output /tmp/domain-check
permansson-app bundle-inventory /path/to/result_files --scope numeric-only \
  --source-commit 3492b26707788293ca88c66637b6ba021c7e478d \
  --source-tree 9ef00ac4b2d4f928aa6551ef3f0dfeb2d4434452 \
  --output /tmp/detached-manifest
permansson-app bundle-verify /path/to/result_files /tmp/detached-manifest/detached_manifest.json \
  --output /tmp/bundle-check
```

The legacy reader invokes the historical offline validator without editing the seven original schemas or source. `domain-validate` preserves evidence role, original event and `known_at` dates, source publication time, missingness and uncertainty; it refuses to promote measurement support, a support matrix or an assumption-conditional simulation into an identified causal transition law. The importer checks the **envelope only**; it does not ingest or authenticate an entire external research companion.

The detached bundle manifest lists exact relative paths, content SHA-256 and source *claims*. Offline verification checks their bytes and rejects path traversal, symlinks and unlisted files. **A self-created manifest is not independently trusted:** supply `--expected-manifest-sha256` from an independent channel when an external trusted digest exists. Even with a trusted hash, source provenance, mathematical applicability, theorem proof and empirical identification need separate verification.

## Scientific and release boundaries

The nine dimensions of the original certificate remain separate from numeric verification. The new report uses `None` for **not assessed**, not `VALID`, `PR` or `CERTIFIED`. Every numeric route explicitly reports that Lean was **not executed**, independent mathematical certification is **not assessed**, and empirical identification is **not identified**.

This development branch does **not** implement the 19-engine / 17-Lean-bridge full target. Absent capabilities stay unavailable; no dummy source files or `sorry`/axioms are used to simulate completion. The separately controlled mathematical 45-case/11-claim CERT, active GitHub Actions trust-profile migration, and independent application release acceptance are outside ordinary application numeric tests.

## Development tests

```bash
python -B -m unittest discover -s apps/permansson/application-successor/tests -p 'test_*.py' -v
python -B -m unittest discover -s verification/research -p 'test_application_successor_numeric.py' -v
```

An installed wheel and source distribution must be tested in clean roots outside the checkout. The current newly tested runtime is Linux/Python 3.13.5; a previous recovered prototype had separate Linux/Python 3.12 evidence. Current-source Windows, fresh Python 3.12, and pinned Lean replay have not been qualified here. See `IMPLEMENTATION_MANIFEST.json` and `docs/ACCEPTANCE_STATUS.md` for source-by-source status and blockers. The execution plan and what is deliberately out of scope are in [`docs/ROADMAP.md`](docs/ROADMAP.md).

### Frozen finite-menu optimization

`permansson-app frozen-menu <request.json> --output <new-output>` computes exact rational finite-horizon survival or exit objective for each *explicitly listed* feasible alpha/U intervention, independently checks all choices, reports every tied optimum, and never claims that the menu exhausts all feasible policies. The mathematical/Lean and causal status remains unassessed. A packaged `examples/finite_menu.v1.json` provides a reproducible input.

### Checked finite feedback and intervention control

```bash
permansson-app finite-bellman /tmp/permansson-resources/examples/control_hitting.v1.json \
  --output /tmp/finite-bellman
permansson-app frozen-menu /tmp/permansson-resources/examples/finite_menu.v1.json \
  --output /tmp/frozen-menu
```

`finite-bellman` implements the actual finite-horizon fully observed hitting
recurrence: a goal gives terminal value one; a forbidden state value zero;
outside both, the value at remaining horizon `h+1` is the maximum
state-dependent permitted-action expectation of the `h` table. The controlled
transition is recomposed exactly from **P then U**, holding the physical
model fixed and optimizing over declared actions rather than treating baseline
`alpha` as optimal. An independent checker validates the entire time/state table
and **all** tied optimizers; a valid alternate tied controller need not be the
producer's reference choice. There is no data-to-Lean proof replay.

`frozen-menu` optimizes **only** over the declared 1–8 strategic interventions,
with exact full-menu assessment and a separate result checker. It does not
optimize the universe of control policies or claim causal constitution.

### Almost-sure safety and finite-horizon perturbation

```bash
permansson-app finite-safety /tmp/permansson-resources/examples/finite_safety.v1.json \
  --output /tmp/finite-safety
permansson-app finite-perturbation /tmp/permansson-resources/examples/finite_perturbation.v1.json \
  --output /tmp/finite-perturbation
```

`finite-safety` computes the **greatest almost-sure controlled invariant subset**
of a finite predeclared safety region, following the finite descending-prune
recurrence of `GreatestControlledInvariant.lean`. The checked receipt records
every pruning iterate and an admissible state-dependent stationary witness.
**Being outside the core does not mean zero survival probability.** It means
that almost-sure protection is not available from that state in the supported
finite fully observed model. The independent checker recomputes P/U support
and verifies that no excluded safe state has a control supported entirely on
the next candidate core.

`finite-perturbation` compares two typed finite transition models with the
same ordered joint-state inventory and two separately declared initial laws.
It computes exact killed-process finite survival through horizon `h`, every
row total-variation discrepancy, initial-law TV and the conservative bound
`min(1, TV(initial laws) + h * max_row_TV)`. The checker independently
reconstructs both induced kernels, the full survival recurrence and the
finite path-event inequality. These are **finite-time error bounds**, not
long-run stability, equilibrium, Exact GR, policy constitution, or statistical
identification.

Both new profiles use the same strict packaged schemas, numerical receipt
policy and nine-dimensional *unassessed* scientific certificate as C10/C11.
No application release acceptance is claimed.

### Additional exact numeric profiles (2026-10-29)

The finite residence and nonlinear classwise stationary-policy engines have independent exact receipt checks and bounded, explicitly scoped examples. See [`docs/NUMERIC_RESIDENCE_NONLINEAR.md`](docs/NUMERIC_RESIDENCE_NONLINEAR.md). Neither profile provides Lean replay, mathematical CERT, empirical identification or application release acceptance.

### Adaptive admitted-block control — numeric profile

`finite-adaptive-grammar` lets the controller choose one whole admitted patch block before every α → P → U stage, possibly a different one each time, and computes the exact survival or exit optimum over every full-history behavioral block controller, with tied optimal blocks, each frozen block's value and the adaptivity gain. See [`docs/NUMERIC_ADAPTIVE.md`](docs/NUMERIC_ADAPTIVE.md). Only declared blocks are controls; P is never changed.

### One-stage private-control robust value — numeric profile

`finite-private-stage` computes the exact private-control value of a finite payoff table when nature sees the controller's mixed strategy but not the realized control: an optimal rational controller mixture and a nature mixture forming a two-sided saddle certificate, the pure-control (revealed-control) value and the randomization gain. See [`docs/NUMERIC_PRIVATE_STAGE.md`](docs/NUMERIC_PRIVATE_STAGE.md). One stage only; no multi-stage private game or empirical identification.

### Finite two-player protocols — numeric profile

`finite-multiagent` assembles an exact finite two-player protocol with product actions from per-player action and private-update tables, a common update and physical P, and computes the baseline, closed-loop (only the treated player's mechanism replaced) and open-loop (a declared anchor profile installed, then the same replacement) joint kernels and their row total variation; P is never changed. See [`docs/NUMERIC_MULTIAGENT.md`](docs/NUMERIC_MULTIAGENT.md). No asymmetric player types, mediated or correlated actions or empirical game identification.

### Rational real-algebra witnesses — numeric profile

`finite-algebra` checks exact rational witnesses for four specialized profiles: seam equations and common mode (rank at most two or one), an LDLᵀ positive-semidefinite witness with the shell Schur complement, singular compatibility (a preimage with the bordered-form gap, or a kernel vector ruling out every preimage), and the Gram gap, witness and exact perturbation threshold. See [`docs/NUMERIC_ALGEBRA.md`](docs/NUMERIC_ALGEBRA.md). The identification of a strategic source with these matrices is an explicit unmet premise.

### Finite metric contraction and invariant-law perturbation — numeric profile

`finite-metric` computes exact Wasserstein-1 transport on a declared finite metric over the joint states: every baseline row-pair distance with an optimal coupling and an attaining 1-Lipschitz potential, the contraction factor ρ, per-row defects δ against a perturbed `α/P/U` model, both unique invariant laws and their exact distance, and the A3 bound `δ/(1−ρ)` only when ρ < 1. An independent checker validates every certificate. See [`docs/NUMERIC_METRIC.md`](docs/NUMERIC_METRIC.md). Not a Polish-space moment argument or an empirical metric.

### Finite CQ-1 constitutive certificate — numeric profile

`finite-cq1` computes, for one declared strategic `α/U` intervention with P held fixed, the region-wide finite persistence gate (killed survival from every region state, not only the comparison set), prefix-survival effects on a comparison set of at least two states and their uniform margin, and reports a finite constitutive certificate only when the gate passes and the margin is positive. An independent rational checker recomputes every value. See [`docs/NUMERIC_CQ1.md`](docs/NUMERIC_CQ1.md). This is **not** an Exact GR/PR, QSD, error-budget or empirical certificate. `finite-cq1-transport` transports a checked certificate to a declared approximate pair sharing P, under exact row-TV budgets (Research's `transportFiniteConstitutiveCertificate`).

### Exact finite robust nature chronology — numeric-only

`finite-robust-nature` implements an action-then-nature rectangular max-min Bellman table and separately evaluates a fixed stationary controller under a nature model committed at time zero. It preserves typed `α/U` while enumerating complete alternative physical `P` kernels; all reported values and ties are recomputed by an independent rational checker. See [`docs/NUMERIC_ROBUST_NATURE.md`](docs/NUMERIC_ROBUST_NATURE.md). This is **not** a committed-game controller optimum or a Lean/Exact-GR/PR/empirical certificate.

### Randomized one-step risk occupancy — numeric-only

The `one-step-risk` command optimizes a bounded randomized policy over one fully observed transition of the **actual typed** finite `α/P/U` model. The independent checker reconstructs original controlled transition rows, all mass and risk constraints, exact primal/dual LP optimality and the policy implied by the certificate rather than a preferred solver vector. See [`docs/NUMERIC_RISK_OCCUPANCY.md`](docs/NUMERIC_RISK_OCCUPANCY.md). This is not multistage control, unbounded policy optimality, a Lean certificate, Exact GR/PR, or empirical identification. When the cap cannot be met, `one-step-risk-infeasibility` certifies that exactly with per-state risk floors (a normalized Farkas ray), instead of the optimum route's `RISK_NO_CERTIFICATE`.

### Bounded one-step observation-conditioned control

`permansson-app one-step-belief <request.json> --output <new-output>` verifies a declared finite hidden-world prior and observation likelihoods, computes exact posteriors for reachable observations, and chooses one common legal action for each observation using complete bounded deterministic-policy enumeration. The independent checker reconstructs the original P/U law and does not trust the candidate action scores. Zero-probability observations have no posterior or inferred action. See [`docs/NUMERIC_BELIEF_CONTROL.md`](docs/NUMERIC_BELIEF_CONTROL.md). This is not general multistage belief-tree/POMDP control or a Lean/GR/PR certificate.

### Multistage finite observation-history control (numeric only)

A separate `finite-belief-tree` CLI supports 1–3 transitions, finite exact
`alpha/P/U` strategic-world dynamics and world-only observation likelihoods.
Policies use the complete available **observation history**, not hidden states
or future signals. The source `alpha` is bound, not replaced or certified.
An independent unnormalized-flow checker replays the chosen decision tree.
The two-stage example scores 55/64 versus a 3/4 blind fixed action sequence;
a separate small oracle enumerates 64 policy trees. See
[`docs/NUMERIC_MULTISTAGE_BELIEF.md`](docs/NUMERIC_MULTISTAGE_BELIEF.md).
This is **not** general POMDP optimality, a Lean proof, mathematical CERT,
empirical identification, release acceptance or publication approval.
