# Lane C2 — finite recurrent communicating classes (draft PR #53)

**Status: IMPLEMENTATION IN PROGRESS / NOT MERGE-READY.** This research-only
workstream follows merged C1 PR #52. The frozen Permansson v0.1.8 core,
`RegimeSpecification.target`, paper, applications, Lean/mathlib pin and
historical proof records must not change.

## The mathematical contract

For a nonempty finite discrete state space `Y` and a genuine homogeneous
Markov kernel `K`, let `C_i` enumerate *all* closed irreducible recurrent
communicating classes. The intended all-chain target is:

1. Decomposition into transient states and disjoint recurrent classes, with
   positive kernel-power probability for true reachability paths.
2. Under the **genuine canonical infinite Markov path law**, almost-sure
   eventual entry into exactly one class; thereafter almost-sure residence
   within that class. Establish a measurable total class selector.
3. Existence and uniqueness of class-supported invariant probability measures
   `π_i`, allowing periodic classes. Global invariant measures need not be unique.
4. Almost-sure empirical occupation convergence, **without aperiodicity**:
   `empirical(w,T) → π_(class(w))`, for every initial probability law.
5. The *entire measure-valued random limit law*
   `Law_μ(π_class) = ∑_i p_i(μ) · δ_(π_i)`. The barycenter of this law is not
   identified with an almost-sure pathwise limit.
6. Frozen descriptor transport `ν_i = descriptor_#π_i`; coincident descriptor
   limits must aggregate probability mass.
7. A separately named, nonvacuous *ex-ante* class-family certificate, and
   conservative recovery of the original `IsExactGeneratedRegime` **only**
   when all original well-posedness, Assumption 4.1, invariance, admissible-
   initial-law and single-common-descriptor-target conditions hold. No PR
   certificate follows without a separate typed constitutive intervention proof.

## Proof dependency order and hazards

- Rational matrix representation is **not** the existing `ℝ≥0∞` Markov kernel.
  Prove a conversion, including nonnegativity, exact rows, kernel powers and
  canonical path-law bridge before transporting any numeric claim.
- Build positive-edge reachability and finite closed-class decomposition.
  Mere graph edges with zero probability are not admissible.
- Obtain a uniform finite-step class-entry bound from actual kernel powers.
  Use Markov semigroup/canonical-path identities, not assumed independent blocks.
- Prove invariant-law existence, supported uniqueness and periodic-safe
  classwise occupation ergodicity. Candidate route: finite Poisson equation
  `(I-K)g = f - π(f)` and a bounded-martingale strong law. Prove both; do not
  assume stationarity, the Poisson solution or the desired strong law.
- Handle the random entry time via an actual post-entry conditional Markov
  continuation or countable time decomposition. Almost-sure closed-class
  residence is distinct from a universal statement about every path.
- Prove an arbitrary-initial-law canonical mixture at the genuine `M.pathLaw`
  level. C1's `Bool×Bool` mixture lemma is not generic.
- Distinguish weak convergence of empirical measures from convergence of
  one-time marginals; in particular the period-two class need not have
  convergent time marginals.

## Implemented initial foundation

- `FiniteCommunication.lean`: typed *rational* stochastic transition object,
  strictly positive edge relation, reflexive-transitive reachability,
  communication equivalence, and closed-subset support primitives.
- `ExactSixStateTyped.lean`: instantiate previously compiled D0-D/D0-E generic typed α/P/U realization, proving one-step event correspondence and **all-horizon typed finite-prefix class-union hitting equality** (with exact two-step values); no claim of a generic infinite occupation limit.
- `ExactSixStateCanonical.lean`: reuse the established D0 exact-rational-to-genuine-canonical-finite-prefix theorem for class-union hitting at two transitions (t=1/2, u=3/4); the infinite path and class destination are not yet certified.
- `ExactSixStateQuotient.lean`: checked rational four-state quotient row lumpability and exact stationary-law pushforwards; no unproved path-level factorization claim.
- `ExactSixState.lean`: exact six-state witness with transient states t/u,
  a deterministic period-two class A and an aperiodic class B; rational
  row stochasticity, explicit closed classes, invariant candidate laws and
  harmonic candidate class-entry weights. These are matrix equalities,
  **not** yet a canonical hitting probability or general ergodic theorem.
- `verification/research/test_lane_c_recurrent.py`: independent pure-Fraction
  Gaussian solve for stationary distributions and class-entry harmonic values,
  graph SCC discovery, periodicity/descriptor/mixture regressions.

## Verified general foundation — checkpoint 4084188a (11 October 2026)

The complete pre-extension source checkpoint
`4084188a465a620cb725810621ff4b16d5170846` passed **all four**
workflows, including Research Lean #38178847476 (2,283 transitive
declarations within the three-axiom allowlist; 108 exact regressions;
194 direct research imports; no proof placeholders).

- `RecurrentClassDecomposition`, `UniformClassEntry` and
  `CanonicalRecurrentResidence` prove genuine canonical a.s. entry into and
  unique eventual residence within one recurrent class, from arbitrary initial
  probability laws. These proofs do not assume the desired occupation limit.
- `FiniteInvariantExistence`, `FiniteClassInvariantExistence` and
  `FiniteClassInvariantMeasure` construct **unique class-supported actual
  invariant probability measures**, including irrational and periodic
  transitions; this is no longer an open theorem for the finite subclass.
- `CanonicalClassSelector`, `CanonicalClassWeights` and
  `ClassStationarySelectionLaw` establish measurable class representatives,
  genuine class-entry weights and the **whole law of the selected stationary
  class measure**. They do not establish that empirical occupation converges
  to that stationary measure.
- `FiniteOccupationTelescoping`,
  `FiniteOccupationLimitFromResidual` and
  `FiniteCanonicalConditionalStep` already construct the exact
  deterministic occupation residual and conditional transition identities.
  The compactness/uniqueness limit theorem has an EXPLICIT residual-
  convergence hypothesis; it is not the stochastic strong law.

## Post-checkpoint research additions — unpromoted until exact-head CI

The following source is present on the branch, with targeted compilation
repairs made in subsequent commits. Do not claim this entire group as
verified merely because an older source checkpoint was green.

- `FiniteOccupationOutside.lean`: after eventual recurrent-class residence,
  Cesàro empirical mass at each outside state vanishes.
- `FiniteMarkovCentered.lean`: exact row-centered mean zero,
  bounded real increments, and a one-step conditional second-moment bound.
  Neither full pathwise orthogonality nor normalized SLLN is asserted.
- `FiniteClassOccupation.lean`: genuine classwise vector limit **conditional
  on almost-sure vanishing stationarity residual**; a canonical a.e. bridge
  retains that explicit strong-law hypothesis.
- `ClassDescriptorSelectionLaw.lean`: frozen descriptor pushforward of the
  selected class stationary probability, full law and equal-observable-atom
  aggregation. This is a SELECTION law, not yet the occupation-limit law.
- `ClassDescriptorOccupationBridge.lean`: conditional weak-topology transport
  from a genuine physical occupation limit through a frozen descriptor;
  no physical occupation convergence premise is hidden.
- `BasinFamily.lean`: separately typed nonempty ex-ante basin, closed
  region and reachable-class family based on positive canonical class
  selection probability; still missing full regime-family classification.
- `ExactSixStateRegion.lean`: proper six-state region, row closure, frozen
  descriptor collapse and nontriviality witness; no Exact GR claim.
- `test_lane_c_basin_integration.py`: seven new independent exact-Fraction
  regression cases, locally passing. Software tests do not prove the
  universal Markov ergodic theorem.

## Still OPEN — strict scientific merge blockers

1. **Canonical finite Markov martingale SLLN:** prove conditional mean-zero
   for the actual path filtration, cross-time orthogonality, uniform
   second-moment bound and normalized almost-sure residual convergence;
   do not assume that residual convergence or independence.
2. **Unconditional classwise occupation:** combine that SLLN with actual
   eventual class residence and unique supported invariant probability
   to obtain a.s. weak convergence for arbitrary initial laws, including
   periodic classes.
3. **Actual random occupation limit law:** identify the class stationary
   selection law with the **proved pathwise empirical limit**, obtaining
   equality of whole measures on the space of probability measures.
4. **Descriptor pushforward of the actual limit:** derive full observed
   random limit distribution and aggregate coincident descriptor limits,
   without choosing a descriptor post hoc.
5. **Structural basin-family certificate and original Exact GR recovery:**
   prove the genuine family gates and the original Assumption 4.1,
   exact invariance, full initial-law convergence and single-common-target
   conditions; keep a separate PR intervention witness mandatory.
6. **Six-state infinite-path realization and adversaries:** prove the
   exact 1/3–2/3 random limit, periodic-marginal mismatch, proper-region
   Exact GR, C1 specialization, unreachable-class and nonconvergence
   boundaries as appropriate Lean theorems.
7. **Release gate:** every mathematical module above compiled and audited
   on the final exact source SHA and tested synthetic merge revision,
   theorem statement/hypothesis review, fresh regressions, source/axiom
   firewall, frozen-file diff and release documentation.

**Scientific promotion rule:** PR #53 stays DRAFT until the above headline
theorems are unconditional under their declared finite-chain hypotheses
and all final-head workflows are green. An axiom audit establishes checked
Lean declarations, not empirical validity, scholarly priority or the
truth of assumptions supplied to conditional lemmas.

## Protected boundaries and CI

Only add research modules, direct root imports, new research tests and
documentation. Keep `PermanssonLean/`, `PermanssonLean.lean`, `paper/`,
`application/`, toolchain/manifest and historical provenance unchanged.
Require research root compilation, full transitive axiom allowlist
(`propext`, `Classical.choice`, `Quot.sound`), no proof placeholders,
original Lean default build, application contract and executable regression
checks on the final tested PR synthetic merge revision.

## Status handoff

The earlier initial-implementation checklist has been superseded by the
verified-foundation and post-checkpoint inventory above. The code currently
implements the deterministic/Cesàro and stationary-class selection pieces;
**the unconditional stochastic occupation theorem remains the critical path**.
No frozen v0.1.8 definitions, paper files or application schemas were changed.
