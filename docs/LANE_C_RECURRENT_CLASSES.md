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

## Explicitly OPEN until machine-checked

- Generic rational-to-kernel and canonical finite/infinite path bridges.
- Complete finite recurrent-class decomposition and genuine a.s. class entry.
- Measurable recurrent-class selector for the canonical path.
- Class-supported stationary-law existence *and uniqueness* for arbitrary
  finite irreducible recurrent classes.
- Classwise a.s. empirical occupation theorem, including periods > 1.
- Measurable full measure-valued limit law for every initial distribution.
- General typed strategic-world integration, descriptor-family and original
  Exact GR recovery for reachable common class limits.
- All advertised adversarial Lean countermodels and their proof statements.

**Scientific promotion rule:** Until all those are discharged with a green
exact-source-head proof audit, this remains a partial Lane C2 draft, even if
every currently imported theorem compiles. Do not claim completion solely
from exact-rational regression success or a green CI run.

## Protected boundaries and CI

Only add research modules, direct root imports, new research tests and
documentation. Keep `PermanssonLean/`, `PermanssonLean.lean`, `paper/`,
`application/`, toolchain/manifest and historical provenance unchanged.
Require research root compilation, full transitive axiom allowlist
(`propext`, `Classical.choice`, `Quot.sound`), no proof placeholders,
original Lean default build, application contract and executable regression
checks on the final tested PR synthetic merge revision.
