# Lane C1 — finite absorbing-family and random occupation laws

**Scope:** Research-only Lane C1, PR #52. Frozen v0.1.8 core and the one-target
`RegimeSpecification.target` remain unchanged. This release certifies a
**specific genuine finite strategic-world witness**, together with conditional
generic absorbing-kernel lemmas. It is **not** a theorem for every finite
Markov chain and **not** a new generalized Permansson Regime.

## Typed stochastic witness and exact process

The physical joint state is `Y = Bool × Bool`, in order `t,u,a,b`.
The actual action-selection/world-transition/strategic-update composition
has kernel

```text
        t    u    a    b
    t   0    1    0    0
    u   0   1/2  1/6  1/3
    a   0    0    1    0
    b   0    0    0    1
```

`TypedStrategicWitness.inducedKernel_atom_entry` proves every atom of the
**actual** α/P/U induced kernel, and
`inducedKernel_eq_rational_transport` proves the complete kernel equality.
`TypedPrefixTransport`, `TypedCanonicalPathBridge` and
`TypedInitialMixture` establish finite-prefix transport and the infinite
canonical path-law initial-mixture identity; they do not assume independent
trajectory segments.

## Formally established at the last green research checkpoint

- `AbsorbingFamily` and `TypedAbsorbingKernel`: two distinct absorbing
  fixed points, and explicit finite measurable-family requirements.
- `KernelBlockSurvival.geometric_endpoint_power_of_absorbing_block`:
  Chapman–Kolmogorov geometric endpoint decay from a **uniform actual
  N-step kernel bound**, conditional on the stated kernel assumptions.
- `KernelCanonicalBlockBridge.canonical_geometric_noHit`:
  canonical no-hit bound from real path-time marginals, conditional on
  the explicit genuine marginal-power identity.
- `TypedMarginalPowers.canonical_eval_eq_kernel_pow`: the genuine
  infinite typed path law satisfies that marginal-power identity for
  every point start and time index.
- `TypedCanonicalHitting`, `TypedEndpointHitting`,
  `TypedEndpointInfiniteWeights`: all-horizon first-hitting results,
  exact ever-hit destination weights 1/3 and 2/3 from t/u.
- `TypedEventualHitting`, `TypedAbsorbingContinuation`,
  `TypedAlmostSureAbsorption`: almost-sure entry followed by
  absorbing continuation for **every initial probability measure**
  on Y, without an added hitting or independence hypothesis.
- `MeasurableDestination`, `TypedRandomOccupation`: a genuinely
  measurable random terminal destination and almost-sure weak
  pathwise empirical occupation convergence to its terminal Dirac law.
- `TypedTerminalEndpointLaw`: exact terminal state weights for t/u
  and singleton event weights for the measure-valued random limit,
  with explicit singleton-measurability premises on the latter.
- `TypedObservedLimit` and `TypedObservedExactGR`: deterministic
  observed occupation convergence for the nonconstant frozen
  descriptor `h(y)=y.1`, plus the original `IsExactGeneratedRegime`
  gate with separate Assumption 4.1 and invariance proofs.

## PR #52 completion pass

`TypedTerminalMixture` implements the point-absorber endpoint results
from the actual canonical time-zero law plus continuation, then
arbitrary-initial-law terminal probabilities by the proved infinite-path
mixture identity. These newest additions require a successful final-head
Lean build before they are reported as formally established.

The intended explicit terminal weights for
`μ = (μ_t, μ_u, μ_a, μ_b)` are

```text
p_a(μ) = μ_a + (μ_t + μ_u) / 3
p_b(μ) = μ_b + 2(μ_t + μ_u) / 3
```

The intended **law on probability measures**, distinct from its
barycenter, is

`Law_μ(ν∞) = p_a(μ) · δ_(δ_a) + p_b(μ) · δ_(δ_b)`.

These closed-form and whole-measure-law statements are not promoted
until the exact Lean declarations compile and their assumptions have
been reviewed. The earlier point-start weights and measurable-law
construction remain separately established.

A complete end-to-end witness-specific `N=2, q=1/2` kernel-derived
geometric no-hit certificate is a desirable second absorption route;
the unconditional exact-hitting absorption theorem is **already proved**
and does not depend on this extra integration.

## Theorem boundaries and negative controls

- **Not all absorbing families absorb almost surely.** Mere existence
  of an absorbing state does not guarantee hitting: the uniform N-step
  hypothesis or another hitting proof must be provided.
- **Random versus expected limit:** individual paths have limits
  `δ_a` or `δ_b`; their weighted mixture is a barycenter, not
  almost surely the trajectory's limit.
- **Multiple physical limits, one observed limit:** the nonconstant
  frozen descriptor sends both a and b to true while distinguishing
  the transient states from absorbing states.
- **Finite vs infinite:** the period-two example provides a separate
  empirical-occupation convergence regression despite oscillating
  marginals. Infinite and nonstationary generalizations are excluded.
- **Formal Exact GR vs confirmatory GR vs PR:** the witness
  `observedSpec.region=Set.univ` has a tautological invariance gate.
  Its observed convergence is substantive, but no strategically
  constitutive intervention is proved. The
  `IsConfirmatoryGeneratedRegime` descriptor-nondegeneracy condition
  requires its own named proof before that stronger label can be used.
- **Research mathematics vs field applications:** none of this proves
  empirical identification, causation, calibrated forecasts or
  geopolitically certified PR status.

## Release and CI policy

- Preserve `PermanssonLean/`, `PermanssonLean.lean`, `paper/`,
  `application/`, original version metadata, pinned Lean 4.34.0,
  mathlib manifest, and historical release artifacts.
- Import every new research module from `PermanssonResearch.lean`.
- Require all four GitHub workflows on the final PR revision.
  Standard PR workflows evaluate GitHub's **synthetic merge commit**;
  record both PR branch head and tested merge SHA. If a literal
  branch-head build is additionally performed, record it separately.
- Transitive axiom allowlist: `propext`, `Classical.choice`,
  `Quot.sound`. Reject `sorry`, `admit` and custom research axioms.
- Record exact-rational regression results, substantive theorem-statement
  review, and any unresolved premises. No claim of independent peer
  review without an actual external review.
- Do not promote, merge or mark the PR ready for review until all
  advertised **new** theorems compile and the scientific review closes.

## After C1

PR #53 remains responsible for general finite recurrent
communicating classes, periodic-class empirical ergodicity, arbitrary
class invariant laws and the full Lane C regime-family decomposition.
