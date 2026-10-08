# CQ-1 / Part 2 — typed finite constitutive certificate (research)

**Status:** Draft PR #37. New proof statements are provisional until the
committed research target, transitive axiom audit and executable fixtures pass.
No promotion to the frozen v0.1.8 GR/PR definitions or application statuses.

Part 1 (merged PR #36) already provides measurable bounded finite-prefix
properties, exact agreement with the canonical path law, and the factor-one
geometric TV expectation-error theorem. This second research increment
combines those with existing *typed strategic interventions*, **region-wide**
finite persistence and **uniform** constitution over the original verified
comparison set `B₁`.

## Mathematical contract

- `L` counts transitions, including path coordinates `0, ..., L`.
- Baseline model `M`, frozen `RegimeSpecification spec`, and
  `B₁ : ConstitutiveComparisonSet M spec`.
- `J : AdmissibleStrategicIntervention F` modifies the strategic generator,
  preserving the original structural world primitive `P`.
- `FiniteConstitutiveCertificate` requires the *existing*
  `IsFinitePersistent M spec L eta` with its **∀ y ∈ spec.region**
  quantifier, together with `0 < κ ≤ constitutiveMargin ... B₁ J`
  for a bounded finite-path observable `f`.
- `StrategicApproximationPair` packages a second baseline and admissible
  strategic intervention with a separate proof `approx.world = M.world`.
  Each intervention preserves its baseline P by the frozen type system.
- `FinitePathModelErrors` binds two one-step event-TV errors δ₀, δJ
  (global over states) and distinct nonnegative output errors b₀, bJ,
  measured against the *actual* finite-path expectations of the approximate
  model and its intervention. Both pairwise comparisons share their start y.
- The frozen `B₁` remains the comparison **evaluation domain**. Robustness
  does not assert it is itself a verified comparison set for the approximate
  model (that requires a separate nontriviality witness).

The research target is the explicitly budgeted pair of inequalities:

```text
for every y in B:
  (1 - eta).toReal - e(L, δ₀) <= approxSurvival(y, L).toReal

uniform margin over the original B₁:
  κ - (e(L, δ₀) + b₀ + e(L, δJ) + bJ) <= approximateMargin

e(L, δ) = 1 - (1 - δ)^L
```

The margin certifies a nonzero approximate uniform effect only if the
remaining budget is strictly positive. The survival lower bound is algebraic
and may be negative; when reporting a nonnegative probability floor it is
truncated at zero, not advertised as a strictly positive survival guarantee.

**No approximation-QSD requirement:** only baseline survival is required.
An intervention may destroy persistence. The stronger `IsFinitePersistent`
for the approximate baseline with a new ENNReal η requires a distinct
normalization/gate; a raw real inequality is not silently rebranded as that.

## Dependency crosswalk

| Research file | New purpose | Frozen theorem/interface reused |
| --- | --- | --- |
| `InterventionPair.lean` | Shared-P typed pair | `AdmissibleStrategicIntervention.world_eq` |
| `SurvivalRobustness.lean` | ENNReal-to-real survival bridge, finite-event TV | `survivesThroughSet_eq_preimage_prefix`, `finitePrefix_eventTotalVariation_le_geometric` |
| `Certificate.lean` | Bundled baseline finite survival and positive uniform margin | `IsFinitePersistent`, `constitutiveMargin`, `IsUniformlyStrategicallyConstitutive` |
| `PropertyErrors.lean` | Bounds actual model outputs and converts them to core error profile | `finitePathExpectation_abs_le_geometric`, `HasConstitutiveOutputErrors` |
| `Robustness.lean` | Strictly positive robust margin and combined theorem | `perturbedConstitutiveMargin_ge`, core perturbation machinery |
| `CertificateExamples.lean` | Positive typed finite witness, boundary proof | `Examples/ConstitutiveNoninvariance.lean` |
| `verification/research/test_cq1_finite.py` | Exact rational finite-state checks, not proof substitutes | Separate research CI step |

A genuine infinite-state formal example separating positive pointwise effects
from a zero uniform infimum remains outside this first PR's finite examples;
an executable finite-grid diagnostic cannot prove that universal distinction.
Original `QSDCounterexample.lean` already proves QSD alone is insufficient
for the original region-wide finite-persistence gate.

## Testing and release firewall

Run `lake build`, `lake build PermanssonResearch`, research transitive axiom
audit, explicit research root import coverage, placeholder/custom-axiom
scanner, and `python3 -m unittest discover -s verification/research -p
'test_*.py' -v`. Maintain the existing original Lean, executable verification,
and Linux/Windows application-contract workflows. No modifications to
`PermanssonLean/`, `PermanssonLean.lean`, frozen paper, historical
verification artifacts or application claim codes are permitted.

All mathematical assertions remain conditional on their declared hypotheses;
numerical tests cannot establish empirical coverage, world-model provenance,
or scientific identification.
