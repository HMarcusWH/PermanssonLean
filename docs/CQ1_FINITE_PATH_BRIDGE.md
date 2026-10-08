# CQ-1 / Part 1 — finite-path property and total-variation bridge

**Status:** Research-theory PR, not part of the frozen v0.1.8 paper or formal
core. A declaration is **PROVED** only after the corresponding committed
research-library Lean build and axiom audit succeed. Do not infer proof status
from this guide alone.

[Architecture](PERMANSSON_RESEARCH_ARCHITECTURE.md#4-lane-a--finite-horizon-constitutive-quasi-regime-certificate-cq-1) ·
[Research build](RESEARCH_BUILD.md) ·
[Original formalization map](FORMALIZATION_MAP.md)

## Mathematical inputs and meaning

The first CQ-1 layer fixes a measurable state space `Y`, an integer `L≥0`
meaning exactly `L` **transitions** (`Y₀,...,Y_L`), and a measurable real
function `f` taking values in `[0,1]` on that prefix. It evaluates the same
frozen property under two distinct stationary Markov kernels from the same
point `y`.

The existing core's `ProbabilitySupport.finitePrefixLaw K y L` is a measure
on the dependent product indexed by `Finset.Iic L`. This module uses exactly
that domain, rather than creating a second time convention. At `L=0`,
the prefix contains the initial state only, so two models sharing the
initial point have the same finite-prefix property expectation.

The generic score is not necessarily the regime descriptor `h`; nor is it
the existing GR occupation-law target `ν`. It is an explicitly frozen
finite-horizon real-valued property. It can be **lifted** to the established
`RegimePropertyMap Y ℝ` by composing it with the infinite path's prefix map.
This is a representation bridge, not evidence of constitution by itself.

## Proposed Lean declaration crosswalk

| New research module | Intended declaration | Role |
|---|---|---|
| `ConstitutiveQuasi/Definition.lean` | `FinitePathProperty` | Measurable `[0,1]`-bounded score for `0..L` |
| same | `FinitePathProperty.integrable` | Finite measures integrate the frozen bounded score |
| same | `FinitePathProperty.expected`, `fromKernel` | Evaluation through arbitrary measure / established prefix law |
| `ConstitutiveQuasi/PathOutput.lean` | `pathLaw_finitePrefix_eq` | Canonical infinite path marginal = finite-prefix law |
| same | `finitePathExpectation_eq_pathLaw` | Equality of the two evaluation routes |
| same | `FinitePathProperty.toRegimeProperty` | Adapter to original whole-path PR property API |
| same | `finitePathExpectation_eq_baselineProperty` | Finite point-start evaluation = original baseline PR property value |
| `ConstitutiveQuasi/BoundedTV.lean` | `boundedIntegral_abs_le_one_sub_commonMass` | Factor-one expectation bound from dominated common submeasure |
| same | `finitePathExpectation_abs_le_geometric` | Apply original common-prefix mass estimate |
| `ConstitutiveQuasi/Counterexamples.lean` | `expected_zero_independent_of_kernel` | Zero-transition regression |
| same | `expected_one_le_uniformTV` | One-transition regression |

The stronger generic statement `|E_μ f − E_ν f| ≤ TV(μ,ν)` is **not**
postulated as an axiom or silently imported. The research theorem proves
the factor-one bound via a finite common submeasure, and then specializes
it to the core's already constructed `commonFinitePrefixLaw` and its
geometric retained-mass estimate.

Given `0 ≤ δ ≤ 1` and the **global** core assumption
`HasUniformEventTVBound K Ktilde δ`, the goal is exactly

```text
|E[K,y,L,f] − E[Ktilde,y,L,f]| ≤ 1 − (1 − δ)^L.
```

There is **no factor of 2** because `f∈[0,1]` and the core uses
event-supremum total variation. If values are instead in `[-1,1]`, if
starting laws differ, or if the kernel error is not uniform over the
relevant states, this specific theorem cannot simply be reused unchanged.

## Build and audit

Run from repository root:

```bash
lake build
lake build PermanssonResearch
```

The dedicated Research Lean workflow must additionally pass its transitive
axiom audit, direct-root-import check and placeholder/custom-axiom firewall.
The original Lean and other established CI workflows must remain green.
The frozen `PermanssonLean/` tree and `PermanssonLean.lean` are not edited.

## What remains for the complete CQ-1 certificate

Part 1 is **not** a finite quasi-regime certificate. A subsequent PR must
freeze a nontrivial comparison set `B₁`, prove finite survival over the
correct regime-wide domain `B`, apply an existing typed admissible
strategic intervention with world kernel `P` held fixed, and combine
baseline/intervention property gaps with explicit one-step and numerical
output error budgets.

Crucially, `IsFinitePersistent` quantifies over **all** `y∈B`; a
`B₁`-only result must carry a distinct diagnostic label. The intervened
model is *not* required to remain a generated regime. QSD remains optional
and distinct from uniform statewise survival. Neither model-relative
finite-path robustness nor green Lean CI establishes scientific
identification, empirical coverage, or a v0.1.8 Exact GR/PR claim.
