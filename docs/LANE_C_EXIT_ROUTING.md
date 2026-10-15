# Lane C-Exit A — Exact first-exit routing (PR #66)

**Status:** implementation draft; every statement below is a proof target until
the matching GitHub source SHA passes Lean CI, source/axiom audits and independent
regressions. Author merge approval is not given.

- **Base:** `main@af9d1084664e9e51f7aba0045e98532e58c18829`, merged PR #65.
- **Normative contract:** audited PR66 C-Exit v1.1 specification; mathematical
  [v0.2.0 integration specification](PERMANSSON_V020_MATHEMATICAL_INTEGRATION_SPEC.md)
  §2, V20.3–V20.6 and V20.10.
- **Next lane:** PR #67 separately proves strategically intervened switch into
  another **independently certified** Exact Generated Regime. It is not in scope.
- **Semantic boundary:** all kernels are from the literal canonical
  `α→P→U` process, not independent transition tables.

## Intended theorem-to-source crosswalk

| Original mathematical obligation | Research declarations | Mandatory limitation |
|---|---|---|
| Genuine first-exit cylinders, finite/infinite and pairwise disjoint | `RegimeExit/ExitEvents.lean` `firstExitAtDestination`, `firstExitAt_eq_exitTime_succ`, `firstExitWithinDestination`, `firstExitEverDestination`, partition theorems | `n+1` first exit; `L=0` empty; destination `D\\B`; no evaluation at `∞` |
| Actual one-step subkernel `E_B` | `RegimeExit/ExitSubkernel.lean` `exitSubkernel`, `firstExitStepMeasure`, `firstExitStepMass_eq_lintegral` | Output-restricted; no artificial Markov normalization |
| Genuine finite/infinite point-start routing | `RegimeExit/ExitRouting.lean` `exitRoutingFiniteMeasure`, `exitRoutingInfiniteMeasure`, `firstExitStep_eq_pathEvent` | Original canonical path law; initial `y∈B` required |
| Law-initialized routing and indefinite survival | `RegimeExit/ExitRouting.lean` `exitRoutingFiniteMeasureFromLaw`, `exitRoutingInfiniteMeasureFromLaw`, `survivalForeverProbabilityFromLaw` | Supported `μ(B)=1`; existing `killedMeasureIterate`, not repeated fresh parameters |
| Finite and infinite first-exit identities and conservation | `RegimeExit/ExitConservation.lean` `exitRouting_eq_prob_exit_in`, `exitRouting_add_killedSurvivalMass_eq_one`, `exitRoutingInfinite_add_survivalForever_eq_one`, law-start analogues | Missing mass exactly indefinite survival; not every path exits |
| QSD destination law | `RegimeExit/QSDDestination.lean` `qsd_firstExitStep_eq_pow_mul`, `qsdRoutingFinite_eq_geometric`, `qsdRoutingInfinite_eq_fraction`, `qsdThetaOne_no_exit` | Certified frozen QSD; denominator only when `0<theta<1`; no uniform statewise persistence from QSD |
| Typed negative-control Markov models | `RegimeExit/ExitModels.lean` | Real `realizedModel` action/world/update factorization, F1/F2/F4 witnesses, not just postulated matrix |
| Independent arithmetic | `verification/research/test_c_exit_routing.py` | 22 `fractions.Fraction` destructive regressions, independent of Lean |
| Focused smoke | `.github/workflows/c-exit-smoke.yml` | Source-head Lean target and independent Python, **not** a substitute for full Research Lean |

## Exactly frozen mathematical objects

Let `B = spec.region`, `K = M.inducedKernel`,
`K_B(y,C)=K(y,C∩B)`, `E_B(y,D)=K(y,D\\B)`. For `y∈B`,

```text
F[n,D] = {w | (∀t≤n, w[t]∈B) ∧ w[n+1]∈D\\B}
Q[n](y,D) = (E_B ∘ₘ (K_B^n(y))) D
R[L](y,D) = Σ_(n<L) Q[n](y,D)
R[∞](y,D) = Σ'_n Q[n](y,D)
R[L](y,Y\\B) + P_y(τ_B>L) = 1
R[∞](y,Y\\B) + P_y(τ_B=∞) = 1
```

When `μ` is supported on `B`, replace `K_B^n(y)` with the original
`killedMeasureIterate M spec μ.toMeasure n`. QSD eigenmeasure
`μ K_B=theta·μ` with `0<theta<1` implies

```text
R[∞](μ,D) = (E_B ∘ₘ μ)(D) / (1-theta).
```

No model-preserving inference is made from finite arrival, and no claim
of an empirically identified exit law or causal intervention is made.

## Destructive acceptance

F1 `b→(b,a,c)` uses probabilities `(1/2,1/3,1/6)`, and
`R[L](b,{a})=(2/3)(1-2^-L)`; eventually A `2/3`, C `1/3`.
F2 `d→(d,b,a)` uses `(1/2,1/4,1/4)`; all-time survival `1/2`
from d; law `(1/3)δ_d+(2/3)δ_b` gives eventually exit `1/6`
and survival `5/6`. F4 witnesses that `δ_b` can be QSD at
`theta=1` while another state `d∈B` exits surely; reaching an outside
`a` does **not** imply staying there because `a→c`.

The independent Python suite runs 22 named cases. Those do not replace
Lean exact-path-law proofs or a genuine typed negative witness. All new
modules must import directly from `PermanssonResearch.lean`.

## Verification and promotion

On **the exact final source HEAD** and **GitHub's synthetic merge**:
Original Lean, Research Lean, Executable verification, Application contract,
C-Exit focused smoke, 3-axiom transitive audit, no proof placeholders, every
research module imported, C10/D0-F proof evidence preserved, frozen-core diff
clean. Record source head, synthetic merge and checkout SHAs and successful run
IDs separately. GitHub PR workflows normally test the synthetic merge;
the source-branch smoke tests HEAD. Never claim a later SHA inherits a previous
PASS.

**Author merge approval is explicitly required.**
