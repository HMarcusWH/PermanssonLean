# Lane C8 — support-graph characterization of finite observed-event constitution

**Research PR:** [#59](https://github.com/HMarcusWH/PermanssonLean/pull/59).  
**Dependency:** [merged C7 PR #58](https://github.com/HMarcusWH/PermanssonLean/pull/58), verified C7 source HEAD `24024033f034a9cf1693e24177a183fe0c29dc9c`, merged to `main` at `784aaa2b5a74efa1a827de2fcbf6b81b30d29de4`.  
**Status:** mathematical-source proof checks **VERIFIED** at head `2775310bc0f15d0953ce730dcd635c9d000fbbea`; PR #59 remains **DRAFT / unmerged**, and its documentation-only release head requires fresh exact-head CI. The result is separate from the original frozen v0.1.8 paper, not a new application certification, empirical identification or external scholarly peer review.

## The exact mathematical claim

Fix a nonempty finite state space `Y` equipped with **measurable singleton atoms** (`MeasurableSingletonClass Y`) and the additional finite/discrete measurable and topological instances explicitly stated by each Lean theorem: in particular the G1–G2 canonical event bridge uses decidable finite states and standard-Borel measurability, while G3–G7 on typed joint state additionally use discrete topology and `OpensMeasurableSpace`. Fix a genuine homogeneous probability kernel `K` and a frozen measurable Boolean descriptor `h`. **The theorem package is not asserted for arbitrary finite spaces equipped with a non-discrete σ-algebra whose singleton transition atoms cannot be measured.** Let `E_h` be the actual infinite-path event that `h(w(n))` is true from some time onward. `Reachable K y i` means *finite reachability by strictly positive singleton transition atoms*, not a zero-weight graph edge or numerical-threshold approximation.

**G1 — positive good-class probability.** `P_y^K(E_h)>0` iff some recurrent communicating class on which every state is true-labelled is graph-reachable from `y`.

**G2 — reachable bad-class complement.** `P_y^K(E_h)<1` iff some reachable recurrent class has at least one false-labelled member. Even one false recurrent state renders an irreducible periodic class BAD, regardless of its convergent empirical occupation frequency. A false-labelled transient state alone is not bad.

**G3 — original baseline extremality.** Under actual original `IsExactGeneratedRegime M spec m` **and literal** `spec.convergenceMode = ConvergenceMode.almostSureWeak`, for each `y∈spec.basin`, `P_y(E_h)=1` iff the ORIGINAL `spec.target=δ_true`; otherwise `P_y(E_h)=0`. This DOES NOT assert that all possible Boolean occupation targets are Dirac. The proof uses original C3's same-path limit equality plus strict finite-class stationary support from C7.

**G4–G6 — opposing-class margin and original PR iff.** The quantitative equalities below are **conditional on an independently proved ORIGINAL baseline `IsExactGeneratedRegime M spec m` certificate, the literal equality `spec.convergenceMode = almostSureWeak`, and the original valid frozen comparison set `B₁`**. For one admissible typed alpha/P/U strategic intervention `J`, let `L=J.intervention.apply.inducedKernel`. If the baseline target is `δ_true`, opposing classes of L are BAD; otherwise they are GOOD. Define `r_J(y)` by summing the actual L-canonical class-selection weights of those opposing classes. For every frozen comparison state `y∈B₁`:
```text
constitutiveEffect(M, ψ_h, J, y) = r_J(y)
constitutiveMargin(M, spec, F, ψ_h, B₁, J) = min_(y∈B₁) r_J(y)
IsUniformGeneralizedPermanssonRegimeRelative(M, spec, m, F, ψ_h, B₁, J)
  iff IsExactGeneratedRegime(M, spec, m)
      and for all y∈B₁ some opposing recurrent class of L is positively reachable
```
Here `B₁` is the original nonempty `ConstitutiveComparisonSet`, not a post-hoc sample or arbitrary singleton, and the literal convergence-mode equality remains a separate hypothesis. The intervened model need not itself satisfy Exact GR.

**G7 — qualitative support invariance.** Two eligible interventions `J₁,J₂` in the same frozen family that have **exactly equal positive-edge support** of their induced kernels have equivalent yes/no original uniform relative PR classifications. This does **not** entail equal numerical margins, event probabilities, path laws, stationary laws, noncomputable class selection maps or alpha/P/U representations.

## Source DAG (draft; proof compilation not asserted here)

| Stage | New research module | Intended theorem |
|---|---|---|
| C8-01 | `FiniteObservedSupportReachability.lean` | class-weight nonzero iff actual graph reachability; G1 |
| C8-02 | `FiniteObservedBadClassReachability.lean` | exact complementary canonical mass and G2 |
| C8-03 | `FiniteObservedClassDirac.lean` | stationarity `h_#π_C=δ_true` iff class all-true |
| C8-04 | `ExactGRObservedEventExtremality.lean` | G3 under original Exact GR plus literal mode |
| C8-05 | `OppositeClassConstitutiveMargin.lean` | G4–G6 original quantitative PR iff |
| C8-06 | `ObservedSupportInvariance.lean` | transport of positive graph, classes and reachability |
| C8-07 | `TypedObservedSupportInvariance.lean` | typed G7 in the unchanged original PR predicate |
| Witness | `ExactSixStateC8SupportWitness.lean` | genuine original six-state Exact GR, two distinct admissible alpha-only interventions with identical positive support; original PR both ways |

The six-state witness keeps original region/basin/descriptor and the full alpha→P→U chain. The two new response kernels make original transient `u` absorbing and split the original A start `a0` once between `u` (bad) and `b0` (good), with rational probabilities 1/2 and 1/1000. This makes both interventions qualitatively constitutive while their actual numerical margins are different; the independent exact-`Fraction` tests check these computations. The Lean witness must be compiled separately to claim formal status.

## Audited mathematical-source checkpoint

Source HEAD: `2775310bc0f15d0953ce730dcd635c9d000fbbea`. Its actual GitHub PR synthetic merge into C7-containing `main` was `f061d26b6a3d5a0776d35607c00877df5d2afdc3` (not an independently invented kernel or unstated commit).

- [Research Lean #38429455138](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38429455138): full root build, **2,982** audited transitive declarations within `propext`, `Classical.choice`, `Quot.sound`, **267/267** research tests, **260** imported research modules, D0-F golden independent recheck, original default build and source firewall passed
- [Original Lean #38429454232](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38429454232): passed
- [Executable verification #38429454684](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38429454684): passed
- [Application contract #38429454707](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38429454707): Ubuntu and Windows passed

The preceding five Lean compiler diagnostics were repaired without changing the original GR/PR predicates, weakening theorem statements or adding axioms. This is the verified *mathematical source* checkpoint; the documentation-only release commit containing this record still requires its own exact-head/synthetic-merge CI before merge consideration.

## Independent adverse controls

`verification/research/test_lane_c8_support_graph.py` adds **50 exact-rational cases**, targeting a total of **267** inherited + new research tests if the C7 217-test baseline remains unchanged. Tests include two unrelated exact five-state graph families and the genuine six-state rational matrices, same graph with distinct transition entries and margins, nonextremal baseline failure of G7 without Exact GR, mixed periodic classes, false transients, partial comparison reachability, min-margins, zero-weight exclusions, and `10^-35` strictly positive transitions. Python tests independently recompute graph closure/absorption; they are NOT a proof of general a.s. convergence or model identification.

## Proof-integrity and release gates

- Same exact frozen six-state observation on both baseline and interventions, separate kernel-specific recurrent selectors, no post-hoc target change.
- Strictly positive atoms `K(x,{z})>0` for graph membership; no arbitrary probability threshold.
- Preserve the ORIGINAL `IsExactGeneratedRegime`, `ConstitutiveComparisonSet`, `IsUniformGeneralizedPermanssonRegimeRelative`, Assumption 4.1 and convergence-mode gates.
- Every new module imported directly by `PermanssonResearch.lean`; use `set_option autoImplicit false`; no `sorry`, `admit`, custom research axioms, or hidden theorem assumptions.
- Do not change `PermanssonLean/`, `PermanssonLean.lean`, C1–C7 sources, `paper/`, `application/`, Lean toolchain, Lake manifest, workflows or original historical release evidence.
- Before review-ready/merge, require Research Lean full source elaboration, transitive declaration audit with only `propext`, `Classical.choice`, `Quot.sound`, at least 267 successful research regressions, import/firewall/D0 golden checks, Original Lean, Executable verification, and Application contract Ubuntu+Windows all green on the **final PR head and exact GitHub synthetic merge**; record URLs and SHAs.
- An assistant/Codex source review does NOT substitute for external scholarly peer review. C7 has merged with separate author authorization; C8 requires its OWN completed formal build, review and explicit merge authorization.

## Branching / review note

C7 merged by a normal two-parent merge commit (`784aaa2b5a74efa1a827de2fcbf6b81b30d29de4`) with the exact same tree as the already certified C7 head. PR #59 remains based on `main`; GitHub comparison confirmed that its C7 source changes are already present on `main` and its remaining diff contains only C8 research modules, imports, tests and these research documentation updates. To align ancestry without rewriting reviewed C8 commits, the branch incorporates merged `main` via a non-force merge update. This does not waive fresh Research Lean, regression, axiom or exact synthetic-merge gates for C8.

**Scientific limitation:** no inference to nonhomogeneous D1 policies, infinite-state chains, all temporal event properties, empirical causal identification, or claim to priority over classical finite Markov-chain graph results.
