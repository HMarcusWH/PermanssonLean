# Permansson next-generation mathematical research architecture

**Document status:** RESEARCH SPECIFICATION v0.1 — proposed, unimplemented, subject to mathematical review.  
**Prepared:** 2026-10-08. **Scope:** Permansson Regime Theory / PermanssonLean; not an Allfather runtime integration.  
**Canonical repository:** [HMarcusWH/PermanssonLean](https://github.com/HMarcusWH/PermanssonLean).  
**Read-only design reference:** `0604fb2a2f8567614b4f29a3385d1c84266c1887` (`main` when this plan was drafted).  
**Immutable v0.1.8 mathematical source:** `c018f79ea4ce46f4f679ad5bca254509778fc53c`.  
**External OpenAI Math fork inspected:** [HMarcusWH/math](https://github.com/HMarcusWH/math), `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.  
**Lean/mathlib baseline:** Lean `4.34.0`, mathlib `v4.34.0` for the frozen Permansson proof snapshot; OpenAI Math's inspected Lean project uses `4.34.1`.  
**Authoritative completed-work index:** [FORMALIZATION_MAP.md](FORMALIZATION_MAP.md); [THEOREM_CROSSWALK.md](../verification/lean/THEOREM_CROSSWALK.md); [PAPER_VERIFICATION_MANIFEST.md](PAPER_VERIFICATION_MANIFEST.md).  
**Short roadmap:** [FUTURE_THEORY_ROADMAP.md](FUTURE_THEORY_ROADMAP.md).  
**Application-status firewall:** [APPLICATION_BOUNDARY.md](APPLICATION_BOUNDARY.md), [Application Standard](../application/APPLICATION_STANDARD.md).

> **Non-claim:** This document does not add a theorem, prove any of the proposed extensions, independently certify OpenAI Math, validate the Iran applications, modify the v0.1.8 paper, or authorize a theory-implementation PR. Proposed module and declaration names below are specifications, not existing source.

## 1. Executive purpose and deliverable

Permansson's established theory starts from a typed strategic generator and world-transition primitive, constructs the induced Markov kernel and canonical path law, and defines exact Generated Regimes (GR) and constitution-sensitive Permansson Regimes (PR). The next research programme should allow a user to state not only *what regime a process generates*, but also:

1. **A — Finite constitutive quasi-regimes:** What can be certified about survival and intervention-sensitive properties for a fixed finite horizon, including model and output errors?
2. **B — Grammar-robust constitution:** Which jointly necessary, redundant or substitutable blocks of strategic mechanisms matter, and which claims persist under a genuinely matched alternative component grammar?
3. **C — Multiple-limit regime families:** What if the same process reaches different recurrent classes or admits state-dependent or random limiting descriptor occupation laws?
4. **D — Reverse Regime Solver:** Given a frozen target, controls and risk constraints, which admissible strategic-generator changes can achieve it? Can we prove a policy and its value correct, or prove impossibility *within its declared policy/model class*?

OpenAI Math is an **external source of candidate results and adversarial examples**, not a trusted upstream theorem library. The highest-value first mathematics is likely an internally derived A certificate; finite D0/D1 can follow without waiting for B/C or external imports.

The output of this document is an **implementation contract**: every module has mathematical inputs, outputs, hypotheses, dependencies, counterexamples, gate criteria and nonclaims. A future implementer must not infer missing mathematics from a feature name.

## 2. Authority, frozen boundaries and statuses

### 2.1 Source hierarchy

1. The editorial-clean v0.1.8 paper and immutable Lean snapshot define the current GR/PR semantics.
2. `docs/FORMALIZATION_MAP.md` and `verification/lean/` specify the present proof ledger, including exact declarations and recorded checks.
3. `application/APPLICATION_STANDARD.md` (draft `0.1.0`) serializes v0.1.8 application claims; it is *not* a theorem prover or an authorization to upgrade a finite regime to `ROBUST_PR`.
4. This architecture and the short roadmap are **non-authoritative research designs** until a separately versioned release.
5. Empirical case-study documents inform examples and identification failure tests but do not establish real-world transition kernels.

Use these distinct statuses on every candidate claim: **EXISTING PROVED / EXISTING DEFINED / PROPOSED DEFINITION / PROPOSED THEOREM / SOURCE-INSPECTED EXTERNAL CLAIM / INDEPENDENTLY REBUILT EXTERNAL PROOF / EMPIRICAL OR COMPUTATIONAL CLAIM / OPEN**. A source file containing a theorem and proof term does not by itself justify the stronger "independently rebuilt" label.

### 2.2 Protected assets

Do not edit existing `PermanssonLean/` theorem statements, `PermanssonLean.lean`, the paper PDF/TeX, frozen release hashes, v0.1.8 Lean provenance or historical test records merely to accommodate a new extension. Do not repurpose the `application/` certificate statuses. Do not touch `Allfatherbusinessintelligence`, create runtime authority or register a Toolbox component.

New research can be housed in a distinct later library, with a separate build target; any change to the build definition or CI is *implementation*, not part of a documentation-only PR. Mark future labels so that no research status silently appears as v0.1.8 certification.

### 2.3 Present completed core: do not re-prove as "missing"

The mapped discrete core through Proposition 8.1 includes:

| Mathematical object | Existing Lean anchor |
|---|---|
| Typed generator and world primitive | `StrategicWorld/Model.lean` — `StrategicGenerator`, `StrategicWorldModel` |
| Induced joint kernel | `StrategicWorld/InducedKernel.lean` — `StrategicWorldModel.inducedKernel` |
| Canonical path law / well-posedness | `StrategicWorld/PathLaw.lean`, `StrategicWorld/WellPosedness.lean` |
| Frozen regime specification | `Regime/Specification.lean` — `RegimeSpecification` |
| Occupation and convergence | `Regime/Occupation.lean` — `empiricalOccupation`, `IsLimitingOccupationLaw`; `Regime/ConvergenceMode.lean` |
| Exact Generated Regime | `Regime/GeneratedRegime.lean` — `IsExactGeneratedRegime` |
| Killed-kernel survival, exit identities | `Regime/SurvivalBridge.lean` — `survivalProbability_eq_killedSurvivalMass`; `Regime/Persistence.lean` |
| QSD and finite quasi-regime | `Regime/QuasiStationary.lean` — `IsQuasiRegime`, `IsQSDCertifiedQuasiRegime` |
| Constitutive PR | `Regime/Constitution.lean` — `IsStrategicallyConstitutive`; `Regime/Permansson.lean` |
| Uniform margins and robustness | `Regime/ConstitutiveMargin.lean` — `constitutiveMargin`; `Regime/Perturbation.lean` — `robustUniformConstitution` |
| Finite-prefix event-TV | `Probability/TotalVariation.lean` and `Probability/FinitePrefixTV.lean` — `proposition_5_4` |
| Typed held-world-fixed intervention | `Intervention/Family.lean` — `AdmissibleStrategicIntervention`; `Intervention/Apply.lean` |
| Intervention-family signatures | `Intervention/Signature.lean`; `Regime/FamilyEquivalence.lean` |
| Factorization and quotient preservation | `Regime/RepresentationEquivalence.lean`, `Quotient/Preservation.lean` |
| Existing period-two and negative examples | `Examples/PeriodicExactGR.lean`, `Examples/ConstitutiveNoninvariance.lean` and related examples |

This table is navigation, not a substitute for inspecting each declaration's exact universe variables, measurability typeclasses, arguments and imports. The frozen paper's Appendix E specialized material, empirical identification, continuous time and new controlled processes are not magically included in that closure.

## 3. Shared semantic contract and conventions

### 3.1 Model and kernel

Let `S` be the strategic-state space, `X` the world-state space, `A` the action space and `Y=S×X`. The canonical model has action-selection kernel `α(da | s,x)`, world kernel `P(dx' | s,x,a)` and strategic-update kernel `U(ds' | s,x,a,x')`. The induced Markov kernel on `Y` is built in this **order**: select `a`, draw `x'`, then update `s'`. Formally, for measurable `E⊆Y`,

\[
K_{G,P}(y,E)=\int_A\int_X\int_S\mathbf1_E(s',x')\,
 U(ds'\mid y,a,x')\,P(dx'\mid y,a)\,\alpha(da\mid y).
\]

Here `G=(α,U)` is the strategic generator. A *strategic intervention* changes admissible portions of `G` while holding `P` fixed; it is **not** permission to change structural world equations. Both policy synthesis and grammar rewriting must respect this distinction.

### 3.2 Frozen specifications and quantifiers

The original `RegimeSpecification` contains `Σ=(B,B₀,h,ν,𝔠)` with frozen region `B`, basin `B₀⊆B`, descriptor `h`, target occupation law `ν` and convergence mode `𝔠`. The constitution comparison object `B₁` is *not* an arbitrary nonempty sample grid: `ConstitutiveComparisonSet` additionally demands `B₁⊆B₀` and a baseline path-law nontriviality witness.

When describing any new certificate, specify separately the quantifiers over `B`, `B₀`, `B₁`, initial distributions, model family and interventions. Never substitute a bound on `B₁` for an existing bound on **every** `y∈B` without creating a separately named weaker diagnostic.

### 3.3 Time indexing

Fix a nonnegative integer `L` meaning **L transitions** and states `Y₀,…,Y_L`. The existing `ProbabilitySupport.finitePrefixLaw K y L` has exactly that meaning; at `L=0` it is the point mass at `y`. Define `τ_B=inf{t≥0:Y_t∉B}`, so survival through `L` means `τ_B>L` and requires `Y₀,…,Y_L∈B`. Occupation horizons have a *different* established convention: `empiricalOccupation` uses `t=0,…,T−1` for `T>0`. Always translate horizons explicitly when these interfaces meet. No off-by-one convention changes inside the frozen library.

### 3.4 Total variation and error sources

Use the paper's **event supremum** convention: `TV(μ,ν)=sup_{E measurable}|μ(E)−ν(E)|` (not twice this quantity). Existing `HasUniformEventTVBound K K' δ` is global pointwise in starting state, with `0≤δ≤1` and countable/countably-generated measurability conditions for the finite-prefix theorem. Under the same initial point,

\[
TV(P_y^K\!\restriction_{0:L},P_y^{K'}\!\restriction_{0:L})
\le e(L,\delta):=1-(1-\delta)^L\le L\delta.
\]

For measurable `f:Y^{L+1}→[0,1]`, `|E_\mu f−E_\nu f|≤TV(μ,ν)`. If `f∈[-1,1]`, the constant may double. If `f` is unbounded or discontinuous in the relevant approximation topology, do not assert this bound automatically.

**Keep independent ledgers** for kernel approximation, output-evaluation approximation, uncertainty about the initial law, selection/search uncertainty, and empirical identification. Kernel TV alone does not resolve the others; point-started bounds do not automatically cover approximate initial distributions.

### 3.5 Certification vocabulary

A new scientific claim must say whether it is: (a) a definition/typed object; (b) a conditional Lean theorem; (c) a finite algorithm proved correct for an exact mathematical input; (d) a numerical witness for sampled models; or (e) an empirical inference with separate identification and coverage assumptions. Inability to find a witness is not proof of nonexistence. An existential witness for one frozen intervention does not prove a universal claim over all possible interventions.

## 4. Lane A — Finite-horizon constitutive quasi-regime certificate (CQ-1)

### 4.1 Motivation and boundary

Existing finite persistence and QSD machinery gives survival properties; existing strategic constitution gives an intervention-sensitive **whole-path property** criterion. CQ-1 provides an explicit **finite-prefix property class** with quantitative survival and constitutive-error budgets. It is a subordinate finite certificate, **never equivalent to Exact GR or PR** without independently proving all the original clauses.

### 4.2 Precise inputs

Freeze: model `M` and original world primitive `P`; `Σ` and its region `B`; verified `B₁ : ConstitutiveComparisonSet M Σ`; horizon `L∈ℕ`; baseline and one `J : AdmissibleStrategicIntervention F`; measurable `f` valued in `[0,1]` on the length-`L+1` prefix; `η∈[0,1]` and `κ>0`. Define `q_K(y)=E_y^K[f(Y₀,…,Y_L)]` and `q_{K^J}(y)` similarly. The output space for this first package is `ℝ` with absolute distance.

Main positive assumptions:

\[
\forall y\in B:\quad P_y^K(\tau_B>L)\ge1-\eta
\]
\[
\forall y\in B_1:\quad |q_K(y)-q_{K^J}(y)|\ge\kappa>0.
\]

The intervened model **need not survive** in `B`; destroying baseline persistence may itself be the constitutive effect. `B₁`'s nontriviality must come from the existing structure, not from a nonempty diagnostic sample.

### 4.3 Robustness theorem, proposed

Let `\widetilde M` and `\widetilde M^J` be *another admissible strategic baseline/intervention pair*, not arbitrary unrelated kernels. Require:
- Their world kernels are identical to each other; more strictly, when claiming same-world sensitivity to the original `P`, both equal `P`. If `P` itself is approximated, use a separately stated robustness result that does **not** mislabel this as a pure strategic replacement.
- Their induced kernels satisfy global one-step `HasUniformEventTVBound` bounds `δ₀` and `δ_J` relative to `K` and `K^J`, respectively.
- Their frozen `B, B₁, L` and finite-path property semantics match. Any compared property implementations add independently proven uniform output errors `b₀,b_J≥0` on `B₁`.
- The same starting `y` is used in each pair; initial-law errors are explicitly excluded from the initial theorem.

Then for every `y∈B` and `y∈B₁`, respectively,

\[
\widetilde P_y(\tau_B>L)\ge 1-\eta-e(L,\delta_0),
\]
\[
|\widetilde q_0(y)-\widetilde q_J(y)|
\ge\kappa-e(L,\delta_0)-e(L,\delta_J)-b_0-b_J.
\]

The approximate **uniform** effect margin is at least the same right-hand side by taking an infimum over the *same* `B₁`. The bound is informative when the right-hand side is positive. State the nonnegative truncation when reporting survival probabilities, but do not hide negative lower-bound expressions inside a misleading "certificate".

A separate optional theorem may allow survival assumptions only on `B₁`; label it **comparison-basin survival diagnostic**, not `IsFinitePersistent` or the existing `IsQuasiRegime`. Optional conditional-on-survival observables need a proved positive survival lower bound, and their error amplifies when the conditioning denominator is small. QSD certification remains an independent attachment.

### 4.4 Proof dependency graph and proposed declarations

Proposed paths under a future separate research library:
- `PermanssonResearch/ConstitutiveQuasi/Definition.lean`: `FinitePathProperty`, `FiniteConstitutiveCertificate`; no automatic conversion to `IsExactGeneratedRegime`.
- `.../PathOutput.lean`: prefix-law/whole-path evaluator agreement and `boundedExpectation_abs_le_eventTV`. Establish the measurable restriction/pushforward lemma instead of merely postulating equality.
- `.../Robustness.lean`: `finiteSurvival_of_prefixTV`, `finiteConstitutiveEffect_robust`, `finiteConstitutiveMargin_robust` and combined certificate.
- `.../Conditioning.lean` (optional later): conditional-on-survival estimate with explicit denominator.
- `.../Counterexamples.lean`: runnable small rational examples plus mathematically formal negative propositions.

Read first: `Regime/Specification.lean`, `Regime/Constitution.lean`, `Regime/Property.lean`, `Regime/ConstitutiveMargin.lean`, `Regime/Perturbation.lean`, `Regime/Persistence.lean`, `Regime/SurvivalBridge.lean` and `Probability/FinitePrefixTV.lean`. Reuse existing `robustUniformConstitution` where the property-output profile can be bridged; do **not** present the existing margin inequality as an invented new theorem.

### 4.5 Falsification and acceptance

Test: absorbing vs leaky states; intervention destroys persistence; exact zero effect; effects positive for each state but infimum zero; QSD with poor starts; `L=0` and `L=1`; event crossing only at `L`; `δ=0,1`; bounded vs unbounded `f`; inadequate state comparison set; and a pair with altered `P` rejected from the typed strategic-only certificate.

**Acceptance:** genuine nontrivial positive finite example; full parameter/hypothesis exposure; checked proof of both inequalities and typed-preservation requirement; no path to `ROBUST_PR` or exact GR without original gates; Lean axiom/placeholder audit and separate executable regression.

## 5. Lane B — Grammar-robust strategic constitution

### 5.1 What is new

Existing `InterventionKernelSignature.Matches`, `InterventionCompatibleFamilyEquivalence` and quotient preservation already prove important *matched* equivalences. B must not rebrand these as missing results. The new work is a typed finite **block grammar** and a theorem for constitution/minimality transported across genuinely compatible block systems.

### 5.2 Frozen block grammar

A grammar `Γ` contains: finite component type `C`; declared primitive targets for each component; admitted finite subsets/blocks `Allowed⊆Finset C` including explicitly chosen treatment of the empty block; an admissible replacement family for every block; and an induced-kernel semantics `K^{Γ,D}` for each admissible `D`. Replacements must preserve `P` for all strategic blocks. Specify whether different blocks can overlap in affected primitives.

**Default first release:** disjoint typed strategic components only, with a *single jointly specified resulting strategic generator* for each block and a proof that untouched fields retain the baseline. Do not silently implement sequential mutation of shared targets or assert order independence. A later release may allow overlap given explicit conflict/precedence semantics and separately proved composition laws. The empty block must induce the baseline kernel.

Define `Δ_{Γ,D}(y)=d(ψ(P_y^K),ψ(P_y^{K^{Γ,D}}))` for a fixed frozen property/metric and comparison set. For the first release, a block is *uniformly constitutive* when `inf_{y∈B₁}Δ_{Γ,D}(y)>0`. A **minimal** such block has no *proper admissible subblock* with this property. Pointwise nonzero constitution and positive uniform margin are distinct; minimality must state which predicate is used. There may be several incomparable minima or none.

### 5.3 Cross-grammar preservation, proposed

Let `Γ₁,Γ₂` be frozen grammars with matching baseline law, a map `Φ` between admissible blocks, matched intervention-induced path laws (or a proved path-law transport), identical grounded property semantics, and matched initial comparison states. For any matched block `D`,

\[
\Delta_{\Gamma_1,D}(y)=\Delta_{\Gamma_2,\Phi(D)}(y)
\]
and hence the uniform margins agree when comparison sets and metric correspond.

To conclude that **minimality** is preserved, additionally require `Φ` to preserve and reflect admissible proper-subblock inclusion (typically a poset isomorphism of admissible block systems). A mere bijection of labels or equality of baseline kernels is insufficient. A quotient case needs the already-established type-respecting kernel intertwining, property descent and admissible lifts, not just coordinate similarity.

### 5.4 Proofs, modules and adversarial tests

Proposed `GrammarRobust/Blocks.lean`, `Semantics.lean`, `Minimality.lean`, `Transport.lean`, `Counterexamples.lean`. Prove: empty-block identity, admissible-block typed world preservation, matched block path-law transport, effect equality, infimum/margin equality, minimality preservation under subblock-order equivalence.

Adversarial cases: two components whose **joint** removal changes the property while either singleton does not; redundant backups; two incomparable minimal blocks; a larger block canceling a smaller effect; equal baseline kernels with different response under intervention; incompatible overlapping replacements; and a bijection that fails to preserve subblock order. Demonstrate explicitly that there is no general monotonicity, unique-minimum or decomposition-independent causal attribution theorem.

## 6. Lane C — Multiple-limit and basin-family semantics

### 6.1 Starting point and scope

The frozen `RegimeSpecification` declares **one** target limiting occupation law `ν` across its admissible basin with a frozen convergence mode. Do not rewrite that field. C introduces a new research object, initially for **finite-state homogeneous Markov chains**, and proves conservative recovery of the old single-limit theory under strong enough hypotheses.

### 6.2 Finite-state recurrent-class first theorem

Assume finite nonempty state space `Y` and a genuine stochastic kernel `K`. Decompose into transient states and disjoint closed irreducible recurrent communicating classes `C₁,…,C_r`. Each class admits one invariant probability `π_i` (periodicity does **not** prevent empirical occupation convergence). For each initial point `y`, the chain eventually enters exactly one recurrent class almost surely; call its index `I(ω)`. Then

\[
\widehat\mu_T(\omega)=T^{-1}\sum_{t<T}\delta_{Y_t(\omega)}
 \xrightarrow[T\to\infty]{a.s.}\pi_{I(\omega)}.
\]

For a finite-valued or otherwise appropriately measurable frozen descriptor `h:Y→H`, set `ν_i=h_\#π_i`. The **random** descriptor occupation limit is `ν_\infty(\omega)=ν_{I(\omega)}`. The initial-state law of the *random measure* is

\[
\mathcal L_y(\nu_\infty)=\sum_{i=1}^{r}h_i(y)\,\delta_{\nu_i},
\qquad h_i(y)=P_y(I=i).
\]

The deterministic mixture `Σ_i h_i(y)ν_i` is its expectation in a suitable sense, **not normally the almost-sure pathwise occupation limit**. Do not conflate convergence of expectations, almost-sure random convergence, convergence in distribution of random measures, and convergence toward a declared closed set.

For infinite-state or nonhomogeneous generalizations, separate measurability, tightness, recurrence, selection and convergence theorems are required; this finite theorem alone does not supply them.

### 6.3 New regime-family object and recovery

Freeze: state/basin/region/descriptor; finite class index set; invariant laws, measurable family semantics and basin-entry weights; convergence notion; optionally an ex-ante set of admissible descriptor limits. Require structural nontriviality and the original exact-invariance gate independently where claiming a GR-like classification. A large ex-post set containing all observed paths must not count as successful certification.

**Conservative recovery proposal:** If for every admissible initial law the random limiting descriptor measure equals the same frozen `ν` almost surely, and all original Exact GR clauses (well-posedness, Assumption 4.1, invariance, convergence) are verified, then the old `IsExactGeneratedRegime` follows. Conversely, do not claim all multiple-limit specifications satisfy the original single-limit definition. PR transfer additionally requires the original typed constitutive intervention gates.

Proposed `MultipleLimit/RecurrentClasses.lean`, `LimitLaws.lean`, `BasinFamily.lean`, `Recovery.lean` and `Counterexamples.lean`. Bridge through `Regime/Occupation.lean` and `Regime/GeneratedRegime.lean` while retaining existing horizon and convergence semantics.

### 6.4 Countermodels

Two disjoint absorbing states (initial dependence); one transient state branching probabilistically into two absorbing classes (random trajectory limit); deterministic period-two cycle (empirical convergence despite distributional oscillation); an infinite-state process with growing alternating residence blocks (no general occupation convergence); descriptor collapsing distinct recurrent classes (distinct state-class limits but same observed limit); and an overbroad target set that vacuously contains everything.

## 7. Lane D — Reverse Regime Solver: synthesis plus verification

### 7.1 Objective and scientific firewall

D is an **inverse mathematical problem**, not a discovery oracle. Input: a frozen target, forbidden region, horizon, information model, admissible strategic controls and uncertainty scope. Output: a proved value and policy when hypotheses permit, a conditional candidate, a mathematically proved impossibility *for the quantified class*, or an explicit unresolved/unsupported result.

The Iran counterfactual work motivates **reverse specification → candidate search → forward holdout/simulation → risk-aware objective switch**. The research papers' diagnostic parameter vectors and corridor shares are **model-conditional**, not estimated real-world transition probabilities. Do not use these particular cases as mathematical premises or operational prescriptions.

### 7.2 D0 — finite frozen intervention menu (first solver milestone)

Freeze a finite nonempty set `I` of existing `AdmissibleStrategicIntervention F` objects. Each `i∈I` induces a time-homogeneous `K_i` via the current typed `apply` and `inducedKernel`. Freeze a finite state `Y`, initial point/law, target `G⊆Y`, forbidden `D⊆Y` with `G∩D=∅` and horizon `T`. Define `τ_G` and `τ_D` as first hitting times from time zero, including initial membership. For each **fixed-for-the-whole-horizon** intervention,

\[
v_i(y)=P_y^{K_i}(\tau_G\le T,\ \tau_G<\tau_D).
\]

D0 calculates each `v_i` exactly for mathematical finite inputs, obtains `max_i v_i`, extracts an argmax and proves the chosen value matches its actual induced kernel. This is an optimum over **the frozen menu**, not over all adaptive policies, all permissible strategic interventions or the true world. Allow the no-intervention baseline explicitly if it is to be a candidate.

Suggested `ReverseSolver/Target.lean` and `FrozenMenu.lean`; prove finite hitting recursion, argmax existence for nonempty finite menu, value soundness and typed world preservation. Validate with hand-computed two-/three-state examples and exhaustive enumeration.

### 7.3 D1 — finite fully observed adaptive controller

**Implementation note (research PR #45, D1-A):** The first scoped Lean
module constructs a finite *stationary state-feedback* policy over the
existing Unit × Fin n typed rational realization, with state-dependent
nonempty permitted controls, full canonical one-step equality and
all-horizon path/value transport. See [D1_CONTROLLED_KERNEL.md](D1_CONTROLLED_KERNEL.md).
It is **not** the full D1 Bellman or general typed-world theorem below.
Those remain subsequent proof obligations.

D1 is **new controlled-process theory**; do not pass a sequence of changing kernels off as one existing `AdmissibleStrategicIntervention`. First implementation constraints: finite nonempty `Y=S×X`, finite `A`, finite nonempty control menu `C(y)` at each state; controls select among *action-selection replacements* `α_c`. Hold `P` and `U` fixed. The selected control is chosen at the *current joint state*, before choosing action `a`; after `x'`, update `s'` exactly as in the canonical model.

For `c∈C(y)`, define `K_c(y,z)` by the original α/P/U integration order with `α_c` selected at `y`. Explicitly prove nonnegativity, stochastic row sum, and equality to the canonical induced kernel of the corresponding replacement when that replacement is frozen. For a feedback policy `π_t:Y→C` with `π_t(y)∈C(y)`, define its finite-horizon nonstationary law directly (or prove it equals a stationary clock-augmented kernel). The controller may use exactly the information allowed by the information contract; initial D1 assumes full observation of `Y`.

Target-success event: reach `G` no later than `T` **strictly before** entering `D`. Treat membership in `G` or `D` as terminal *for value evaluation*, not as a claim that the underlying world kernel physically absorbs there. With `V₀(y)=1_G(y)` (and `G∩D=∅`), the proposed finite-horizon Bellman recursion is

\[
V_{t+1}(y)=
\begin{cases}
1 & y\in G,\\
0 & y\in D,\\
\displaystyle\max_{c\in C(y)}\sum_{z\in Y}K_c(y,z)V_t(z)
& y\notin G\cup D.
\end{cases}
\]

Prove by backward induction: `V_T(y)` equals the supremum of target-before-danger probabilities over all admissible **state-feedback, finite-horizon Markov policies** in the declared class; then construct a maximizing policy and prove its actual finite-path law realizes this value. Explain why broader history-dependent policies cannot improve the finite fully observed Markov problem *if* that reduction is proved, rather than assuming it. Also prove the `T=0`, `G=∅`, `D=∅` and impossible target cases. A policy returned on a finite model is **not automatically** a valid new frozen intervention family member; typed strategy compatibility must be separately established.

Proposed modules: `ReverseSolver/ControlledKernel.lean`, `Bellman.lean`, `PolicySynthesis.lean`, `ForwardVerification.lean`, `Counterexamples.lean`. Preserve the canonical `α→P→U` ordering in all definitions.

### 7.4 Later solver variants: do not silently implement as D1

- **Reach-and-stay:** hitting a target is distinct from reaching and remaining there for `m` transitions or forever. Finite residence requires a product/clock state and new recursions; infinite residence needs viability/invariance hypotheses.
- **Hard risk budgets:** optimizing success subject to `P(\tau_D≤T)≤ρ` cannot generally use an unconstrained max-success Bellman equation. Define a constrained optimization state or a separate certificate/dual bound. Probability of forbidden entry is not the same as probability of failing to reach the target.
- **Robust model uncertainty:** for a frozen admissible model set `𝒦` distinguish a single shared policy, `sup_π inf_{K∈𝒦}P^{K,π}(\text{success})`, from model-specific policies, `inf_{K∈𝒦}sup_πP^{K,π}(\text{success})`. In general `sup inf≤inf sup`, with inequality possibly strict. Do not write a local robust Bellman recursion without specifying rectangularity, when nature chooses a model, and what observations reveal.
- **Partially observed or history-dependent controls:** require explicit observation kernels/belief-state sufficiency and cannot inherit the fully observed theorem automatically.
- **Grammar blocks (B):** each proposed block policy must satisfy its new block admissibility semantics before becoming a control option.
- **Regime-family outcomes (C):** optimizing entry into a particular recurrent class or its descriptor law requires an explicit objective and an independent bridge from finite hitting targets to asymptotic classifications.
- **Model mismatch:** no mathematical optimization of an assumed kernel identifies the true kernel or validates policy efficacy in the real world.

### 7.5 Solver result typing

Use a *conceptual* future result algebra, not the current application standard's nine-field status vocabulary:
- **PROVED_OPTIMUM(model, admissible policy class, horizon, objective, policy, value, proof)**;
- **PROVED_UNREACHABLE** (value zero for the *entire declared class*, not failed search);
- **FEASIBLE_WITNESS** (a proved admissible policy and lower bound, without global optimality);
- **COMPUTATIONAL_CANDIDATE** (numerically evaluated, no proof certificate);
- **UNRESOLVED / HYPOTHESES_NOT_MET** (explicitly preserve uncertainty).

Treat probabilities as model-conditional. For an empirical application, a separately justified observational/causal model and identification protocol is mandatory.

## 8. OpenAI Math harvest — optional external research adapters

**Pin external corpus:** `HMarcusWH/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`, [CONTENTS.md](https://github.com/HMarcusWH/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/CONTENTS.md), `lean/docs/` and `lean/ComparatorChallenges/`. The repository advertises 722 manuscripts in 372 families and different stages of verification; the original Wave 1 screened the catalogue and inspected selected families. This document does **not** independently reproduce its full catalogue-wide screen or compile external Lean solutions.

| Family | Relevant mathematical claim / selected source | Hypothesis-to-Permansson bridge | Research disposition |
|---|---|---|---|
| 104 | Mean-payoff games; solution at `lean/OAI/Computability/MeanPayoff/Main.lean` and registered randomized result `OAI.randomized_quasipolynomial_mean_payoff` in `.../RandomMean/Main.lean` | Encode finite turn-based two-player zero-sum liminf mean-payoff game, reward, strategy and objective; general stochastic/non-zero-sum GR does not automatically fit | COMPUTATIONAL BACKEND CANDIDATE |
| 131 | Degree-preserving lazy graph-switch chain mixing: `OAI.Problem315.switch_chain_main` and `switch_chain_tv_bound`, `.../SwitchChain/Main.lean` | Prove **exact kernel identification/intertwining** with this specific labeled undirected switch chain and transport invariant law | ADAPTABLE WITH NEW PROOF |
| 152 | `OAI.SmoothObstruction.main`, `.../SmoothObstruction/Main.lean`: a finite-KS-entropy ergodic invertible system with no compact smooth positive-volume model | Negative boundary on universal smooth representations, *not* a refutation of existing conditional quotient results | COUNTEREXAMPLE / VALIDATION ASSET |
| 145 | `OAI.Rokhlin.mixing_all_finite_orders`, `.../MultipleMixing/Main.lean`, claims ordinary invertible measure-preserving mixing implies all finite orders | Needs independently rebuilt extraordinary ergodic result **and** a genuinely invertible stationary mixing realization; killed or multistable kernels do not qualify | RESEARCH LEAD — EXCEPTIONAL VERIFICATION |
| 154 | Pointwise multiple ergodic averages manuscript; no matching selected `lean/docs/154.md` verified in Wave 1 | No generic passage from a mixing assumption to arbitrary finite-world regime observables; verify manuscript/proof first | RESEARCH LEAD |
| 229 | Three-state symmetric broadcast supercritical reconstruction selected formalization in `lean/docs/229.md` | Specify exactly matching tree-broadcast observation law and prove reduction; not a generic identification theorem | RESEARCH LEAD |
| 140 | Restricted-memory noiseless Gaussian regression results, `OAI.Probability.MemoryPrecision.main` | Need exact unknown signal, observation distribution, memory and success reductions | RESEARCH LEAD |
| 327 | Banach Markov-type/superreflexivity, `lean/docs/327.md` | No established implication for general Permansson kernels or quotient semantics | REJECT — INCOMPATIBLE ASSUMPTIONS for direct import |

**104 bookkeeping correction:** a deterministic theorem declaration exists in a solution source, but `lean/docs/104.md` and the current `lean/formalization.yaml` do **not** list it as the selected registered deterministic theorem in the way the first harvest implied. Source presence ≠ independently certified selected proof. Likewise some 131/145/152 solution+comparator pairs do not appear in the inspected main-result YAML catalogue. Resolve inventory discrepancies before making claims about registered formalization.

**145 verification warning:** resolving the general one-transformation Rokhlin multiple-mixing problem would be a major theorem. A comparator JSON with standard permitted axioms and an apparent proof term warrants deep audit, not automatic import or external mathematical authority.

**Import rule:** for every candidate capture exact manuscript/PDF, family, fork SHA, theorem text/hypotheses, selected comparator type, solution declaration, transitive dependencies, toolchain, fresh compilation outcome, `#print axioms` / accepted axioms, mathematical bridge lemma, countermodel and disposition. Keep these three separate: (1) a manuscript claim, (2) a source-level Lean proof term, (3) independently reproduced verification. An external result with no proved representation bridge cannot appear in a Permansson theorem statement as if its hypotheses were automatic.

## 9. Proposed research library and dependency DAG

The **eventual**, not presently created, repository layout:

```text
PermanssonLean/                   # frozen existing mathematical source
PermanssonLean.lean               # existing root imports stay unchanged
PermanssonResearch/               # future separate Lean library
  ConstitutiveQuasi/
    Definition.lean
    PathOutput.lean
    Robustness.lean
    Conditioning.lean             # optional later
    Counterexamples.lean
  GrammarRobust/
    Blocks.lean
    Semantics.lean
    Minimality.lean
    Transport.lean
    Counterexamples.lean
  MultipleLimit/
    RecurrentClasses.lean
    LimitLaws.lean
    BasinFamily.lean
    Recovery.lean
    Counterexamples.lean
  ReverseSolver/
    Target.lean
    FrozenMenu.lean
    ControlledKernel.lean
    Bellman.lean
    PolicySynthesis.lean
    ForwardVerification.lean
    Robustness.lean               # optional later
    Counterexamples.lean
PermanssonResearch.lean           # future explicit research imports
docs/PERMANSSON_RESEARCH_ARCHITECTURE.md  # this research plan
```

The current `lakefile.toml` defines `PermanssonLean` as the default library; placing files under a new directory **would not automatically build them**. On the first approved implementation PR, add a second `[[lean_lib]]` named `PermanssonResearch`; retain the default target and frozen core unchanged; explicitly run `lake build PermanssonResearch` in a new or extended CI job. Initially use the baseline `lean-toolchain` and locked `lake-manifest.json`; do not mutate the original dependency lock to import OpenAI Math `4.34.1` until a compatibility plan and proof audit have passed.

The *logical* dependencies are:
- A → existing survival + event-TV + typed constitution. No B/C/external dependency.
- D0 → existing induced kernels + typed interventions + finite hitting arithmetic. A is optional for D0's basic theorem.
- D1 → D0's targets plus controlled-kernel semantics, Bellman and policy correctness. It must not pretend D0 fixed interventions already represent adaptive policies.
- B → existing frozen-family signatures + new block semantics.
- C → existing occupation + new recurrent-class theorem.
- Advanced D → may selectively reuse A (finite certificates), B (compound admissible controls), C (limit-family objectives), and separately verified external algorithms.

No declaration should import a downstream layer for a mere convenience theorem; extract common lemmas to a low-level research module when necessary to avoid cycles. Future module naming is not an alternative source of mathematical authority.

## 10. Adversarial counterexample and acceptance matrix

| ID | Minimal mathematical model | False claim it must defeat / correct property |
|---|---|---|
| A1 | Two-state chain, survival `q^L<1` | Good finite retention ≠ exact invariance |
| A2 | Positive individual effects approaching zero along admissible states/models | Pointwise effect ≠ uniform positive margin |
| A3 | Killed chain with QSD and poorly surviving initial states | QSD alone ≠ global finite-persistence bound |
| A4 | Condition on survival probability near zero | Unconditional TV ≠ uniformly small conditional error |
| A5 | Exit exactly after transition `L` | Survival `τ_B>L` and prefix `0…L` must agree |
| A6 | Two approximations with changed world `P` | Numerical effect ≠ typed strategic constitution |
| B1 | Joint block changes output; singleton blocks do not | Singleton scan misses joint effect |
| B2 | Redundant supports/incomparable minima | Uniqueness of minimal block is false |
| B3 | Bigger block cancels effect of smaller block | Constitution is not block-monotone |
| B4 | Same baseline kernel, different intervention kernels | Baseline equivalence ≠ causal equivalence |
| B5 | Label mapping fails to preserve admissible-subblock order | Effect transport alone ≠ minimality transport |
| C1 | Two absorbing classes | One common state-independent limit need not exist |
| C2 | Branching transient state | Random limit ≠ deterministic mixture almost surely |
| C3 | Period-two irreducible class | Occupation converges although marginals oscillate |
| C4 | Infinite growing alternating residence blocks | Candidate limit set ≠ convergence theorem |
| C5 | Descriptor collapses distinct classes | State-class plurality ≠ observed-descriptor plurality |
| D1 | Target unreachable from initial state under every admissible control | Correct formal zero value / impossibility |
| D2 | A sampled search misses an admissible control | NOT_FOUND ≠ proved impossible |
| D3 | Feedback policy beats every fixed menu intervention | D0 optimality ≠ D1 optimality |
| D4 | Forbidden region encountered before target | Strict target-before-danger event respected |
| D5 | Overlapping controls or modified world primitive | Invalid policy rejected by grammar |
| D6 | Two uncertain kernels with different optimal controls | `sup inf` and `inf sup` not conflated |
| D7 | Reaching target then immediately exiting | Reachability ≠ reach-and-stay |

Formal negative statements should be represented as Lean propositions where feasible, not exclusively comments. Small finite-state dynamic-programming examples should also be **exhaustively enumerated computationally**, comparing Bellman values against all eligible policies (with explicit numerical tolerance only if floating arithmetic is used). These tests are falsification/regression, not a general proof. Reuse the existing period-two example as a regression control rather than counting it as new mathematics.

## 11. Verification, provenance and evidence discipline

The repo already distinguishes (1) Lean proof; (2) destructive/regression runs; (3) release/integrity gates; and additionally (4) application contract validation. Preserve this separation in all future PRs.

**Mathematical release gate:** precise theorem statement and scope; transitive imports reviewed; `lake build PermanssonResearch` green on pinned dependencies; no `sorry`, `admit` or unexplained custom `axiom`; audit `#print axioms` / comparator assumptions on new high-level declarations; positive and adversarial examples; existing core build and original tests unchanged; statement-to-paper and statement-to-Lean crosswalk. Compilation establishes the encoded statement under its actual assumptions, not the validity of an empirical model.

**Numerical gate:** reproducible seeds/parameter ranges, exact frozen policy/model set, explicit objective, disjoint selection versus holdout data where used, documented approximation/rounding error, and refusal to replace a sampled minimum with a proved universal bound. Report simulation counts as correlated comparisons if draws are shared.

**Empirical gate:** state-observation map, fitted/identified kernel and uncertainty set, provenance, support, selection, measurement/coverage and causal assumptions; do not turn exploratory coefficients into real-world control recommendations. Preserve separate epistemic and statistical status in any future application contract extension.

**OpenAI import gate:** verified upstream theorem type+axioms, independent compatible rebuild, exact Permansson bridge and adversarial test. A paper with a novel claim but no rebuilt proof remains research, not a transitive dependency.

**Release gate:** new version boundary and theorem ledger; protected v0.1.8 hashes and historical PASS results unchanged. No user-facing new GR/PR certificate semantics until the separate release and reporting format are approved.

## 12. Implementation milestones and individual PR contracts

**PR 0 — Documentation only (this proposal).** Add this master specification; link it from `docs/FUTURE_THEORY_ROADMAP.md` and `docs/README.md`. No Lean, toolchain, `lakefile`, application-schema, CI or frozen evidence changes. Review the claims and acceptance criteria before any theory implementation.

**PR 1 — Research library scaffold, after authorization.** Register `PermanssonResearch` as a separately compiled library; ensure baseline `lake build` and research-target build succeed without stubs masquerading as proofs; add separate CI/axiom checks.

**PR 2 — A definition and prefix property.** Formalize finite path property, measurable evaluator, shared horizon, bounded expectation-TV lemma, and the typed certificate interface. No robustness "proof by declaration".

**PR 3 — A robustness and countermodels.** Prove survival/error and margin/error composition; verify approximate strategic pair preserves `P`; examples and negative tests. Research gate for CQ-1.

**PR 4 — D0 finite frozen menu.** Freeze target/forbidden/horizon and finite admissible intervention menu; prove exact forward hitting probability and optimum over that menu. No adaptive policy claims.

**PR 5 — D1 controlled process.** Build nonstationary finite controlled path law using state-feedback action selection, keeping `P,U` fixed, plus frozen-replacement agreement lemma.

**PR 6 — D1 Bellman/argmax/forward verification.** Prove recurrence, extract policy, compare certified value with law, exhaustive small-model regressions. No constrained/robust optimality claim.

**PR 7+ — B blocks then grammar transport.** Build admissible block semantics before minimality/transport theorem; counterexamples before generalizing.

**PR 8+ — C finite recurrent classes then recovery.** Prove class decomposition and pathwise limiting law; distinguish mixture semantics, then conservative original GR recovery.

**Subsequent optional PRs:** A-conditioned probabilities; reach-and-stay; robust uncertainty; finite-game backend; validated external ergodic results; versioned application contract. These must be separately proposed and reviewed.

PR numbers are illustrative ordering, not a promise that GitHub PR sequence identifiers will match. Keep each PR scoped to one nontrivial proof obligation plus necessary definitions and regression tests; do not merge a partial abstraction just because the build is green.

## 13. Review gate, open decisions and autonomous-agent handoff

Before coding each milestone, an agent must:
1. Re-read current GitHub default-branch HEAD **and** the immutable baseline; do not assume this doc's design-time `main` hash remains current.
2. Read the complete `FORMALIZATION_MAP`, `THEOREM_CROSSWALK`, relevant source theorem signatures and this plan. Distinguish preexisting statements from proposed proofs.
3. Present the *exact* selected theorem statement with variable types, measurability/topological hypotheses, quantified states/model families, intervention typing and explicit countermodels.
4. Check whether that statement already follows from existing Lean declarations and name the missing bridge lemma. Do not rewrite the completed theorem to make it look novel.
5. Flag any unmade policy choice as an explicit review blocker. In particular: finite-path property class, globally uniform versus reachable-state TV, allowed simultaneous block targets, information available to controller, uncertain-model quantifier order, and whether a regime objective is reachability or reach-and-stay.
6. Once authorized, implement only the approved PR slice in the separate research library, run build and axiom checks, inspect counterexample outcomes and baseline regressions, then report exact changed declarations and limitations.
7. **Never infer** empirical validity, a universal causal intervention, optimum across an undeclared class, or historical preregistration from a mathematical/software PASS.
8. Update the research ledger after a reviewed proof; do not turn this document's "proposed" text into "PROVED" ahead of that review.

### Blocking design choices, with recommended first-release defaults

| Choice | Initial default | When to revisit |
|---|---|---|
| CQ-1 survival domain | Entire frozen `B` | Explicitly named `B₁` diagnostic only |
| CQ-1 property | Measurable `[0,1]` finite-prefix observable | Metric-valued bounded-Lipschitz later |
| CQ-1 approximation | Same initial point, uniform event-TV on all `Y` | Separate initial-law or local-reachability theorem |
| B block conflicts | Disjoint targets and jointly specified replacements | Formal overlap algebra later |
| C scope | Finite stationary Markov systems | General state spaces only with recurrence/measurability theorems |
| D0 policies | One intervention held through full horizon | D1 feedback policies |
| D1 controls | Fully observed, finite, action-selection replacements only | Update/block/POMDP later |
| D1 objective | Hit target before forbidden within `T` | Stay, risk budgets, robust game later |
| External Math | No imported theorem | Verified independent rebuild + proved bridge |
| Application interface | No schema/status change | Separately versioned release after proof |

### Completion meaning

The programme is **not complete** when four folders exist or all computational tests pass. It is complete, at the scope of each independently promoted research lane, only when definitions and quantifiers are fixed, theorem obligations are discharged by Lean under audited assumptions, counterexamples defeat unjustified stronger claims, algorithm outputs have proofs tied to their actual controlled kernel, and a new release snapshot/claim ledger preserves the v0.1.8 boundary.

**Immediate approved scope of this documentation PR:** the detailed plan and navigation changes only. **Next theory-implementation decision:** independently review and explicitly authorize CQ-1's final Lean theorem signatures, including the distinction between regional survival and the comparison-basin constitutive effect.
