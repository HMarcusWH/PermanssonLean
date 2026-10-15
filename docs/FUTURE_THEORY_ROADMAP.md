# Future Permansson theory roadmap

**RESEARCH / NOT PART OF THE FROZEN v0.1.8 RELEASE.**  
**Current planning checkpoint:** 15 October 2026; main@d137ac2308285f843a1ccf76fede74b4b6b65131, following merged C11-A and the DOC-0 v0.2.0 specification. This is a **date- and commit-scoped status**, not a live CI dashboard.  
**Complete mathematical specification:** [PERMANSSON_V020_MATHEMATICAL_INTEGRATION_SPEC.md](PERMANSSON_V020_MATHEMATICAL_INTEGRATION_SPEC.md) — hypotheses, all equations, proof skeletons, exact-countermodel tests, Lean module names and manuscript wiring.  
**Detailed original A/B/C/D architecture:** [PERMANSSON_RESEARCH_ARCHITECTURE.md](PERMANSSON_RESEARCH_ARCHITECTURE.md). **Actual research-build evidence:** [RESEARCH_BUILD.md](RESEARCH_BUILD.md).

## Current implementation inventory — do not re-build existing theorems

| Lane | State at this checkpoint | Formal provenance / limits |
|---|---|---|
| Original v0.1.8 | **Frozen, historical proof snapshot** | c018f79ea4ce46f4f679ad5bca254509778fc53c; discrete GR/PR core through Prop. 8.1, not empirical certification |
| A / CQ-1 | **Merged research**, PRs #36–38 | finite bounded-path and approximation certificates, no automatic Exact GR |
| B / grammar robustness | **Merged research**, PR #51 | joint-only constitutive PR witness, OR/AND/XOR and admissible block grammar/minimality already implemented |
| C / multiple limits | **C1–C11-A merged**, PRs #52–62 | recurrent-class occupations, typed Exact GR, eventual events, rational absorption, certified class stationarity; specialized finite chain scope and conditional receipt semantics |
| C11-A | **Merged**, PR #62 | exact rational stationary class certificates on the typed finite subclass; not a universal solver, Exact GR/PR promotion or independent peer review |
| D / reverse solver | **Merged research**, PRs #39–50 | finite menus, controlled kernels, Bellman, rational nonstationary/history-sensitive policies; optimum in specified class |
| E / approximate typed quotients | **PROPOSED** | exact quotient theorem exists, quantitative defect-to-margin transport does not yet exist |
| F / multi-agent protocols | **PROPOSED** | typed intervention primitives exist, opponent CL/OL semantics are not yet formalized |
| X / flagship application | **PROPOSED** | finite game-theoretic MPE-versus-learning witness still needs construction and certification |

**Source of truth for changing status:** live PR, exact source HEAD and synthetic merge, primary Lean declarations, CI and axiom audit. Old A–D sections below intentionally preserve the historical proposals, so their “work to do” language is not a claim that merged PRs remain unimplemented.

## Version boundary

Retain the original PermanssonLean library, v0.1.8 paper and release hashes unchanged. Add future proofs only to the separate, explicitly built PermanssonResearch library; use a new versioned TeX and verification manifest for v0.2.0. This document is a *programme*, not a declaration that all future theorems are already proved.

## A. Constitutive quasi-regimes

Starting point: v0.1.8 Sections 4.2-4.4 already define killed-kernel finite
persistence and optional QSD certification; Section 5 separately defines strategic
constitution. A finite-horizon constitutive certificate could combine these without
weakening the definition of Exact PR.

Work to do: freeze the horizon, survival requirement, descriptor/property, basin
and intervention; define a subordinate finite-horizon class; prove the exact
hypothesis-to-certificate implications; carry property-output error budgets and
support/identification uncertainty through the finite comparison. Keep a QSD
certificate independent of the statewise finite-survival requirement.

Acceptance tests: positive examples, leaky/zero-margin counterexamples, off-by-one
exit tests, adversarial QSD examples, and a direct theorem/Lean interface. Do not
rename a finite-survival result `ROBUST_PR` under the existing application schema.

## B. Grammar-robust constitution

Starting point: Section 5.4 says component attribution is grammar-relative. Compound
blocks may matter when singleton interventions do not. A change in coordinates is
not automatically a matched substantive intervention.

Work to do: specify a frozen family of admissible component decompositions and
semantic transport maps; distinguish minimal constitutive blocks, joint necessity,
substitutability and invariance across matched grammars. Determine which statements
require closure assumptions; do not assume a unique minimal grammar or monotonicity
of constitutive effects under aggregation.

Acceptance tests: synergistic and redundant components, incomparable minimal sets,
reparameterization counterexamples, hard target-closure failures, and a preservation
theorem with explicit hypotheses. Existing intervention-family equivalence is a
starting substrate, not an already-proved grammar-lattice theorem.

## C. Multiple-limit / regime-family semantics

Starting point: Definition 4.3 requires one declared limiting occupation law across
the admissible basin. A future regime-family object might permit initial-state-
dependent limiting laws or an ex ante set of admissible limits.

Work to do: distinguish convergence to a set, convergence to a random law, and
state-indexed deterministic limits; specify topology, measurability, initial-law
quantifiers and intervention transport; prove conservative recovery when the limit
family is a singleton. A large post-hoc set containing every observed outcome is
not a substantive classification.

Acceptance tests: multistability, mixtures of recurrent classes, nonconvergent
occupation sequences and overbroad limit sets; then a direct GR/PR transfer result
and a versioned application contract. Do not silently replace nu in v0.1.8.

## D. Reverse Regime Solver

Starting point: typed strategic interventions and induced Markov kernels are already
formalized, but backward reachability, control-policy synthesis and policy-value
certification are new theory. See the [master architecture](PERMANSSON_RESEARCH_ARCHITECTURE.md#7-lane-d--reverse-regime-solver-synthesis-plus-verification).

Work to do: first evaluate a finite frozen menu of existing admissible strategic
interventions (D0). Then define a separate finite, fully observed controlled
process for state-dependent action-selection policies, with the world primitive
and strategic update held fixed (D1). Prove backward Bellman values, extract an
admissible maximizing policy, and verify its forward path law. Later extend only
under explicit assumptions to reach-and-stay, risk constraints, robust model sets,
block interventions and multiple-limit targets.

Acceptance tests: impossible targets, sampling false negatives, adaptive-vs-fixed
policy differences, forbidden-region precedence, held-world violations, horizon
boundaries and uncertainty-quantifier counterexamples. A numerical NOT_FOUND is
not a theorem of impossibility, and a mathematical optimum is only for the
specified model and policy class.

## v0.2.0 mathematical integration — exact obligations and status

Every formula in this section is **PROPOSED**, unless the stated legacy declaration is named as EXISTING. The corresponding complete theorem statements, proofs/countermodels, Lean targets and assumptions are in the [v0.2.0 Mathematical Integration Contract](PERMANSSON_V020_MATHEMATICAL_INTEGRATION_SPEC.md). Existing v0.1.8 notations and quantified gates remain unchanged.

**Implementation tracking (15 October 2026):** A2's additive primitive TV, factor-one bounded score and generic metric-valued L-Lipschitz source are implemented in
[draft PR #64](https://github.com/HMarcusWH/PermanssonLean/pull/64), alongside 16 exact-rational adversaries and full finite-persistence certificate transport. [Proof ledger](V020_RESEARCH_PROOF_LEDGER.md). Source and
test commits are not proof release evidence; promote only after the exact-head
Lean and independent review gates. C11-A PR #62 has merged since this
roadmap's historical baseline.

### A2 — Typed primitive-kernel error to finite constitutive margin

For the canonical $\alpha\to P\to U$ kernel, given global one-step event-TV bounds $\delta_\alpha,\delta_P,\delta_U\in[0,1]$ on all relevant kernel rows, require the **additive** primitive error theorem

$$
\sup_y\|K(y,\cdot)-\widetilde K(y,\cdot)\|_{\mathrm{TV}}
\le\delta_K:=\min\{1,\delta_\alpha+\delta_P+\delta_U\}.
$$

The sharper bound $1-(1-\delta_\alpha)(1-\delta_P)(1-\delta_U)$ requires its own measurable sequential coupling/common-overlap proof, not just three additive telescoping terms. For each baseline/intervention label $\ell\in\{0,J\}$, independently budget $\delta_{K,\ell}$. Under a frozen $T$-prefix, $L_\psi$-TV-Lipschitz property,

$$
|\widetilde\kappa_{\psi,J}(B_1)-\kappa_{\psi,J}(B_1)|
\le L_\psi\sum_{\ell\in\{0,J\}}\left[1-(1-\delta_{K,\ell})^T\right]
\le L_\psi T(\delta_{K,0}+\delta_{K,J}).
$$

Reuses **existing** Proposition 5.4 and CQ-1. Positive finite-horizon margin does not by itself certify Exact GR/PR. Keep property-evaluation, initial-law, model-set and causal-identification budgets separate.

### A3 — Infinite-horizon closure for a contractive subclass

Under invariant laws $\pi_\ell,\widetilde\pi_\ell$, common metric, finite first moments, uniform $W_1$ contraction factor $\rho_\ell<1$ for $K_\ell$, and one-step Wasserstein defect $\delta_\ell$,

$$
W_1(\pi_\ell,\widetilde\pi_\ell)\le\frac{\delta_\ell}{1-\rho_\ell}.
$$

If $\psi$ genuinely factors through an $L_h$-Lipschitz descriptor and an $L_F$-Lipschitz functional of the deterministic limiting occupation law, the target certificate is

$$
|\widetilde\kappa-\kappa|
\le L_F L_h\!\left(\frac{\delta_0}{1-\rho_0}+
                         \frac{\delta_J}{1-\rho_J}\right).
$$

This **does not** cover discontinuous indefinite survival indicators: an arbitrarily small positive leakage can break exact invariance. Establish existence/uniqueness/ergodic property identification separately. A2 is not a replacement for A3.

### B2 — Four-corner strategic-generator interaction

**Implementation (PR #65, draft):** [B2 theorem and adversarial ledger](LANE_B2_SEQUENTIAL_EFFECTS.md). The branch formalizes three *separately admitted* interventions, physical α/U atom compatibility rather than a downward-closure assumption, the original B₁ margin bridge, and a genuine two-time zero-infimum counterexample. This is in research only and does not alter the frozen v0.1.8 paper/core. Exact-head compilation and CI remain the promotion gate.


Freeze $z_{00},z_{10},z_{01},z_{11}$ for baseline, action-only, update-only and joint $(\alpha,U)$ interventions, with fixed $P$ and the same property map. Set

$$
\Delta_\alpha=d(z_{00},z_{10}),\quad
\Delta_U=d(z_{00},z_{01}),\quad
\Delta_{\alpha U}=d(z_{00},z_{11}),\quad
\Delta_{U\mid\alpha}=d(z_{10},z_{11}).
$$

The valid *sequential* triangle is

$$
|\Delta_\alpha-\Delta_{U\mid\alpha}|
\le\Delta_{\alpha U}\le\Delta_\alpha+\Delta_{U\mid\alpha},
$$

and analogously for $U$ first. If $\kappa_{\alpha U}>0$ and singleton effects are **pointwise zero on all $B_1$**, conditional singleton margins equal $\kappa_{\alpha U}$. **Do not infer singleton-null from a zero infimum**, nor claim the false direct subadditivity $\Delta_{\alpha U}\le\Delta_\alpha+\Delta_U$.

For normed vector outputs, add $I_{\alpha U}=z_{11}-z_{10}-z_{01}+z_{00}$. Preserve finite inclusion-minimal constitutive blocks and grammar-order conditions. **Existing Lane B already proves joint-only original PR constitution**, so only the genuinely missing sequential quantitative calculus is new.

### C-Exit — Sub-Markov destination and constitutive switching

**Live implementation overlay (PR #66, draft):** [C-Exit research ledger](LANE_C_EXIT_ROUTING.md) documents actual first-exit path-law events, finite/infinite destination submeasures and QSD routing in separate research modules. Its generic Lean proofs and typed adversaries are not accepted until exact-head and synthetic-merge CI pass. Typed intervention-driven switching and random-entry occupation convergence stay in PR #67.

For $y\in B$, $K_B(y,C)=K(y,C\cap B)$, and $\tau_B=\inf\{t\ge0:Y_t\notin B\}$, define

$$
E_B(y,D)=K(y,D\setminus B),\qquad
R_B^{(L)}(y,D)=\sum_{n=0}^{L-1}(K_B^nE_B(\cdot,D))(y).
$$

Prove **exact** first exit routing and mass conservation,

$$
P_y(\tau_B\le L,Y_{\tau_B}\in D)=R_B^{(L)}(y,D),\qquad
R_B^{(L)}(y,Y\setminus B)+(K_B^L{\bf1}_B)(y)=1.
$$

The infinite routing sum is a subprobability measure. For a strategically intervened Exact GR $R'$ whose basin $B'_0$ lies outside $B$, the condition $R_B^{J,(\infty)}(y,B'_0)\ge1-\eta$ proves probabilistic first-exit entry; retaining the target requires **separate post-intervention Exact-GR invariance**. With $\psi_B(P_y)=P_y(\tau_B=\infty)$, baseline Exact GR and that routing condition give $\kappa_{\psi_B,J}(B_1)\ge1-\eta$, subject to typed intervention and grounding gates.

Under a QSD eigenmeasure $\mu_BK_B=\theta_B\mu_B$ with $0<\theta_B<1$, prove the destination probability $\mu_B(Q_r)/(1-\theta_B)$, $Q_r(y)=K(y,B^{(r)}\setminus B)$. Exclude the $\theta_B=1$ denominator case.

### D2 — Reverse-solver regime-switching objectives

Extend D only *after* C-Exit supplies mathematical target semantics. A finite hit event is **not** a stay or an Exact GR certificate. Freeze distinct objectives for $P(\tau_{B'_0}\le T,\tau_{B'_0}<\tau_D)$, finite post-entry residence for a declared duration, and almost-sure/thresholded eventual switching. A robust objective must specify $\sup_\pi\inf_K$ versus $\inf_K\sup_\pi$, observation structure and rectangularity before Bellman reasoning. D0/D1 already prove narrower finite objectives: reuse rather than overclaim.

### E1 — Approximate type-respecting frozen-family quotients

For a surjective type-respecting $q=q_S\times q_X$ and frozen matching $\phi$, preserve every semantic factorization/initial-law-lift requirement of Theorem 7.4b except exact intertwining. Define, for each label $\ell$,

$$
\eta_\ell=\sup_y\|q_\#K^\ell(y,\cdot)-\bar K^{\phi(\ell)}(q(y),\cdot)\|_{\mathrm{TV}}.
$$

Even though $q(Y_t)$ need not be Markov, analytic finite-horizon hybrid integration gives

$$
\|(q^{0:T})_\#P_y^{K^\ell,0:T}
      -P_{q(y)}^{\bar K^{\phi(\ell)},0:T}\|_{\mathrm{TV}}
\le\min\{1,T\eta_\ell\}.
$$

With factorized $T$-prefix $L_\psi$-Lipschitz properties and surjective comparison set, obtain

$$
|\kappa_{\psi,J}(B_1)-\bar\kappa_{\bar\psi,\phi(J)}(\bar B_1)|
\le L_\psi T(\eta_0+\eta_J).
$$

A sharper $1-(1-\eta_\ell)^T$ path estimate needs an independently proved common-overlap measure construction. **A positive quotient margin is not itself a certificate for Exact GR**, which may fail under arbitrarily small leakage; never claim preservation of complete PR status unless both Exact-GR gates hold.

### F1 — Explicit multi-agent adaptation protocols

On the conditional-product subclass $S=S_0\times\prod_iS_i$, $A=\prod_iA_i$, freeze player-specific $\alpha_i,U_i$ and common $P$. Define $J_{i,\mathrm{CL}}$ (replace player $i$, leave functional opponent kernels intact) and $J_{i,\mathrm{OL}}$ (also impose a declared opponent nonreactive anchor on all intervention-reachable rows). For output points $z_0,z_{\mathrm{CL}},z_{\mathrm{OL}}$, prove

$$
|\Delta_{\mathrm{CL}}-\Delta_{\mathrm{OL}}|
\le d_\psi(z_{\mathrm{CL}},z_{\mathrm{OL}})
\le \Delta_{\mathrm{CL}}+\Delta_{\mathrm{OL}}.
$$

This is a protocol-comparison metric, **not automatically identified causal mediation**. A baseline-support-matching frozen anchor need not be unique off support. Models with genuinely correlated moves need an explicit shared-variable representation or a different nonproduct subclass.

### X1 — Flagship MPE versus learning in one economic world

Freeze the same *actual* world $P(dx'\mid x,a)$, payoffs $r_i$, discount $\beta_i$, typed relevance map, and common substantive criteria. Produce both a certified equilibrium $\pi^*$ satisfying Bellman equalities and all unilateral incentive inequalities and a finite Markov-sufficient non-equilibrium learner $(\alpha^{\mathrm{learn}},U^{\mathrm{learn}})$.

For finite state/action sets, certify

$$
V_i(x)=\sum_a\pi^*(a\mid x)\big[r_i(x,a)+\beta_i\sum_{x'}P(x'\mid x,a)V_i(x')\big],
$$

$$
V_i(x)\ge\sum_{a_{-i}}\pi^*_{-i}(a_{-i}\mid x)
\big[r_i(x,a_i,a_{-i})+\beta_i\sum_{x'}P(x'\mid x,a_i,a_{-i})V_i(x')\big]
\quad(\forall i,x,a_i).
$$

Then compute the killed-survival vector, action/update/joint constitutive margins, occupation and nine **categorical** certificate dimensions for both. A shared $\Sigma=(B,B_0,h,\nu,\mathfrak c)$ is valid for both generators only if both genuinely attain the same $\nu$; otherwise keep the substantive criteria fixed and declare distinct occupation targets.

### Editorial and formal-release carry-forward

Carry two non-breaking specification clarifications into a **new** TeX: off-graph measurable extension for $U$, and substantively justified/frozen $h|_{Y\setminus B}$ for post-exit properties. Fix the observed math-mode $\psi$/outcome and $(L,\eta)$-quasi markup, theorem-header/proof styling, loose symbols and Tables 3–4 captions with correct multipage layout. Do **not** modify v0.1.8's hash-verified PDF/TeX or its release evidence.

### Formal falsification and sequence

The full [adversarial table](PERMANSSON_V020_MATHEMATICAL_INTEGRATION_SPEC.md#11-new-destructive-test-ledger) covers ER1–6, PT1–4, SY1–4, MA1–3, AQ1–5 and EG1–3. Require exact positive and negative witnesses, final-head + synthetic-merge Lean builds, proof axiom/placeholder audit, old-core CI and separate application contract validation.

**Docs-only first; then A2, B2, C-Exit, E1, F1, A3, flagship X1 and a new paper/release gate.** Sharp optional estimates and stronger D objectives get separately tracked work items. No code or empirical statuses are promoted merely by adding this roadmap.

## Promotion rule

Each lane needs a stable definition, explicit scope, proof and counterexamples,
executable tests, paper-to-Lean crosswalk, and its own version/release boundary.
Until those exist, no stubs or assumed theorems are added to `PermanssonLean/`.
The application standard only records existing theory; it does not implement these
research lanes by issuing stronger labels.
