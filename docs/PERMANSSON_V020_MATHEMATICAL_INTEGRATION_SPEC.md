# Permansson v0.2.0 — Mathematical Integration and Adversarial Verification Contract

**Status:** proposed *research specification*, **not** a compiled v0.2.0 theorem release.  
**Prepared:** 15 October 2026. **Baseline:** main at 57aa4eb3b58df770630f16b04940cb5933317709.  
**Historical mathematical snapshot:** c018f79ea4ce46f4f679ad5bca254509778fc53c (v0.1.8; Lean 4.34.0 and pinned mathlib).  
**Scope:** documentation-only integration contract for Permansson Regimes and the separate PermanssonResearch library. It does not authorize changing the historical source, formal core, existing proof declarations, application certificate schema, or active C11-A work.

This document carries the **complete intended mathematics, hypotheses, proof obligations, known countermodels, Lean interfaces, and paper wiring** for the proposed v0.2.0 upgrades. It is an implementation specification, not a claim that the proposed statements have been mechanically checked. Before implementing any item, compare its precise Lean formulation with current source and prove it *without silently changing quantifiers or assumptions*.

## 0. Ground truth and source hierarchy

1. The [final v0.1.8 manuscript](../paper/Permansson_Regimes_Strategic_Dynamics_Beyond_Equilibrium_v0.1.8_SUBMISSION_FINAL_EDITORIAL_CLEAN_2026-09-23.pdf) and [frozen formalization map](FORMALIZATION_MAP.md) define the baseline semantics. Historical CI is scoped to **the encoded mathematical core through Proposition 8.1**, not empirical identification or every specialized result.
2. The separate [research build ledger](RESEARCH_BUILD.md) and actual implementation are current-state evidence; the 8 October [architecture](PERMANSSON_RESEARCH_ARCHITECTURE.md) is a historical research proposal and must not supersede compiled subsequent work.
3. A/B/C/D are preexisting research lanes. A1/CQ-1 (PRs #36–38), finite Lane B (PR #51), C1–C10 (PRs #52–61), and D0/D1 (PRs #39–50) were merged by the specified baseline. **C11-A (PR #62) is separately in progress**, and is not certified or incorporated into this plan as a completed theorem.
4. A theorem cited from existing code is marked **EXISTING** only for its actually encoded statement; a new generalization is **PROPOSED** until a final-head Lean proof, adversarial tests, axiom audit, and paper crosswalk exist. Passing regression tests alone does not certify a universal statement.
5. Source links, declaration identifiers, release commits, and explicit nonclaims are integral to the implementation contract. No status is promoted merely because this document contains a proof sketch.

### 0.1 Existing reusable primitives (do not duplicate)

| Existing source | Proven or represented substrate | Correct interpretation |
|---|---|---|
| PermanssonLean/Regime/SurvivalBridge.lean | survivalProbability_eq_killedSurvivalMass | exact killed survival, not yet arbitrary exit destinations |
| PermanssonLean/Regime/ExitTimeExpectation.lean | expectedExitTime_eq_greenSeries | expected exit time, not distribution of first exit location |
| PermanssonLean/Regime/QuasiStationary.lean | IsQSDCertifiedQuasiRegime; proposition_4_4b | QSD conditional stationarity; no automatic existence/uniqueness |
| PermanssonLean/Probability/FinitePrefixTV.lean | proposition_5_4; geometricTVEnvelope; commonFinitePrefixLaw | full finite-prefix event-TV bound |
| PermanssonLean/Regime/Perturbation.lean | constitutiveMargin_perturbation_abs_le | property-space bridge only; no primitive-error theorem |
| PermanssonLean/Quotient/Preservation.lean | quotient_frozenFamilyPR_iff | **exact** intervention-compatible quotient preservation |
| PermanssonResearch/ConstitutiveQuasi/ | finite certificates, TV and output-error budgets, typed certificate transport | finite subordinate certificate, not Exact PR |
| PermanssonResearch/GrammarRobust/ | typed finite blocks, original path-law margins, refinement, OR/AND/XOR, minimum blocks | **joint-only constitution and original PR witness already exist** |
| PermanssonResearch/MultipleLimit/ | recurrent classes, random occupation laws, Exact GR, hitting/absorption | finite homogeneous chain subclass and typed examples |
| PermanssonResearch/ReverseSolver/ | finite menu, Bellman, typed nonstationary controls, rational absorption and margins | optimum over **declared** policy/menu class, not arbitrary real-world control |

Do not claim the existing Lean proofs entail the new proposed general theorems without an explicit bridge.

## 1. Shared typed model and certification conventions

Let nonempty Polish strategic and world spaces be $(S,\mathcal B(S))$ and $(X,\mathcal B(X))$, let the nonempty action space $(A,\mathcal A)$ be standard Borel, and let $Y=S\times X$. A feasible measurable correspondence $A(y)\subseteq A$ is nonempty. The canonical model is

$$
\mathfrak G=(\alpha,U), \qquad
Y_t=(S_t,X_t)\xrightarrow{\alpha}A_t\xrightarrow{P}X_{t+1}\xrightarrow{U}S_{t+1}
$$

with $\alpha(A(y)\mid y)=1$ and a world kernel $P(dx'\mid y,a)$ and strategic-update kernel $U(ds'\mid y,a,x')$. The Markov kernel on $Y$ is

$$
K_{\mathfrak G,P}(E\mid s,x)
=\int_A\int_X\int_S {\bf1}_E(s',x')\,
U(ds'\mid s,x,a,x')P(dx'\mid s,x,a)\alpha(da\mid s,x).
\tag{V20.1}
$$

If $P$ or $U$ is initially defined only on the feasible Borel graph, specify a measurable off-graph extension using fixed probability laws on nonempty $X$ or $S$, respectively. Only feasible rows affect $K$ under the support condition. Any intervention that changes feasibility must declare a new admissible behavior rule.

Keep the ex-ante regime object $\Sigma=(B,B_0,h,\nu,\mathfrak c)$, $B_0\subseteq B\subseteq Y$, and full-state descriptor $h:Y\to H$. For an Exact GR, require **exact invariance on every $y\in B$** and convergence to the specified **single deterministic** occupation target $\nu$ for *every* admissible initial law on $B_0$, plus Assumption 4.1 and the appropriate confirmatory nondegeneracy and relevance rules. For any constitutive property $\psi:\Delta(Y^{\mathbb N_0})\to (Z_\psi,d_\psi)$, frozen comparison set $B_1\subseteq B_0$, and typed intervention $J$, use

$$
\Delta_{\psi,J}(y)
=d_\psi\!\left(\psi(P_y^K),\psi(P_y^{K^J})\right),
\qquad
\kappa_{\psi,J}(B_1)=\inf_{y\in B_1}\Delta_{\psi,J}(y).
\tag{V20.2}
$$

**Important:** $\kappa=0$ does not mean $\Delta(y)=0$ for all $y$, and finite-horizon positivity or a positive perturbation margin does not imply Exact GR. When $B_1$ is nonempty, universally null effects mean $\sup_{y\in B_1}\Delta(y)=0$ (or pointwise zero), not merely zero infimum. Quantifiers over $B$, $B_0$, $B_1$, model uncertainty and the intervention family must never be silently exchanged.

Use the paper's event-supremum TV convention $\|\mu-\nu\|_{\mathrm{TV}}=\sup_{E}|\mu(E)-\nu(E)|$. A horizon $T$ counts **$T$ transitions**, with prefix $Y_0,\ldots,Y_T$. Occupation averages use $t=0,\ldots,T-1$. Full path properties and finite-prefix properties remain distinct; $d_{\mathrm{BL}}$ is the bounded-Lipschitz metric of the frozen descriptor convention.

## 2. Module C-Exit: exact sub-Markov exit routing and regime switching

**Proposed paper location:** immediately after Corollary 4.2c, with the strategic-constitutive corollary in Section 5.4.  
**Reuse:** Theorem 4.2a, the killed kernel, finite stopping/hitting and C-lane class-absorption mathematics.

### 2.1 Definitions (proposed Definition 4.2d)

Let $B\in\mathcal B(Y)$ and $y\in B$. Define the first exit time and killed kernel

$$
\tau_B=\inf\{t\geq0:Y_t\notin B\},\qquad
K_B(y,C)=K(y,C\cap B).
\tag{V20.3}
$$

The **one-step exit subkernel** (on $B$, supported outside $B$) and its finite/infinite destination-routing operators are

$$
E_B(y,D)=K(y,D\setminus B),
\qquad
R_B^{(L)}(y,D)=\sum_{n=0}^{L-1}
 \bigl(K_B^{n} E_B(\cdot,D)\bigr)(y),
\qquad
R_B^{(\infty)}(y,D)=\sum_{n=0}^{\infty}
 \bigl(K_B^{n} E_B(\cdot,D)\bigr)(y).
\tag{V20.4}
$$

Here $L\in\mathbb N$ counts transitions; $R_B^{(0)}=0$ by empty-sum convention. The infinite operator is **subprobability**; missing mass is the probability of never exiting. If target regions $B^{(r)}\subseteq Y\setminus B$ are pairwise disjoint, each $R_B^{(L)}(y,B^{(r)})$ is a first-exit destination probability; the sum over targets need not exhaust all exits.

### 2.2 Exit-routing theorem (proposed Theorem 4.2e)

For every measurable destination $D$, $L\ge1$, and $y\in B$,

$$
\begin{aligned}
P_y^K(\tau_B\le L,\;Y_{\tau_B}\in D)&=R_B^{(L)}(y,D),\\
P_y^K(\tau_B<\infty,\;Y_{\tau_B}\in D)&=R_B^{(\infty)}(y,D),\\
R_B^{(L)}(y,Y\setminus B)+(K_B^L{\bf1}_B)(y)&=1,\\
R_B^{(\infty)}(y,Y\setminus B)+P_y^K(\tau_B=\infty)&=1.
\end{aligned}
\tag{V20.5}
$$

**Proof obligations:** From $y\in B$, $\tau_B\ge1$. For $n\ge0$, $\{\tau_B=n+1,Y_{\tau_B}\in D\}$ is the event of $n$ transitions staying in $B$ followed by a transition into $D\setminus B$, with probability $(K_B^nE_B(\cdot,D))(y)$. Sum disjoint events over $n<L$ or $n\ge0$. Since $E_B(\cdot,Y\setminus B)={\bf1}_B-K_B{\bf1}_B$ on $B$, the finite sum telescopes:

$$
\sum_{n=0}^{L-1}
\left[(K_B^n{\bf1}_B)(y)-(K_B^{n+1}{\bf1}_B)(y)\right]
=1-(K_B^L{\bf1}_B)(y).
\tag{V20.6}
$$

Pass to the infinite limit using monotone convergence and Theorem 4.2a. Define $Y_{\tau_B}$ only on the event $\tau_B<\infty$ (or use a clearly specified measurable cemetery extension), avoiding evaluation at $\infty$.

### 2.3 Intervention-driven switching (proposed Proposition 4.2f)

Let $R=(\mathfrak G,P,B,B_0,h,\nu,\mathfrak c)$ be an Exact GR. Freeze an admissible $J$ with $K^J=K_{J(\mathfrak G),P}$. Assume $R'=(J(\mathfrak G),P,B',B'_0,h',\nu',\mathfrak c')$ is **independently an Exact GR for the post-intervention kernel**, where $B'_0\subseteq B'\subseteq Y\setminus B$. Suppose

$$
\inf_{y\in B_1}R_B^{J,(\infty)}(y,B'_0)\ge 1-\eta,
\qquad 0\le\eta\le1.
\tag{V20.7}
$$

Then, from each $y\in B_1$, the event of finite first exit into $B'_0$ has probability at least $1-\eta$. On that event, the strong Markov property and Exact-GR invariance imply retention in $B'$ afterward and the target regime's declared occupation convergence (for almost-sure or in-probability weak convergence, with an explicit random-entry argument). When $\eta=0$, all these hold almost surely. In a.s. convergence, deletion of a finite, randomly long initial prefix is harmless; for $T>\tau_B$ a normalized bounded-Lipschitz comparison can be bounded by $2\tau_B/T$ using the same descriptor $h'$ defined globally. For convergence in probability, integrate the conditional convergence probabilities against the hitting distribution, using bounded convergence; do not simply identify conditional point-started convergence with unconditional convergence by assertion.

Choose a **frozen, substantive** full-path property

$$
\psi_B(P_y)=P_y(\tau_B=\infty),\qquad Z_\psi=[0,1],\quad d_\psi(u,v)=|u-v|.
\tag{V20.8}
$$

Then baseline invariance gives $\psi_B(P_y^K)=1$ and (V20.7) gives $\psi_B(P_y^{K^J})\le\eta$, hence

$$
\kappa_{\psi_B,J}(B_1)\ge1-\eta;
\quad\text{in particular }\eta=0\Rightarrow \kappa_{\psi_B,J}(B_1)=1.
\tag{V20.9}
$$

This is a **uniform strategic-constitutive certificate for the declared property** only if $J$ is an admissible strategic intervention, $B_1$ satisfies its existing gate, and the confirmatory grounding map includes the region/survival semantics. It does **not** empirically identify a political transition.

### 2.4 Quasi-stationary destination corollary

If $\mu_B K_B=\theta_B\mu_B$ for a probability $\mu_B$ on $B$, $0\le\theta_B<1$, and $Q_r(y)=K(y,B^{(r)}\setminus B)$, then

$$
P_{\mu_B}(\tau_B<\infty,\;Y_{\tau_B}\in B^{(r)})
=\sum_{n\ge0}\theta_B^n\,\mu_B(Q_r)
=\frac{\mu_B(Q_r)}{1-\theta_B}.
\tag{V20.10}
$$

This follows from $\mu_B K_B^n=\theta_B^n\mu_B$. It requires $\theta_B<1$ for division; for $\theta_B=1$ the QSD assigns zero one-step exit mass and the division formula is not applicable. A QSD alone does not certify the uniform statewise finite-persistence gate.

**Adversarial tests:** off-by-one ($L=0,1$), destination overlapping $B$, incomplete partition of possible exits, certain nonexit, stochastic leak, competing targets, baseline Exact-GR zero exit routing, post-J switch into $B'_0$, target basin missed with positive probability, finite entry without target invariance, $\theta_B=1$ denominator exclusion.

## 3. Module A2: primitive kernel perturbation and finite-horizon constitutive margin

**Proposed paper location:** after Proposition 5.4 in Section 5.4.1. **Reuse:** Proposition 5.4 and Proposition 5.2/Corollary 5.3; CQ-1 finite model/output error transport.

### 3.1 Typed one-step composition (proposed Proposition 5.5)

Consider two well-posed triples $(\alpha,P,U)$ and $(\widetilde\alpha,\widetilde P,\widetilde U)$ on the same measurable types and feasible-action grammar. Assume row-uniform event-TV errors, including **all intervention-reachable** feasible rows,

$$
\begin{aligned}
\sup_y\|\alpha_y-\widetilde\alpha_y\|_{\mathrm{TV}}&\le\delta_\alpha,\\
\sup_{y,a}\|P_{y,a}-\widetilde P_{y,a}\|_{\mathrm{TV}}&\le\delta_P,\\
\sup_{y,a,x'}\|U_{y,a,x'}-\widetilde U_{y,a,x'}\|_{\mathrm{TV}}&\le\delta_U,
\end{aligned}\qquad 0\le\delta_\alpha,\delta_P,\delta_U\le1.
\tag{V20.11}
$$

Either use the global row assumption as displayed, or explicitly replace it by a weaker **proved reachable-row** variant. The induced joint kernels satisfy the universally available additive bound

$$
\sup_y\|K(y,\cdot)-\widetilde K(y,\cdot)\|_{\mathrm{TV}}
\le\delta_K,\qquad
\delta_K:=\min\{1,\delta_\alpha+\delta_P+\delta_U\}.
\tag{V20.12}
$$

**Proof:** In the iterated integral (V20.1), add and subtract terms replacing $U$, then $P$, then $\alpha$, holding all other factors fixed appropriately. Every intermediary integrand is measurable and $[0,1]$-valued. Applying the probability event-TV bound to each replacement yields $\delta_U+\delta_P+\delta_\alpha$, capped by one. The proof requires **no probabilistic independence assumption** between the stages.

An optional sharper bound, for suitably measurable maximal sequential couplings on standard-Borel state/action spaces, is

$$
\delta_K\le1-(1-\delta_\alpha)(1-\delta_P)(1-\delta_U).
\tag{V20.13}
$$

Prove the measurable coupling/common-overlap construction as a **separate** Lean obligation; do not attribute (V20.13) to the simple three-term analytic telescoping proof. On the coupling success event, action agrees first, then next world state, then next strategic state. Errors on inadmissible off-graph rows may not be evaluated unless the hypotheses explicitly require them.

### 3.2 Complete finite-horizon certificate (proposed Corollary 5.6)

For each label $\ell\in\{0,J\}$, separately obtain $\delta_{\alpha,\ell}$, $\delta_{P,\ell}$ and $\delta_{U,\ell}$ satisfying (V20.11) for the baseline and **matched post-intervention model**. Let

$$
e_\ell=1-(1-\delta_{K,\ell})^T
\le T\delta_{K,\ell},\qquad
\delta_{K,\ell}=\min\{1,\delta_{\alpha,\ell}+\delta_{P,\ell}+\delta_{U,\ell}\}.
\tag{V20.14}
$$

Suppose the frozen property depends only on the first $T$ transitions and is $L_\psi$-Lipschitz for event TV on the corresponding prefix laws. Then

$$
\left|\widetilde\kappa_{\psi,J}(B_1)-\kappa_{\psi,J}(B_1)\right|
\le L_\psi(e_0+e_J)
\le L_\psi T(\delta_{K,0}+\delta_{K,J}).
\tag{V20.15}
$$

A positive lower bound $\kappa>L_\psi(e_0+e_J)$ preserves a positive **uniform margin on the same frozen comparison set**. Independent property-evaluation errors $b_0,b_J$ add to the right-hand side. The approximate model's *own* admissible comparison-set gate must be established for a formal PR assertion; a numerical positive margin alone does not certify it.

**Proof:** apply Proposition 5.4 twice, the property Lipschitz condition, and the two-sided metric margin bridge of Proposition 5.2. The one-step approximations of baseline and $J$ must be modeled as actual typed replacements; do not assume that an arbitrary software perturbation respects $J$ or leaves $P$ fixed.

**Nonclaims:** finite $T$ is not an infinite-path bound; one-step TV does not transfer exact invariance; altered $P$ is structural/model error, not a pure strategic intervention; finite numerical grids cannot prove a global infimum; initial-law error and causal identification require independent ledgers.

**Adversarial tests:** zero horizon, error zero/one, total primitive error above one, off-graph rows, intervention-reachable but baseline-unvisited rows, wrong $\alpha\to P\to U$ order, changed-world masquerading as strategic, non-Lipschitz property, single-state versus all-$B_1$ minimum.

## 4. Module A3: long-run contraction/ergodic kernel-to-margin subclass

**This was in the original six-upgrade proposal and remains OPEN; it is not supplied by A2.**

Assume two baseline/intervention Markov pairs $(K_\ell,\widetilde K_\ell)$, $\ell\in\{0,J\}$, act on a common metric space $(Y,d)$ with the required finite first moments and invariant laws $\pi_\ell,\widetilde\pi_\ell$. Assume $K_\ell$ is uniformly $W_1$-contractive,

$$
W_1(\mu K_\ell,\nu K_\ell)\le\rho_\ell W_1(\mu,\nu),\quad
0\le\rho_\ell<1,\qquad
\sup_y W_1(K_\ell(y,\cdot),\widetilde K_\ell(y,\cdot))\le\delta_\ell.
\tag{V20.16}
$$

The invariant-law perturbation theorem is

$$
W_1(\pi_\ell,\widetilde\pi_\ell)
\le\frac{\delta_\ell}{1-\rho_\ell}.
\tag{V20.17}
$$

**Proof:** $\pi_\ell=\pi_\ell K_\ell$ and $\widetilde\pi_\ell=\widetilde\pi_\ell\widetilde K_\ell$ imply

$$
W_1(\pi_\ell,\widetilde\pi_\ell)
\le \rho_\ell W_1(\pi_\ell,\widetilde\pi_\ell)+\delta_\ell.
$$

Assume a globally $L_h$-Lipschitz descriptor $h$ and a $L_F$-Lipschitz property functional $F$ of the deterministic limiting descriptor occupation law, with the required equality $\psi(P_y^{K_\ell})=F(h_\#\pi_\ell)$ **for all $y\in B_1$ and all four compared processes** (or prove it from an ergodic convergence theorem). Then

$$
|\widetilde\kappa-\kappa|
\le L_F L_h\left(
\frac{\delta_0}{1-\rho_0}
+\frac{\delta_J}{1-\rho_J}
\right).
\tag{V20.18}
$$

If using a bounded-Lipschitz rather than Wasserstein metric on output laws, prove the relevant metric comparison explicitly. A typed primitive **Wasserstein** $\delta_\ell$ bound needs its own coupling/Lipschitz hypotheses; **do not substitute a total-variation primitive budget into (V20.18) without a proved conversion**. For bounded $d$ a conversion may exist with an explicit diameter factor; for unbounded $d$ it need not.

**Counterexample defeating an overclaim:** on $Y=\{0,1\}$ let $K(y,\cdot)=\delta_0$ and $\widetilde K(y,\cdot)=(1-\varepsilon)\delta_0+\varepsilon\delta_1$. Both are uniformly mixing, with small one-step TV discrepancy, but for $B=\{0\}$ the first has $P_0(\tau_B=\infty)=1$ and the second has $P_0(\tau_B=\infty)=0$ for every $\varepsilon>0$. Therefore (V20.18) is **not a theorem for arbitrary infinite-path exact-survival indicator properties**. Check Exact-GR status independently.

**Implementation split:** A3a finite-state stationary/contractive proof, A3b output-law bridge, A3c optional general Polish/Doeblin theorem; none should block the initial A2 finite theorem release.

## 5. Module B2: compositional $(\alpha,U)$ attribution and joint-only constitution

**Proposed paper location:** Section 5.4.2. **Strong existing basis:** Lane B (PR #51) already has an original-path-law finite Boolean witness with singleton effects zero and joint uniform margin one, including an original generalized PR. Do not count this existing existence result as a new first proof.

Freeze a four-corner intervention design, with identical non-intervened world primitive $P$, fixed property $\psi$, and admissible, explicitly joint replacements

$$
z_{00}(y)=\psi(P_y^{\alpha,U}),\quad
z_{10}(y)=\psi(P_y^{\alpha',U}),\quad
z_{01}(y)=\psi(P_y^{\alpha,U'}),\quad
z_{11}(y)=\psi(P_y^{\alpha',U'}).
\tag{V20.19}
$$

The effects are

$$
\begin{aligned}
\Delta_\alpha(y)&=d_\psi(z_{00},z_{10}),&
\Delta_U(y)&=d_\psi(z_{00},z_{01}),\\
\Delta_{\alpha U}(y)&=d_\psi(z_{00},z_{11}),&
\Delta_{U\mid\alpha}(y)&=d_\psi(z_{10},z_{11}),&
\Delta_{\alpha\mid U}(y)&=d_\psi(z_{01},z_{11}).
\end{aligned}
\tag{V20.20}
$$

The **sequential metric triangle theorem** is

$$
\begin{aligned}
|\Delta_\alpha(y)-\Delta_{U\mid\alpha}(y)|
&\le\Delta_{\alpha U}(y)
\le\Delta_\alpha(y)+\Delta_{U\mid\alpha}(y),\\
|\Delta_U(y)-\Delta_{\alpha\mid U}(y)|
&\le\Delta_{\alpha U}(y)
\le\Delta_U(y)+\Delta_{\alpha\mid U}(y).
\end{aligned}
\tag{V20.21}
$$

If $\sup_{B_1}\Delta_\alpha\le\varepsilon_\alpha$, then

$$
\inf_{B_1}\Delta_{U\mid\alpha}
\ge\kappa_{\alpha U}(B_1)-\varepsilon_\alpha;
\quad
\inf_{B_1}\Delta_{\alpha\mid U}
\ge\kappa_{\alpha U}(B_1)-\varepsilon_U
\quad\text{if }\sup_{B_1}\Delta_U\le\varepsilon_U.
\tag{V20.22}
$$

**Proof:** triangle and reverse triangle on $(z_{00},z_{10},z_{11})$ and $(z_{00},z_{01},z_{11})$ at each $y$, followed by the correct supremum/infimum inequalities. The false naive inequality $\Delta_{\alpha U}\le\Delta_\alpha+\Delta_U$ must appear as an explicit rejected claim: these two singleton legs do not form a path from $z_{00}$ to $z_{11}$.

### 5.1 Precise joint-only/self-healing definition

A pair of interventions is **singleton-null/joint-uniform-positive** on nonempty frozen $B_1$ if

$$
\forall y\in B_1:\Delta_\alpha(y)=\Delta_U(y)=0,
\qquad \kappa_{\alpha U}(B_1)>0.
\tag{V20.23}
$$

Under (V20.23), pointwise $\Delta_{U\mid\alpha}(y)=\Delta_{\alpha\mid U}(y)=\Delta_{\alpha U}(y)$, hence

$$
\inf_{B_1}\Delta_{U\mid\alpha}
=\inf_{B_1}\Delta_{\alpha\mid U}
=\kappa_{\alpha U}(B_1)>0.
\tag{V20.24}
$$

It may be called **self-healing/redundancy shielding** as a declared diagnostic taxonomy, but actual temporal recovery or learning reconstruction needs separately demonstrated dynamics. The strong null is not inferred from $\kappa_\alpha=\kappa_U=0$.

### 5.2 Explicit finite-state witness and existing proof reuse

A candidate all-Boolean model, included to keep the mechanism fully reproducible, is

$$
S=X=A=\{0,1\},\quad
\alpha(s,x)=\max(s,x),\quad P(x'\mid s,x,a)=\delta_a(x'),\quad U(s'\mid s,x,a,x')=\delta_a(s');
$$

$$
\alpha'(s,x)=s,\qquad U'(s'\mid s,x,a,x')=\delta_0(s').
\tag{V20.25}
$$

Use $B=Y$, $B_0=B_1=\{(1,0),(1,1)\}$, $h=g=x$, $H=\{0,1\}$, $\nu=\delta_1$, almost-sure weak occupation convergence, and the globally specified scalar functional

$$
\psi(\mu)=\limsup_{T\to\infty}\int\left(\frac1T
\sum_{t=0}^{T-1}x_t\right)d\mu,\quad d_\psi(u,v)=|u-v|.
\tag{V20.26}
$$

From both initial states, baseline and either singleton eventually keep $x_t=1$, so their property output is $1$. Under both replacements, $x_2=0$ and remains there, so output is $0$ and $\kappa_{\alpha U}=1$. Check Assumption 4.1, type feasibility, Borel measurability, original Exact-GR and relevance-map gates explicitly; do not assume an arbitrary numerical witness already has them.

**Already proved alternative:** GrammarRobust/BooleanPersistence.lean has actionEffect_eq_zero, updateEffect_eq_zero, jointMargin_eq_one and uniformRelativePR. BooleanEffects.lean and BooleanMinimalityCases.lean have OR/AND/XOR and minimal-block tests. **Prefer transporting these existing genuine theorem statements and adding only the missing general sequential inequalities** over duplicating an equivalent existence theorem.

### 5.3 Additive interaction only with algebraic structure

If $(Z_\psi,\|\cdot\|)$ is a normed vector space, define the same-state four-way interaction vector

$$
I_{\alpha U}(y)=z_{11}(y)-z_{10}(y)-z_{01}(y)+z_{00}(y),
\qquad
\mathcal I_{\alpha U}(B_1)=\sup_{y\in B_1}\|I_{\alpha U}(y)\|.
\tag{V20.27}
$$

This is **not** in general equal to the scalar $\Delta_{\alpha U}-\Delta_\alpha-\Delta_U$, nor does it automatically identify an empirical causal interaction. For arbitrary metric $Z_\psi$ use only the triangle diagnostics (V20.21), or explicitly define a convention-dependent nonadditivity score.

For a finite frozen admissible component grammar $\Gamma$, let $\mathcal D_\Gamma$ be its admitted blocks. A block $D$ is minimally uniformly constitutive if $\kappa_D>0$ and $\kappa_E\le0$ for all **proper admissible** $E\subsetneq D$. No monotonicity, uniqueness, downward closure or invariance under arbitrary relabeling is automatic. Reuse Lane B minimality and grammar-order transport, preserving the original path-law semantics.

**Adversarial tests:** universally zero versus infimum-zero; joint-only OR, incomparable AND minima, XOR cancellation, effect-matched invalid grammar relabeling; distinct PR outcomes for baseline-equivalent factorizations; conditional asymmetry with deliberately noncommuting replacements (these require a separate ordered protocol rather than pretending they are the four simultaneous corners).

## 6. Module F: multi-agent closed-loop vs declared frozen-response protocols

**Proposed paper location:** Section 5.4.3. **Scope:** conditional-product subclass, not a generic claim that all games have independent action/update kernels.

For finite players $I=\{1,\dots,n\}$, take $S=S_0\times\prod_i S_i$ and $A=\prod_i A_i$, with feasible behavior and conditional factorizations (if proven for the model)

$$
\alpha(da\mid s,x)=\bigotimes_i\alpha_i(da_i\mid s,x),\qquad
U(ds'\mid s,x,a,x')
=U_0(ds'_0\mid s,x,a,x')\otimes\bigotimes_iU_i(ds_i'\mid s,x,a,x').
\tag{V20.28}
$$

The $S_0$ factor can encode common information; correlated actions require an adequate shared source or a different factorization. Fix player $i$ and target replacements $(\alpha'_i,U'_i)$.

- $J_{i,\mathrm{CL}}$: replace player $i$ only, keep opponents' *functional kernels* and $P$ fixed, and allow $S_{-i,t},A_{-i,t}$ to respond to the altered counterfactual world/history.
- $J_{i,\mathrm{OL}}$: also replace opponents by a **frozen, ex-ante declared** non-reactive anchor $(\overline\alpha_{-i},\overline U_{-i})$ on all intervention-reachable states. Require typed feasibility and explicit treatment of clock/time if the anchor is nonstationary. Agreement with baseline support is optional evidence, **not sufficient to identify a unique anchor outside that support**.

Define the three property points $z_0(y)=\psi(P_y)$, $z_{\mathrm{CL}}(y)=\psi(P_y^{J_{\mathrm{CL}}})$, $z_{\mathrm{OL}}(y)=\psi(P_y^{J_{\mathrm{OL}}})$ and their distances to baseline $\Delta_{\mathrm{CL}}$, $\Delta_{\mathrm{OL}}$ and mutual adaptation-protocol distance $A_i(y)=d_\psi(z_{\mathrm{CL}},z_{\mathrm{OL}})$. Then

$$
|\Delta_{\mathrm{CL}}(y)-\Delta_{\mathrm{OL}}(y)|
\le A_i(y)\le \Delta_{\mathrm{CL}}(y)+\Delta_{\mathrm{OL}}(y).
\tag{V20.29}
$$

If $\Delta_{\mathrm{OL}}(y)=0$, then $A_i(y)=\Delta_{\mathrm{CL}}(y)$; conversely if $\Delta_{\mathrm{CL}}(y)=0$, $A_i(y)=\Delta_{\mathrm{OL}}(y)$. These are metric identities, **not identified direct/indirect causal mediation effects**: the OL protocol intervenes on the opponents' mechanisms as well. To interpret a causal response channel, impose separately defended structural modularity, observation/support, opponent-anchor and identification assumptions.

**Tests:** two-player response vs frozen, identical baseline/off-support different anchors, correlated actions beyond product subclass, opponent anchor violating action feasibility, intervention changing $P$ incorrectly, nonstationary opponent needing clock state, direction and uniform-gap claims separated.

## 7. Module E: approximate type-respecting state quotients

**Proposed paper location:** Section 7.4.3 immediately after Theorem 7.4b. **Reuse:** original type-respecting product quotient, full frozen intervention-family mapping, property/relevance descent, original admissible comparison sets and lift condition, and Proposition 5.4.

Let $q=q_S\times q_X:Y\twoheadrightarrow\bar Y$ be measurable, type-respecting and surjective. Let $\phi$ be a frozen target/type-grammar-preserving bijection between intervention labels including baseline label $0$. Retain conditions (ii)–(vi) of Theorem 7.4b **independently**: $B,B_0,B_1$ are inverse images of $\bar B,\bar B_0,\bar B_1$; both specifications satisfy their nontriviality gates; $h=\bar h\circ q$; $\psi$ factors through the entire coordinatewise projected path law on the compared laws; $g=\bar g\circ q$ for grounded claims; and quotient initial laws have admissible lifts. Do not infer any of these from small TV error.

Replace exact kernel intertwining by

$$
\eta_\ell=\sup_{y\in Y}
\left\|q_\# K^\ell(y,\cdot)
-\bar K^{\phi(\ell)}(q(y),\cdot)\right\|_{\mathrm{TV}}
\in[0,1],\qquad \ell\in\{0\}\cup\mathcal J.
\tag{V20.30}
$$

The projected fine process $q(Y_t)$ need **not** itself be Markov. Nevertheless, the finite-prefix laws from the **same fine initial state** satisfy

$$
\left\|(q^{0:T})_\#P_y^{K^\ell,0:T}
-P_{q(y)}^{\bar K^{\phi(\ell)},0:T}\right\|_{\mathrm{TV}}
\le \min\{1,T\eta_\ell\}.
\tag{V20.31}
$$

**Provable analytic induction without Rokhlin disintegration:** at $T=0$ both prefix laws are $\delta_{q(y)}$. For event $A\subseteq\bar Y^{T+1}$, integrate the continuation probability starting from fine $y'$ against $K^\ell(y,dy')$, add and subtract the quotient continuation $\bar u(q(y'))$, bound the continuation difference by the inductive $\delta_{T-1}$ uniformly over all $y'$, and bound the remaining difference of integrals of a $[0,1]$-valued function by $\eta_\ell$. Thus $\delta_T\le\delta_{T-1}+\eta_\ell$, giving (V20.31). This argument requires measurable path kernels/functions and pushforward integration, not a fine-fibre RCD.

The **sharper conjectured/available coupling-style** bound

$$
\delta_T\le1-(1-\eta_\ell)^T
\tag{V20.32}
$$

must be a **separate proof obligation**. The simple add-and-subtract induction alone does not justify $\delta_T\le(1-\eta)\delta_{T-1}+\eta$. A common-overlap-submeasure or measurable maximal-coupling construction must quantify matched first-step mass and control the unmatched remainder. If that measure-theoretic bridge is not available in mathlib, ship the rigorously established linear theorem and leave (V20.32) OPEN, not asserted proved.

For a $T$-prefix $L_\psi$-TV-Lipschitz property and $\ell\in\{0,J_\star\}$, property factorization plus (V20.31) yields, for each $y\in B_1$,

$$
\left|
\Delta_{\psi,J_\star}(y)
-\bar\Delta_{\bar\psi,\phi(J_\star)}(q(y))
\right|
\le L_\psi T(\eta_0+\eta_{J_\star}).
\tag{V20.33}
$$

Surjectivity $q(B_1)=\bar B_1$ gives

$$
\boxed{
|\kappa_{\psi,J_\star}(B_1)
-\bar\kappa_{\bar\psi,\phi(J_\star)}(\bar B_1)|
\le L_\psi T(\eta_0+\eta_{J_\star}).
}
\tag{V20.34}
$$

If $\kappa$ exceeds this full budget, the **quotient margin** remains positive, and vice versa. A strictly positive quotient margin is not alone an **Exact GR or PR certificate**: independently establish the respective Exact-GR/confirmatory gates on both sides before making full PR claims. If comparing whole-path non-Lipschitz properties, replace the finite-horizon bridge by separately proved property-output budgets $\varepsilon_0^{\mathrm{quot}},\varepsilon_J^{\mathrm{quot}}$ and use $|\kappa-\bar\kappa|\le\varepsilon_0^{\mathrm{quot}}+\varepsilon_J^{\mathrm{quot}}$.

**Explicit destructive example:** identity quotient on $\{0,1\}$, baseline $K(y,\cdot)=\delta_0$ and approximation $\bar K(y,\cdot)=(1-\eta)\delta_0+\eta\delta_1$. With $B=\{0\}$, baseline Exact-GR invariance holds but quotient invariance fails for every $\eta>0$. This defeats any inference of exact persistence from approximate intertwining even under strongly mixing kernels.

**Tests:** $\eta=0$ reduction to exact quotient when all original semantic gates hold, $\eta=1$, horizon zero, untyped quotient rejection, baseline-only versus complete frozen family, label mismatch, non-lumpable hidden state, failure of $\psi/h/g$ descent, failure of initial-law lifts, approximate equivalence of margins without Exact GR, leakage counterexample, sharp-bound proof with common mass (if attempted).

## 8. Cross-lane economic/game-theoretic flagship (X1)

**Proposed manuscript location:** new Section 8.4 (or separate application section), not a claim that the present two-state witnesses already certify an economic game.

Freeze one **identical world kernel** $P(dx'\mid x,a)$, world space $X$ (e.g. finite resource depleted/replete states), common joint action set $A=\prod_i A_i$, payoffs $r_i(x,a)$, discount $\beta_i\in(0,1)$, and one substantive comparison of $B,B_0,h,g,\psi,B_1$. Use compatible typed strategic states for both generator implementations, with an explicit transport if their internal memory spaces differ.

**Generator E:** an actually certified Markov-perfect equilibrium $\pi^*$, not just a stationary policy. For finite discounted payoffs its value vector must satisfy, for all $i,x$,

$$
V_i(x)=\sum_a\pi^*(a\mid x)
\left[r_i(x,a)+\beta_i\sum_{x'}P(x'\mid x,a)V_i(x')\right],
\tag{V20.35}
$$

and for every unilateral alternative $a_i$,

$$
V_i(x)\ge\sum_{a_{-i}}\pi^*_{-i}(a_{-i}\mid x)
\left[r_i(x,a_i,a_{-i})+
\beta_i\sum_{x'}P(x'\mid x,a_i,a_{-i})V_i(x')\right].
\tag{V20.36}
$$

Also prove equality for actions receiving positive support in a mixed equilibrium. On finite rational examples certify the relevant value equations and incentive inequalities with exact arithmetic. Embed $\pi^*$ through the original EGR-to-GR machinery with a clearly defined strategic update.

**Generator L:** a finite-memory reinforcement, log-linear, or multiplicative-weights-style update $(\alpha^{\mathrm{learn}},U^{\mathrm{learn}})$ sharing **exactly the same world $P$**, with fully specified parameters, feasible actions and Markov sufficient memory. Prove the claimed nonstationary/periodic/occupation behavior rather than inferring persistent cycles from a plot.

The empirical and mathematical outputs must be calculated for both:

$$
K_{B,\mathrm E}^L{\bf1}_B,\quad
K_{B,\mathrm L}^L{\bf1}_B,\quad
\kappa^{\mathrm E}_{\psi,J^\alpha},\quad
\kappa^{\mathrm E}_{\psi,J^U},\quad
\kappa^{\mathrm L}_{\psi,J^\alpha},\quad
\kappa^{\mathrm L}_{\psi,J^U},
\quad\text{and relevant joint effects}.
\tag{V20.37}
$$

**Critical consistency condition:** identical $P$, $B$, $h$, $g$ and comparison criterion do **not** imply the same long-run $\nu$. If the E and L occupation limits differ, either compare both against one frozen target (allowing one to fail its GR gate) or declare separate $\nu_{\mathrm E}$ and $\nu_{\mathrm L}$ while keeping the substantive comparison semantics fixed. A common specification $\Sigma$ may be asserted for both **only if both actually satisfy its frozen occupation target and convergence mode**.

Record all **nine orthogonal categorical application-certificate dimensions** (validity, epistemic mode, selection, identification, statistics, provenance, substantive PR status, direction and uniform-gap status). They are not nine numerical scores and do not turn a parameterized mathematical example into an empirically confirmed institution.

**Falsifiers:** non-equilibrium policy falsely labelled MPE; payoffs optimized under a different $P$; learning update unrecorded in Markov state; different targets hidden by a shared $\nu$ label; unreachable decorative descriptors; same baseline observation with distinct typed constitution; numerical versus formal witness confusion.

## 9. Non-breaking clarification and editorial carry-forward

These are **proposed v0.2.0 source improvements**, not retroactive errors in v0.1.8 and not changes to the immutable release.

1. **Off-graph U extension:** Section 3.3/3.4 should state that a kernel $U$ initially specified on the feasible graph receives a measurable extension to the full product using a fixed law on nonempty $S$, parallel to the already-described $P$ extension using nonempty $X$.
2. **Post-exit descriptor grounding:** Section 5.2 or Appendix 15.2 should explicitly require any confirmatory property that reads $h(Y_t)$ after $\tau_B$ to justify and freeze $h|_{Y\setminus B}$ substantively. An arbitrary decorative extension cannot be promoted to a grounded constitutive conclusion without a matching relevance-map justification.
3. **TeX syntax:** correct the source text containing $\psi$/outcome (not $\psi/outcome$ entirely in math mode); render $(L,\eta)$-quasi with the hyphen outside math mode; standardize theorem-header/proof emphasis and mathematical-symbol markup.
4. **Tables:** Tables 3 and 4 currently use a longtable with detached prose captions; move captions into the correct table environment and preserve meaningful page breaks. Do not blindly replace a genuinely multipage longtable with an overfull float.
5. **Release discipline:** make a new versioned v0.2.0 TeX, compile and visually proofread, construct a new SHA/test manifest and paper-to-Lean crosswalk; do not mutate or relabel the verified v0.1.8 TeX/PDF/hash or historical PASS reports.

## 10. Paper-to-Lean wiring and declaration acceptance ledger

The names below are **proposed new declarations**, not existing proof claims. Keep fresh work under PermanssonResearch and direct-import every new module in PermanssonResearch.lean; never alter existing original theorem statements to make a proposed extension appear to fit.

| Proposed paper item | Lean target (candidate) | Required existing connection | Acceptance theorem / countermodel |
|---|---|---|---|
| Def. 4.2d / Thm. 4.2e | RegimeExit/ExitRouting.lean: exitRouting_eq_prob_exit_in, exitRouting_add_killedSurvivalMass_eq_one | survivalProbability_eq_killedSurvivalMass | horizon 0/1; overlap; infinite nonexit |
| Prop. 4.2f | RegimeExit/ConstitutiveSwitch.lean: routedSwitch_stays_target, routedSwitch_margin_ge | Original Exact-GR and relative PR interfaces | arrival only versus arrival-and-stay; $\eta$ budget |
| QSD destination | RegimeExit/QSDExit.lean: qsd_exitTarget_eq_fraction | proposition_4_4b | $\theta=1$ excluded; multiple destinations |
| Prop. 5.5 | Perturbation/PrimitiveTV.lean: inducedKernel_tv_le_primitive_sum | inducedKernel_apply, eventTotalVariation | stage-order, feasible rows; sum cap |
| Prop. 5.5 sharp | Perturbation/PrimitiveTVSharp.lean: inducedKernel_tv_le_primitive_product | suitable measurable coupling/common mass | optional; do not assert if missing |
| Cor. 5.6 | Perturbation/PrimitiveMargin.lean: robustUniformPR_of_primitive_tv | proposition_5_4, constitutiveMargin_perturbation_abs_le, CQ-1 | two distinct error budgets, finite horizon |
| A3 contraction | Perturbation/ContractiveOccupation.lean: invariantLaw_wasserstein_le, occupationMargin_robust | finite invariant/occupation law foundations | discontinuous survival counterexample |
| Def. 5.8/Prop. 5.9 | GrammarRobust/SequentialEffects.lean: jointEffect_le_action_add_condUpdate, condUpdateMargin_ge_joint_sub_action | original path-law property map and margins | triangle and conditional unlocking |
| Prop. 5.10 witness | existing GrammarRobust/BooleanPersistence.lean; optional bridge to new notation | actionEffect_eq_zero, updateEffect_eq_zero, jointMargin_eq_one, uniformRelativePR | **already exists in appropriate scope** |
| Def. 5.11/Prop. 5.12 | MultiAgent/Protocols.lean, MultiAgent/AdaptationBound.lean: abs_closedLoop_sub_openLoop_le_adapt | typed strategic kernel composition | distinct anchors and infeasible responses |
| Thm. 7.4c linear | Quotient/ApproxPrefix.lean: approxQuotient_pathLaw_tv_le_linear | exact quotient typing, finite prefix and TV | non-Markov projected state, $\eta T$ |
| Thm. 7.4c margin | Quotient/ApproxMargin.lean: approxQuotient_margin_abs_le | constitutiveMargin_perturbation_abs_le | positive margin **not** automatically Exact GR |
| Thm. 7.4c sharp | Quotient/CommonMass.lean: approxQuotient_pathLaw_tv_le_geometric | common submeasure/measurable lift | optional, independent proof |
| Flagship E/L | Examples/CommonsMPELearning.lean and independently checked rational fixtures | D1, C-lane occupation and original EGR transport | exact incentive test; distinct occupation laws |

**Lean acceptance includes exact binder/quantifier inspection.** Some existing results require CountableOrCountablyGenerated measurable-space instances; merely quoting a paper-level Polish assumption without the corresponding Lean instance is insufficient. In particular, do not say that the geometric quotient theorem requires *zero* extra measure theory if its overlap lift has not been proved.

## 11. New destructive-test ledger

| ID | Failure / expected result |
|---|---|
| ER1 | $R_B^{(0)}=0$ and $P_y(\tau_B>0)=1$ for $y\in B$ |
| ER2 | $R_B^{(1)}(y,D)$ counts **only** $D\setminus B$ |
| ER3 | $R_B^{(L)}(Y\setminus B)+K_B^L1_B=1$ for every declared finite case |
| ER4 | Baseline Exact GR exit routing is zero, post-J routing may differ |
| ER5 | Entering an alternative set without Exact-GR invariance does not certify switching |
| ER6 | QSD exit formula holds only for $\theta<1$ |
| PT1 | Primitive errors sum $\gt1$ clamps TV at one; linear and sharp constants checked separately |
| PT2 | A perturbed row reachable only under $J$ is not ignored |
| PT3 | Different world $P$ is not automatically a strategic intervention |
| PT4 | Small kernel TV can flip exact infinite survival |
| SY1 | Both singleton **pointwise** null, joint margin one |
| SY2 | $\inf\Delta=0$ while some states have positive effect; no false null |
| SY3 | Naive baseline-origin subadditivity explicitly fails |
| SY4 | AND incomparable minima, XOR nonmonotonicity, grammar transport conditions |
| MA1 | Closed/open adaptation differs after an intervention-reachable state |
| MA2 | Two baseline-agreeing OL anchors disagree off support; protocol not identified |
| MA3 | Correlated-player model not misrepresented by product factorization |
| AQ1 | Exact $\eta=0$ recovers only the appropriately typed/exact theorem |
| AQ2 | Projected fine state non-Markov, yet finite-prefix linear TV bound holds |
| AQ3 | Small intertwining error breaks exact invariance; preserve margin versus GR firewall |
| AQ4 | Full frozen intervention family and label grammar required |
| AQ5 | The sharper geometric bound cannot be marked proved from additive induction alone |
| EG1 | Equilibrium conditions checked with the **same** world primitive |
| EG2 | Learning dynamics with different limit cannot be assigned equilibrium's same $\nu$ |
| EG3 | Application certificate flags theoretical versus empirical status honestly |

Test fixture naming and actual counts must be recorded after implementation, not invented in this specification. Reuse historical Runs 17–30 without changing their frozen source/results, and add a separately named v0.2.0 destructive suite.

## 12. PR decomposition, state machine and release gate

1. **DOC-0 (this specification):** roadmap + detailed theorem contract + dated research-status reconciliation + navigation. **No Lean, tests, TeX, toolchain or application schema writes.** This PR must remain unmerged until reviewed and approved; do not attach its changes to PR #62.
2. **A2:** additive primitive TV and finite-horizon margin closure; optional sharp bound separate.
3. **B2:** metric sequential effects, conditional margin and existing Lane B witness bridge; reuse, do not duplicate.
4. **C-Exit:** sub-Markov destination and mass conservation, strong Markov target routing, QSD corollary.
5. **E1:** linear approximate-quotient path error then margin; optional geometric bound as E2.
6. **F1:** product-game and explicit CL/OL protocol objects and adaptation metric.
7. **A3:** contractive long-run kernel-to-occupation-law margin subclass.
8. **X1:** fully specified and independently certified MPE versus non-equilibrium learning commons benchmark.
9. **Release integration:** generate **new** v0.2.0 source/PDF only from proved or visibly marked conditional material, with theorem/Lean map and SHA manifest; preserve v0.1.8 release identity.

**Suggested dependency order:** A2 uses CQ-1 / Prop. 5.4, B2 uses Lane B, C-Exit uses C/C10 and killed kernels, E1 uses exact quotient typing plus Prop. 5.4, F1 uses typed composition, A3 uses invariant-law/contractive lemmas, X1 consumes A/B/C/D/E/F as applicable. Maintain an acyclic research import DAG: extract small shared lemmas to lower-level modules instead of importing a downstream solver.

**Per-PR stop conditions:** exact theorem statement and hypotheses reviewed; proof compiled at source head and GitHub synthetic merge; transitive axiom audit permits only propext, Classical.choice and Quot.sound; no sorry, admit, custom axiom or hidden native_decide; original and research Lean, executable verification and application-contract workflows green; destructive negative controls pass; current paper-to-Lean ledger and claim firewall updated; no unrequested auto-merge. A failing or skipped check is OPEN, not PASS.

**Scientific nonclaims:** None of these theorems alone proves kernel identification from observed trajectories, universal game-theoretic novelty, a calibrated economic prediction, political-regime collapse, a practical intervention's safety/effectiveness, or a real-world PR certificate. Quantified model uncertainty, evidence vintage, causal modularity, provenance, simultaneous statistical coverage and the nine-dimensional application status remain independent gates.

## 13. Cross-references and change management

- [Future-theory roadmap](FUTURE_THEORY_ROADMAP.md) — navigational programme and implementation status.
- [Master research architecture](PERMANSSON_RESEARCH_ARCHITECTURE.md) — historical A/B/C/D design, its precise original contracts, and the v0.2.0 addendum link.
- [Research build guide](RESEARCH_BUILD.md) — implemented source and CI; historical entries may predate merged PR statuses.
- [Formalization map](FORMALIZATION_MAP.md) — frozen original theorem inventory, not a claim that proposed v0.2.0 statements are done.
- [Original paper and hash-verified TeX](../paper/README.md) — immutable release boundary.
- [Lane B exact joint-only theorem](../PermanssonResearch/GrammarRobust/BooleanPersistence.lean).
- [CQ-1 robustness machinery](../PermanssonResearch/ConstitutiveQuasi/Robustness.lean).
- [C10 typed absorption mathematics](../PermanssonResearch/ReverseSolver/TypedStoppedClassAbsorption.lean).
- [Existing exact quotient preservation](../PermanssonLean/Quotient/Preservation.lean).

**Promotion rule:** only promote a PROPOSED theorem to PROVED after checking the *exact* encoded hypothesis and conclusion, with CI and verification evidence specific to its final commit. This full mathematical specification deliberately preserves OPEN obligations so no future engineer must reconstruct what was meant from a one-paragraph upgrade summary.
