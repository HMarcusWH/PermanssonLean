# M — Strict MA2: an autonomy obstruction, not another recording toy

**Atlas:** F1-MA2. **New derivation:** a stochastic finite-state obstruction under full baseline-support agreement and the actual autonomous opponent-locked restrictions. This is a stronger paper result than the existing deterministic-recording obstruction. It is not yet a Lean theorem and does not assert impossibility for every conceivable meaning of a nonreactive anchor.

## M-DATA — Exact hypotheses

All state/action sets are finite and nonempty. Write
$y=(s_0,s_1,s_2,x)$ and $q(y)=(s_0,s_2)$. Fix the baseline generator $G$, physical $P$, and a starting law $\mu$. The common update is exogenous:

$$U_0(s_0'\mid y,a,x')=c(s_0'\mid s_0).$$

For either of the two anchors, indexed by $j\in\{a,b\}$, the mechanisms factor as

$$\alpha_2^j(a_2\mid y)=p^j(a_2\mid q(y)),
\qquad U_2^j(s_2'\mid y,a,x')=u^j(s_2'\mid q(y),a_2).$$

These are the source's `IsStrictlyNonReactive` plus `IsExogenousCommon`. Conditional action and update products are those of `TwoPlayerGenerator`. In particular, the common/private updates have no unrecorded shared randomization.

Let $R$ be the set of states with positive baseline probability at some finite time. For each $j\in\{a,b\}$ require agreement with the **baseline opponent** as follows:

1. For every $y\in R$, $p^j(\cdot\mid q(y))=\alpha_2^G(\cdot\mid y)$.
2. For every baseline-supported update input $(y,a_1,a_2,x')$, namely
$y\in R$ and
$\alpha_1^G(a_1\mid y)\alpha_2^G(a_2\mid y)P(x'\mid y,a)>0$,
$u^j(\cdot\mid q(y),a_2)=U_2^G(\cdot\mid y,a,x')$.

Equality only of a final statistic or only of the unmarked $q$-transition is insufficient. Equality of updates merely at the initial state is insufficient.

## M-AUTONOMY — The key process is autonomous

Under any treated player-1 replacement $r$, and anchor $b$, the next key has kernel

$$L_b((s_0,s_2),(s_0',s_2'))=
 c(s_0'\mid s_0)\sum_{a_2}p^b(a_2\mid s_0,s_2)
 u^b(s_2'\mid s_0,s_2,a_2).$$

**Proof.** Sum the full actual transition over the next world and player-1 state. The player-1 update, world transition and player-1 action law each integrate to one. The factors displayed above do not depend on the coordinates integrated out. This proof uses product structure and common exogeneity, not an informal causal assertion.

## M-CLOSURE — Baseline key support remains closed after treatment

Put $Q=q(R)$. For every $q\in Q$, the anchors' action laws agree. For every $a_2$ with positive common probability, their private-update laws agree. Consequently $L_a=L_b$ on $Q$, and $L_a(q,Q)=L_b(q,Q)=1$ there.

**Proof.** Choose a baseline-reachable $y$ with key $q$. Action equality is Hypothesis 1. If its $a_2$ mass is positive, the baseline player-1 action law has a positive atom $a_1$ and the physical kernel then has a positive atom $x'$. Hypothesis 2 at that input identifies both anchor updates. To prove closure, take a positive term contributing to a next key $(s_0',s_2')$. The chosen supported action/world input, the positive common update and positive opponent update can be completed by some positive player-1 update atom. This gives a positive baseline transition to a state with that key. Thus the next key lies in $Q$.

The positive-atom selection is valid because the spaces are finite. It is not silently reused as a pointwise argument for nonatomic spaces.

## M-NOSEPARATION — Full counterfactual laws coincide

**Theorem.** For every common player-1 replacement $r$,

$$\mathbb P_\mu^{\operatorname{OL}(G,r,a)}
=\mathbb P_\mu^{\operatorname{OL}(G,r,b)}.$$

**Proof.** The initial key belongs to $Q$ almost surely. M-AUTONOMY and M-CLOSURE keep the key in $Q$ under either counterfactual. At every full state whose key is in $Q$, the two opponent action laws agree; on every action with positive mass their update laws agree. The player-1 mechanism, common update and physical world are identical. Expanding the actual stage product therefore gives equal full transition kernels on $q^{-1}(Q)$. Induction gives identical finite-prefix laws, and existing canonical path uniqueness gives identical infinite laws. Every measurable property of those laws agrees.

The same reasoning works for a common nonanticipating history-dependent treated mechanism once the trace law is explicitly constructed. The first Lean target should use the existing stationary `PlayerOneMechanism` interface, for which no new history semantics are needed.

**Consequence.** A strict MA2 separation witness cannot exist in this finite autonomous subclass under the stated support agreement. The correct closure is this obstruction theorem. It does not discharge a different MA2 statement that uses weaker agreement, endogenous common state, correlated hidden updates, or another anchor semantics. Keep those distinctions visible in the status crosswalk.

## M-AE — Standard-Borel extension contract

A non-atomic extension replaces positive support by almost-everywhere mechanism equality at each baseline time. Use specified factor kernels $p^a,u^a,p^b,u^b,c$ and standard-Borel spaces. Let $\mu_t$ be the baseline state law, $\nu_t=q_\#\mu_t$. Require action equality $\mu_t$-a.e. and update equality a.e. under the actual baseline law of $(Y_t,A_t,X_{t+1})$, for every $t$.

Pushforward of the action equality identifies $p^a=p^b$ $\nu_t$-a.e. Pushforward of the update-input law identifies $u^a=u^b$ a.e. under $\nu_t(dq)p^a(q,da_2)$. These equalities also identify the baseline key transition with $L_a$ and $L_b$. Therefore the key marginal under either treated law remains $\nu_t$ by induction. At time $t$, conditional full transition laws agree under the actual treated marginal, since the exceptional keys have zero $\nu_t$ mass. Prefix induction and uniqueness finish the proof.

**Measurability dependency.** Equality of measure-valued kernels and the exceptional sets must be reduced to countable determining classes on standard-Borel targets. Prove that lemma explicitly; do not identify a union of uncountably many null sets with a null set. This is a separate measurable extension of M-NOSEPARATION. Arbitrary measurable targets remain outside this derivation.

**Build.** Add `MultiAgent/AutonomousKey.lean`, `AutonomousSupportClosure.lean`, `StrictMA2Obstruction.lean`, followed separately by `AutonomousAEMechanisms.lean`. Export the autonomous marked-kernel formula, support closure, supported full-kernel equality and full path-law equality. Preserve the original strict witness requirement as open outside the proved subclass; do not relabel the old reactive example as strict.

**Falsifiers.** Route player 1's action into $S_0'$; permit $U_2$ to read $x'$; drop update agreement; compare only one time's support; or equate only a projected statistic. Each invalidates a stated premise and must be classified as such. The independent tests exercise all 64 deterministic treated rules on a six-state finite model with two different anchors agreeing on a closed reachable key set. Finite testing corroborates, but does not prove, M-NOSEPARATION.

# F — Additional multi-agent contracts

## F-SWAP — Player 2 without an unjustified symmetry assumption

**Atlas:** F1-P01. Define player-2 CL directly by replacing `G.player2`; OL additionally replaces `G.player1` by its declared anchor. $P$ and $U_0$ remain literal fixed objects.

For code reuse, let $\tau(s_0,s_1,s_2,x)=(s_0,s_2,s_1,x)$ and swap the action coordinates. Define the swapped physical kernel by pullback of its **inputs**, not by asserting $P$ is symmetric. Reindex the output strategic coordinates similarly. Finite-sum change of variables gives

$$K^{\mathrm{swap}}(\tau y,\tau E)=K(y,E).$$

Prefix induction transports path laws; property pullback, comparison-set image and original margin equality follow. Applying the existing player-1 construction in swapped coordinates and transporting back produces the required player-2 construction even in an asymmetric game. Test an asymmetric payoff/world model; a coordinate permutation must not exchange the meaning of fixed physical mechanisms inside one comparison.

## F-N — Finite indexed product protocols

**Atlas:** F1-P02. For a finite index set $I$, define
$S=S_0\times\prod_{i\in I}S_i$, $A=\prod_iA_i$,
$\alpha_y=\bigotimes_i\alpha_{i,y}$ and
$U_{y,a,x'}=U_{0,y,a,x'}\otimes\bigotimes_i U_{i,y,a,x'}$.
For treated $i$, CL replaces only its action/update; OL also installs the specified opponent anchors. Finite products of probability kernels are probability kernels; cylinder evaluation and the finite-product integral prove the action/update formulas and actual $K$. The original joint-strategic family then proves fixed $P$.

For a common original metric property, put $z_0,z_C,z_O$ for the three values. The existing triangles give

$$|d(z_0,z_C)-d(z_0,z_O)|\le d(z_C,z_O)
\le d(z_0,z_C)+d(z_0,z_O).$$

A uniform bound on the gap over the same comparison set gives the margin comparison by G-MARGIN's infimum argument. No independent-action representation theorem for all games is asserted. Reduction to $|I|=2$ must agree with existing source; the empty-index case has no treated player.

## F-CLOCK — Legitimate nonstationary anchors

**Atlas:** F1-P03. Enlarge a permitted common or private state with $t\in\mathbb N$ and actually update $t'=t+1$. At state $t$, use the declared anchor $(p_t,u_t)$. Projecting away the clock gives exactly the finite prefixes of the chronological time-inhomogeneous process, by induction on time. Common-clock exogeneity holds only if the original lifted common update reads the old common state/clock and not treated variables. A private clock belongs to the anchor's own state and is updated through its own update mechanism.

This defines a **new lifted baseline model**. It does not add a clock coordinate to a frozen model while leaving its update unable to advance that clock. Prove the projection bridge and inherited feasibility. A periodic two-step anchor is the positive test; a purported common clock updated by the treated action is the negative test.

## F-FEAS — Feasible strict anchors and a useful impossibility test

**Atlas:** F1-P04. In a finite model let $\mathcal A_2(y)$ be the legal actions. A strict anchor reads $q$, so define

$$I(q)=\bigcap_{y:q(y)=q}\mathcal A_2(y).$$

Then a strict action law is feasible at every state iff its support is contained in $I(q)$ for every key. A feasible strict anchor exists iff every realized key has nonempty $I(q)$; choose the least legal action in the fixed finite ordering to construct one.

**Proof.** A common law supported in each fibre member's legal set is supported in their finite intersection. Conversely support in the intersection implies every individual constraint. A probability law cannot be supported on the empty set. Nonempty intersections admit the deterministic selection.

Nonempty $\mathcal A_2(y)$ separately is insufficient: two states sharing a key may permit disjoint actions. Restriction to a reachable domain is legitimate only with a proof that the domain is invariant under all compared protocols. Joint nonrectangular feasibility is not equivalent to separate component feasibility: in that case check support of the full joint action law against the actual joint legal set.

## F-LUMP — Exact behavioral autonomy criterion

**Atlas:** F1-P05. This is a selected, fully quantified characterization, not a structural causal-identification theorem. Let $K_c$ be a finite controlled family and $q:Y\to Q$. Then the following are equivalent:

1. There exists a kernel $L$ with $q_\#K_c(y)=L(q(y))$ for every state and admissible control.
2. From every point start and under every nonanticipating admissible control rule, the projected next-key law conditional on the full history is $L(q(Y_t))$.

**Proof.** (1) implies (2) by conditioning on the actual control and summing a convex combination of the identical projected rows. Conversely specialize (2) to time zero, each point start and each deterministic admissible control.

For autonomy of opponent **actions as well as states**, use the marked one-step kernel of $(A_{-i},Q_{t+1})$ in place of $q_\#K_c$. Equal unmarked key laws can conceal different action couplings. Structural own-state factorization plus common exogeneity is sufficient for the marked criterion; it is not necessary because model-specific cancellations can occur. A criterion from only one observed starting law cannot establish this all-state/all-control equivalence.

## F-CORR — Correlated joint action construction

**Atlas:** F1-P06. For a finite joint law $\gamma_y$ on $A=\prod_i A_i$, sample a mediator variable $Z\in A$ with law $\gamma_y$, and let player $i$ take $A_i=Z_i$. Then

$$\sum_{z\in A}\gamma_y(z)\prod_i1_{\{a_i=z_i\}}=\gamma_y(a).$$

This is an exact mixture-of-products representation. The mediator sample is part of the action-generation stage, not an unannounced alteration of the old state. The original general strategic generator can consume the resulting joint kernel. If a public signal is instead carried in $S_0$, define its initialization/update and prove the time-shift bridge explicitly. A state-dependent mediator law is not automatically exogenous. Which signals are observed changes the deviation class and must be part of the game specification.

The diagonal Boolean law assigning $\frac{1}{2}$ to 00 and 11 cannot itself be one independent product: its two fair marginals would assign $\frac{1}{4}$ to all four pairs. This falsifies a universal conditional-product claim, not the mixture construction.

## F-CAUSE — Causal decomposition under an explicit finite SCM

**Atlas:** F1-P07. A new causal model is required. Choose finite pretreatment covariate $C$, treatment $T$, mediator $M=f(T,C,U_M)$ and outcome $Y=g(T,M,C,U_Y)$. Given $C$, require treatment assignment independent of the noises and $U_M\perp U_Y$, consistency/modularity, and positivity at each treatment/mediator value used. Define potentials using the same declared noises.

Then

$$\mathbb E[Y(t,M(t'))]=
\sum_c p(c)\sum_m
\mathbb E[Y\mid T=t,M=m,C=c]\,
 p(m\mid T=t',C=c).$$

**Proof.** Condition on $C$ and $M(t')$. Noise independence makes the conditional outcome response at fixed $(t,m,c)$ equal its interventional response. Consistency, treatment independence and positivity identify that response and mediator distribution with the displayed observational conditionals. Sum the finite probabilities.

Signed total effect decomposes exactly by adding and subtracting $Y(1,M(0))$ inside expectation. An absolute metric gap need not decompose additively. Without these new premises there is a counterexample: let $T$ be fair, $M=T$, and compare SCMs $Y=M$ and $Y=T$. Both give identical observed $(T,M,Y)$, but under $do(T=1,M=0)$ the outcomes are 0 and 1. Their direct/indirect decompositions differ. Thus the existing protocol-gap inequality does not identify mediation. A dynamic adaptation interpretation needs a separate sequential SCM/identification bridge; the finite one-mediator theorem does not silently supply it.
