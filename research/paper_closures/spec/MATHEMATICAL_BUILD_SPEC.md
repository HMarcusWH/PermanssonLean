# Mathematical build contract: scope and authority

**Source basis:** SRC-030. Exact references and canonical hashes are in the source register; theorem IDs in this chapter denote the new paper derivations.

**Document ID:** `PERMANSSON-PAPER-CLOSURES-1`  
**Date:** 18 October 2026.  
**Repository reference:** `39279799834ae536bda715dedecdc11a32bf6c82`.  
**Status:** new paper derivations and proposed implementation contracts; **not a new Lean-certified release**.

This document develops the mathematics behind all 42 entries in the supplied *Mathematical Closure Atlas*. It does not interpret the atlas as 42 unrestricted universal theorems. Several entries are open-ended research directions. For those, the document selects an explicit first theorem, gives its proof, and records the residual broader question. Every such selection is labelled below. In particular, finite, compact, standard-Borel, first-moment, independence, rectangularity, and property-form assumptions are mathematical hypotheses, not implementation conveniences to omit from the published conclusion.

The theorem identifiers in this document are new **paper-contract identifiers**. Proposed Lean names are not declarations already present in the repository. The signatures are mathematically typed interface contracts, not a claim of compiling Lean syntax. Existing source names are recorded separately in the source register. No placeholder proof may be committed in their place.

## What was actually checked for this document

The live reference was read through the connected GitHub repository. The mathematical files extracted from the supplied source ZIP were checked by reconstructing their Git subtree identities. The frozen-core subtree is `252cae4955bfb8f6440567a5186398bb1967a24c`; the research subtree is `f40d38fd0c0e836f73d4f6f64e66b876ff31fd1c`. Both match the live reference. The source papers and accepted release files match as well. Later maintenance files were not inferred from that older ZIP.

An independent, standard-library Python implementation in this package checks the exact finite arithmetic used below. It does not import the repository's numerical model. Its 27 test methods passed, including repaired-content mutation checks against the supplied table interface. These checks include all eight X1 transition matrices, 144 stochastic rows, 432 dynamic-programming equations, 72 terminal values on the nine comparison starts, the six minima, Cramer stationary examples, residence monitors, and adversarial examples. They are not a universal proof or a Lean run. No fresh Lean compilation was performed for this document.

## Fixed boundaries

The original v0.1.8 core, accepted v0.2.0 manuscript and archive, historical solver files covered by preservation, dependency pins, and existing application schema are inputs, not files to rewrite. Add new mathematical modules under `PermanssonResearch/`; import them explicitly from its root. Extend tests and current nonfrozen crosswalks additively. Never run a dependency update merely to make a proposed proof easier. Changes to a reviewed workflow profile require the hardening workflow's separate reviewed policy process.

Neither the former X1 replete region nor its descriptor is repaired here. Their recorded negative regime result remains true. The new positive economic witness below is a different mathematical instance. The old C10 constructed six-state evidence is not an X1 certificate. The already-proved total C10 Dirichlet/Cramer theorem and bounded-diameter TV-to-dual-$W_1$ estimate are reused, not commissioned again.

## Reading and build order

The immediate implementation unit is Chapters X and S: exact X1 numerical margins, then unrestricted discounted strategies. Chapter M gives an obstruction theorem for strict MA2 in the autonomous subclass, replacing blind witness search with a mathematically testable outcome. Chapters Q and A supply robustness proofs. Chapter D uses one finite-monitor theorem to avoid separately rebuilding each solver variant. Chapters C, B and E cover stationary constructors, general-state limits, grammar, and specialized algebraic transfers.

For each atlas item the machine-readable registry records: selected mathematical scope; paper theorem IDs; source foundations; proposed modules; prerequisites; falsification tests; and residual scope. A row marked `SCOPED_DERIVATION` must never be promoted as an unrestricted closure. All new rows remain `NOT_LEAN_VERIFIED` until the exact source/head/synthetic-merge acceptance process has completed.

# Shared definitions and proof lemmas

## G.1 — The actual process

Let $Y=S\times X$. An action kernel $\alpha:Y\rightsquigarrow A$, world kernel $P:Y\times A\rightsquigarrow X$, and update kernel $U:Y\times A\times X\rightsquigarrow S$ are probability kernels. Their ordered composition is

$$
K((s,x),d(s',x'))=
\int_A \alpha((s,x),da)\,P((s,x),a,dx')\,U((s,x),a,x',ds').
$$

Write $\mathbb P_y^K$ for the existing canonical path law, and $\mathbb P_\mu^K$ for its mixture over an initial probability $\mu$. The finite version replaces integrals by finite sums. All model-specific numerical matrices below must be proved equal to this kernel. Reindexing a finite set by `Fin n` is allowed only with the explicit measurable bijection and corresponding kernel/path transport.

A strategic intervention changes only the permitted strategic primitives. Its physical $P$ is literally the same. Two compared models may have different physical primitives as model uncertainty, but that difference is not relabelled as a within-model strategic intervention.

## G.2 — Original effects and margins

For a frozen metric-valued property $\psi$, write

$$
z_0(y)=\psi(\mathbb P_y^K),\qquad
z_J(y)=\psi(\mathbb P_y^{K^J}),\qquad
\Delta_J(y)=d(z_0(y),z_J(y)),\qquad
\kappa_J=\inf_{y\in B_1}\Delta_J(y).
$$

The original `ConstitutiveComparisonSet` supplies a nonempty measurable $B_1$ and the two-start path-law condition. A singleton whose one trajectory law is random does not supply two different starting laws.

**G-MARGIN — uniform output-error lemma.** Suppose $B_1\ne\varnothing$, all effects are finite, and for every $y\in B_1$,

$$d(z_0(y),\widetilde z_0(y))\le e_0,
\quad d(z_J(y),\widetilde z_J(y))\le e_J.$$

Then $|\widetilde\kappa_J-\kappa_J|\le e_0+e_J$.

**Proof.** Twice applying the triangle inequality gives
$|\widetilde\Delta_J(y)-\Delta_J(y)|\le e_0+e_J$.
Thus every $\widetilde\Delta_J(y)$ is at least
$\kappa_J-e_0-e_J$, proving one infimum inequality. Reverse the roles for the other. Nonnegativity and one finite value ensure both infima exist as real numbers. This is the existing margin perturbation pattern; instantiate it rather than redefine the margin.

**G-MIN — exact finite minimum certificate.** For finite nonempty $B_1$, if $a\le\Delta_J(y)$ at every start and equality holds at $y_*\in B_1$, then $\kappa_J=a$. The lower bound follows by infimum monotonicity; the attaining point supplies the reverse inequality. Both directions are required. Merely displaying an attained value proves only an upper bound on the infimum.

## G.3 — Event total variation and common mass

Use event TV,

$$\operatorname{TV}(\mu,\nu)=\sup_E|\mu(E)-\nu(E)|,$$

not the unhalved $L^1$ norm. For finite probabilities it equals
$\frac12\sum_x|\mu_x-\nu_x|$.

**G-OVERLAP.** If $\xi\le\mu,\nu$ is a common subprobability and $\xi(Y)\ge c$, then $\operatorname{TV}(\mu,\nu)\le1-c$.

**Proof.** The positive measures $\mu-\xi$ and $\nu-\xi$ each have total mass $1-\xi(Y)$. Their difference on any set lies between its negative and positive total masses, proving the bound. No independence assumption is involved.

**G-SCORE.** If $0\le f\le1$ is measurable, then
$|\mu f-\nu f|\le\operatorname{TV}(\mu,\nu)$.
Use the layer-cake representation $f=\int_0^1 1_{\{f>t\}}dt$ and integrate the event bound. A score in $[a,b]$ has factor $b-a$; a merely $|f|\le C$ score has factor $2C$.

## G.4 — Paper proof versus implemented proof

Finite arithmetic constants are certificate data until a Lean proof validates their equations. Python fractions, a true JSON field, a computed eigenvector, a spectral plot, and source hashes do not by themselves establish theorem truth. Analytic ingredients such as completeness of the first-moment probability space, finite linear-program duality, conditional probabilities, and the ergodic theorem are named proof dependencies below. They must be discharged by an existing pinned theorem or a new lemma, not introduced as custom axioms.


\newpage

# X — Exact X1 numerical closure

**Source basis:** SRC-001, SRC-002, SRC-003, SRC-004. Exact references and canonical hashes are in the source register; theorem IDs in this chapter denote the new paper derivations.

**Atlas:** X1-N01, X1-N02, X1-N03. **Scope:** the exact accepted 18-state instance, unchanged.

**Existing foundations:** `X1/Parameters.lean`, `TypedModels.lean`, `Comparison.lean`, `FiniteOutputs.lean`, and `OccupationTargets.lean`. The latter's baseline rational-atom bridge may be reused; do not build a second inconsistent baseline matrix.

## X-DEF — Frozen constants and state order

Use $y=(q_1,q_2,x)$ with $q_i\in\{0,1,2\}$ and $x\in\{0,1\}$, enumerated lexicographically in that order. Actions are $a=(a_1,a_2)\in\{0,1\}^2$.

$$p_x(a)=\min\{1,\max\{0,r_x-(a_1+a_2)/4\}\},
\quad r_0=1/4,\quad r_1=9/10.$$

The actual world draw has mass $p_x(a)$ at 1 and $1-p_x(a)$ at 0. Rewards, discount and baseline values are

$$r_i(x,a)=\frac{x a_i}{2}-\frac{193}{211}a_1a_2-\frac{1-x}{10},
\quad \beta=\frac9{10},\quad
V_i(0)=-\frac{121}{211},\quad V_i(1)=-\frac{81}{211}.$$

E's extraction rate is $x/2$. L's rate for memory $q$ is $(9q+1)/20$, hence exactly $1/20,1/2,19/20$.

Let $\operatorname{clip}(k)=\max(0,\min(2,k))$. The accepted reinforcement update has this equivalent elementary form:

* If $x=0$, memory $q_i$ changes to $\operatorname{clip}(q_i+1-2a_i)$.
* If $x=1$ and $a=(1,1)$, both memories decrement, with clipping.
* If $x=1$ and $a\ne(1,1)$, both memories increment, with clipping.

**Proof of the simplification.** At $x=0$, $r_i-r_{\mathrm{ref}}=-1/20-(193/211)a_1a_2<0$. At $x=1$, a nonextracting player has reward-minus-reference $-1/20$; a sole extractor has $9/20>0$; a joint extractor has $9/20-193/211<0$. Multiplying each sign by $2a_i-1$ gives the stated increments. This proof must connect the simplified function to `updateL`; the function is not a replacement definition of learning.

## X-ATOM — Eight exact kernels

Index the protocol by two flags $(r,u)\in\{0,1\}^2$: restrain current action if $r=1$; reset **next** memory if $u=1$. The four flags are baseline $(0,0)$, action $(1,0)$, update $(0,1)$ and joint $(1,1)$.

Let $\theta_{m,r,i}(y)$ be zero under restraint and the E/L rate otherwise. Put

$$w_{m,r}(y,a)=\prod_{i=1}^2
\theta_{m,r,i}(y)^{a_i}(1-\theta_{m,r,i}(y))^{1-a_i},$$

where implementations should use a Boolean branch rather than ambiguous $0^0$ arithmetic. Let $F_{m,u}(y,a)$ be $(1,1)$ if reset, $q$ for E without reset, and the accepted L update otherwise. Then

$$Q_{m,r,u}(y,(q',x'))=
\sum_{a\in\{0,1\}^2}
 w_{m,r}(y,a)\,1_{\{q'=F_{m,u}(y,a)\}}
\begin{cases}p_x(a)&x'=1,\\1-p_x(a)&x'=0.\end{cases}$$

**Theorem X-ATOM.** Every entry is a nonnegative rational, each row sums to one, and its nonnegative-real cast equals the corresponding actual typed baseline or intervened induced-kernel atom.

**Proof.** Bernoulli masses are nonnegative and sum to one. For each action the deterministic update admits exactly one next memory, and the two world masses sum to one. Summing all next states therefore leaves the product action mass, whose sum is one. For semantic equality, expand the original induced-kernel composition; integrate the finite product action law, the actual Boolean world law and the Dirac update. These are exactly the terms above. For each of `Jaction`, `Jupdate`, `Jjoint`, first unfold `intervention.apply` and use its primitive identity. In particular, reset is not permitted to alter $w_{m,r}$.

**Build.** Add `X1/InterventionNumerics.lean` and `X1/InterventionNumericalBridge.lean`. Export proposed declarations `entry_nonneg`, `entry_sum_one`, `baseline_atom_eq`, `action_atom_eq`, `update_atom_eq`, `joint_atom_eq`. Keep the flag-to-actual-intervention mapping in one exhaustive definition and prove it by cases.

## X-DP — All-horizon rational terminal evaluation

For each of the eight kernels define

$$v_0(y)=x,\qquad v_{t+1}(y)=\sum_z Q(y,z)v_t(z).$$

**Theorem X-DP.** For every natural $t$ and every state $y$,

$$0\le v_t(y)\le1,
\qquad \operatorname{kernelTerminal}(K,t,y)
 =\operatorname{ofReal}((v_t(y):\mathbb R)).$$

Consequently the original time-three property is exactly $(v_3(y):\mathbb R)$.

**Proof.** Probability bounds follow by induction and stochastic row sums. At zero the terminal indicator agrees. At the successor, replace each actual kernel atom using X-ATOM, use the induction hypothesis, and commute finite sums/products with the cast using nonnegativity. The already-proved `baselineProperty_eq_kernelTerminal` completes the original-path-law bridge. This is terminal repletion: do not insert killing at intermediate times.

## X-TABLE — Reflection without an exponential proof term

The certificate JSON supplies $8\times4\times18=576$ rational values. Treat them as a candidate table $T(k,t,y)$, not as the definition of $v$. Check the 144 initial indicator entries and 432 successor equations, then prove uniqueness of the recurrence by induction to obtain $T=v$. This avoids expanding every length-three path repeatedly inside each margin proof.

A Lean checker may use ordinary kernel-reduced `decide`, explicit finite case elimination, and rational normalization. It must not use `native_decide`, a custom axiom, or an unchecked native executable. Generated proof files must import the semantic bridge, not merely certify an isolated arithmetic table.

The file `certificates/x1_exact_tables.json` gives **all** matrices, values, effects and attaining starts. Its accompanying checker generates it deterministically from the constants above. It is build input data, not theorem evidence until Lean checks it.

## X-MARGIN — Six exact original margins

The comparison set is the nine states with $x=1$. For each protocol set
$e(y)=v^J_3(y)-v^0_3(y)$. The exact table proves $e\ge0$ for every action/joint effect and every L update effect; E update effects are all zero. Hence absolute and signed effects agree in these cases.

The targets are:

| Generator | Action | Update | Joint |
|---|---:|---:|---:|
| E | $\frac{271}{800}$ | $0$ | $\frac{271}{800}$ |
| L | $\frac{3010663529}{6400000000}$ | $\frac{1244820951}{25600000000}$ | $\frac{3010663529}{6400000000}$ |

E ties at all nine starts. L's action/joint minimum is attained uniquely at $((0,0),1)$; its update minimum is attained uniquely at $((2,2),1)$.

**Proof.** Reflect all 54 effect values from X-TABLE. Apply G-MIN using the complete nine-element set and the displayed attaining states. Use `constitutiveEffect_eq_finiteEffect` and `constitutiveMargin_eq_finiteInf` to rewrite the original margin, then cast the rational inequalities and equality. Uniqueness of attainers is a separately checkable finite statement, not needed for margin existence but useful for mutation tests.

**Sanity derivations.** For E, the world transition sends a replete probability $p$ to $1/4+(2/5)p$. Thus $p_3=227/500$ from a replete start. All-restrain sends $p$ to $1/4+(13/20)p$, giving $\frac{3171}{4000}$. Their difference is $\frac{271}{800}$. E memory reset cannot change this world recursion. Under L reset, after the first step the rates are $\frac{1}{2}$ each, giving world recursion $p\mapsto1/16+(47/80)p$; the first-step distribution still depends on the original memory. The certificate checks that dependence rather than resetting it prematurely.

**Proposed final declarations.** In `X1/ExactMargins.lean`, export `equilibrium_action_margin`, `equilibrium_update_margin`, `equilibrium_joint_margin`, `learner_action_margin`, `learner_update_margin`, `learner_joint_margin`. Each left side must be the original `constitutiveMargin` applied to `model`, `specification`, `family`, `property`, `comparisonSet`, and the corresponding existing intervention. Their right sides are real casts of the exact rationals above.

**Falsifiers.** Alter a world probability, use the new rather than old world in learning, reset current memory before choosing action, swap action/update flags, change horizon, drop an attaining start, or change one table literal. The appropriate semantic/table/minimum theorem must then fail. The already-proved one-step retention $13/20<1$ and `replete_not_exactGR` remain intact. A positive margin is not a replacement for Exact GR.


\newpage

# S — Unrestricted discounted-strategy verification

**Source basis:** SRC-005. Exact references and canonical hashes are in the source register; theorem IDs in this chapter denote the new paper derivations.

**Atlas:** X1-S01. **Selected scope:** finite state/action stochastic games; both X1 players; arbitrary nonanticipating behavioral unilateral action deviations with the opponent's baseline policy fixed. Full observed history may be used. No concurrent opponent action, future noise or changed world kernel may be observed or selected by the deviator.

## S-TRACE — Construct the right probability space

A canonical state path does not itself record the realized joint actions on which rewards depend. Use the alternating histories

$$H_t=(Y_0,A_0,Y_1,\ldots,A_{t-1},Y_t).$$

Given a behavioral rule $\sigma_t(da_i\mid H_t)$, sample the opponent independently with law $\pi_{-i}(da_{-i}\mid Y_t)$, then the actual $P$ and the declared strategic update $U$. This defines a finite trace kernel. Iterating it gives consistent finite trace laws; the infinite law is their canonical extension. The marginal state-prefix law for a Markov baseline agrees with the existing original law, proved by finite-prefix induction and uniqueness. Do not merely write a reward function on a state path that has lost the required action.

A private random seed is covered when independent of future/opponent random draws: conditioning on the observed/own-information history induces a behavioral distribution. A seed correlated with current opponent randomness is a different information structure. Additional private memory may organize a deviation, but cannot directly modify $P$ or another player's primitives.

## S-VERIFY — Finite-game verification theorem

Fix player $i$, $0\le\beta<1$, bounded reward $|r_i(y,a)|\le R$, and bounded candidate value $|V_i(y)|\le C$. Suppose for every state and own pure action,

$$V_i(y)\ge \sum_{a_{-i}}\pi_{-i}(a_{-i}\mid y)
\left[r_i(y,(a_i,a_{-i}))+
\beta\int V_i(y')K(dy'\mid y,(a_i,a_{-i}))\right].$$

Assume equality after averaging the candidate own policy $\pi_i$.
Then, for every initial law $\mu$ and admissible behavioral history rule $\sigma$,

$$J_i^\sigma(\mu)=
\mathbb E_\mu^\sigma\sum_{t=0}^\infty\beta^t r_i(Y_t,A_t)
\le\int V_i\,d\mu
=J_i^\pi(\mu).$$

**Proof in implementable lemmas.**

1. Convex combinations of the pure inequalities give the same inequality for the actual conditional law $\sigma_t(\cdot\mid H_t)$ at each history.
2. Conditional on $H_t$, the action/world/update factorization gives
$\mathbb E[r_t+\beta V_i(Y_{t+1})\mid H_t]\le V_i(Y_t)$.
This is an equality under $\pi$.
3. Multiply by $\beta^t$, integrate, and sum over $t<n$. Adjacent value terms cancel:

$$\mathbb E\sum_{t<n}\beta^t r_t+
\beta^n\mathbb E V_i(Y_n)\le\mathbb E V_i(Y_0).$$

4. The terminal term has absolute value at most $C\beta^n$. The payoff series converges absolutely on every trace, with uniform tail bound
$R\beta^n/(1-\beta)$. Thus expectation commutes with its limit by that explicit uniform bound. Send $n\to\infty$; equality for the candidate gives attainment.

This is not restricted to stationary or Markov deviations. Nonanticipation is used in Step 2. No interchange of a supremum with an infinite horizon is required: the same bound holds for every individual policy, and the baseline attains it.

## S-X1 — Stronger exact performance-difference identity

In the accepted X1 instance the one-shot loss is not just nonnegative. Direct expansion of the eight player/state/action cases gives

$$V_i(x)-Q_i(x,a_i)=\frac9{211}\,1_{\{x=0,\ a_i=1\}}.$$

For $x=1$ both own pure actions are indifferent against the fixed half-extracting opponent. At $x=0$ restraining has zero loss and extraction loses $\frac{9}{211}$.

Therefore the preceding telescoping proof gives the exact identity

$$\boxed{
J_i^\sigma(y)=V_i(x)
-\frac9{211}\,
\mathbb E_y^\sigma\sum_{t=0}^\infty
(9/10)^t1_{\{X_t=0,A_{i,t}=1\}}.}
$$

For X1 use the simple reward bound $R=2$ and $C=1$; every source reward and candidate value satisfies them. Thus the generic payoff tail is at most $20(9/10)^n$. The identity proves optimality for both indexed players and every memory/world start. It also characterizes equality: the nonnegative discounted extraction-in-depletion sum has expectation zero. Actions in a replete state can differ from the candidate without improving its value. Do not infer uniqueness of equilibrium or uniqueness of best response.

**Build decomposition.** `StrategicWorld/ActionTrace.lean` supplies trace laws and state-marginal transport. `Games/DiscountedVerification.lean` supplies the finite-horizon telescoping and infinite payoff theorem. `X1/FullStrategyCertificate.lean` proves the exact advantage table and instantiates the general theorem. The generic theorem is about scalar expected discounted rewards; a risk-sensitive or adversarially correlated payoff criterion is a separate target.

**Tests.** Exhaust both players and all pure state-dependent deviations; compare finite trace enumeration with telescoping including the terminal correction. A time-dependent deviation must be accepted as admissible and satisfy the bound. A wrong discount, altered payoff/world row, reward evaluated from missing actions, or information access to the current opponent draw must not receive this certificate. Neither this theorem nor X1-N03 changes the failed replete-region Exact-GR conclusion.


\newpage

# M — Strict MA2: an autonomy obstruction, not another recording toy

**Source basis:** SRC-008, SRC-009, SRC-010. Exact references and canonical hashes are in the source register; theorem IDs in this chapter denote the new paper derivations.

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


\newpage

# Q — Shared-mass proofs and quantitative transport

**Source basis:** SRC-027, SRC-025, SRC-026. Exact references and canonical hashes are in the source register; theorem IDs in this chapter denote the new paper derivations.

**Atlas:** E1-G01, A2-P01, A2-P02, E1-P01, E1-P02.

## Q-LIFT — Lift a common projected subkernel

Let $q:Y\to Z$ be measurable, $K:Y\rightsquigarrow Y$ and $\bar K:Z\rightsquigarrow Z$ Markov. Put
$P_y=q_\#K_y$ and $B_y=\bar K_{q(y)}$.
Assume a measurable common subkernel $M_y\le P_y,B_y$ with
$M_y(Z)\ge1-\eta$, $0\le\eta\le1$.
Assume the measurable kernel Radon--Nikodym machinery needed to choose jointly measurable
$r(y,z)=dM_y/dP_y$ exists. The finite case always satisfies this. A sufficient general profile is countably generated coarse target sigma-algebra with the corresponding source kernel RN instance; standard-Borel $Z$ is a familiar sufficient choice.

Clip the RN density to $[0,1]$ without changing it $P_y$-a.e. Define

$$R_y(dy')=r(y,q(y'))K_y(dy').$$

Then $R$ is a measurable subkernel, $R\le K$, $q_\#R_y=M_y$, and $R_y(Y)\ge1-\eta$.

**Proof.** Joint measurability survives composition with $(y,y')\mapsto(y,q(y'))$. The clipped density is between zero and one, proving domination. For every measurable $E\subset Z$, change variables under pushforward:

$$R_y(q^{-1}E)=\int_E r(y,z)P_y(dz)=M_y(E).$$

At $E=Z$ obtain the mass bound. The proof uses a density on the **coarse** space and does not need disintegration over fibres of $q$ or a Markov assumption for the projected fine process.

For finite spaces there is a directly computable formula:

$$R(y,y')=K(y,y')
\frac{\min\{P_y(q(y')),\bar K(q(y),q(y'))\}}{P_y(q(y'))},$$

with ratio zero when the denominator is zero. All fine atoms in that zero-mass fibre already vanish, so the convention preserves equality after projection.

**Implementation dependency.** Reuse `PermanssonLean.ProbabilitySupport.commonPartKernel` and its mass/domination facts where its `CountableOrCountablyGenerated` instance is available. Add the lifted-density lemma in the research library. The older countability-free E1 linear result remains unchanged. Do not attach the new geometric result to unrestricted measurable spaces merely because the linear theorem has that generality.

## Q-GEOMETRIC — Projected-prefix geometric error

Let $\mathbb P_y$ and $\bar{\mathbb P}_{q(y)}$ be the actual path laws. Under Q-LIFT,

$$\operatorname{TV}\!\left(q^{0:T}_\#\mathbb P_y^{0:T},
\bar{\mathbb P}_{q(y)}^{0:T}\right)
\le 1-(1-\eta)^T.$$

**Proof.** Build a subprobability $\xi_T$ on fine histories by starting with the original Dirac law and iterating $R$ rather than $K$. Its total mass is at least $(1-\eta)^T$: at each extension the conditional retained mass is at least $1-\eta$. Also $\xi_T\le\mathbb P_y^{0:T}$ by domination at each step.

Let $\theta_T=q^{0:T}_\#\xi_T$. At zero $\theta_0$ is the coarse Dirac start. Suppose $\theta_T\le\bar{\mathbb P}^{0:T}$. Extend a fine history and project. Q-LIFT bounds its projected next subkernel by $\bar K$ evaluated at the last projected state. Integration and monotonicity show the extended projected history law is bounded by extension of $\theta_T$ with $\bar K$, and hence by the actual coarse prefix law. Thus $\theta_T$ is a common submeasure of the two compared prefix laws, with mass at least $(1-\eta)^T$. Apply G-OVERLAP.

This is the missing multiplicative argument. It does **not** assert the unsupported recurrence $\delta_{T+1}\le(1-\eta)\delta_T+\eta$ solely from the old hybrid TV calculation. The recursive object is retained common mass, not the actual TV error.

The same argument with time-varying bounds gives
$1-\prod_{t<T}(1-\eta_t)$. With an initial common mass at least $1-\varepsilon_0$, it gives
$1-(1-\varepsilon_0)\prod_{t<T}(1-\eta_t)$.

**Build:** `Probability/ProjectedCommonSubkernel.lean`, `Quotient/GeometricPrefix.lean`, and `Quotient/GeometricMargin.lean`. Export separate finite and RN-hypothesis wrappers. Instantiate G-MARGIN with $L_\psi$ times the baseline and intervention geometric budgets. Preserve source label matching and the complete original comparison sets.

## Q-PRIMITIVE — Sequential product bound for alpha/P/U

**Atlas:** A2-P01. For two typed models at the same starting state, suppose measurable common subkernels exist for each primitive pair with retained masses at least
$1-\delta_\alpha$, $1-\delta_P$, $1-\delta_U$, uniformly on the required inputs. Define their ordered sub-Markov composition using the actual action/world/update order.

It is dominated by each full induced kernel, because all factors are nonnegative and each subkernel is dominated by its corresponding primitive. Iterated integration gives retained mass at least the product. Therefore

$$\operatorname{TV}(K_y,\widetilde K_y)
\le1-(1-\delta_\alpha)(1-\delta_P)(1-\delta_U).$$

**Proof detail.** Integrating the update subkernel first gives at least $1-\delta_U$ at every previous input. Integrating the world subkernel gives an additional factor $1-\delta_P$; integrating action gives $1-\delta_\alpha$. This is a lower bound from uniform conditional masses, not independence of three error events. Shared model-dependent noise is allowed to the extent it is represented by the stated ordered kernels.

All primitive errors are in $[0,1]$. Their off-graph completions and intervention-reachable rows belong to the hypotheses. A changed $P$ here is a comparison between models, not a within-model intervention. The existing additive primitive bound remains useful when it requires weaker measurable machinery.

## Q-LOCAL — Initial-law and localized row budgets

**Atlas:** A2-P02. For two finite or measurable history kernels $K_t,\widetilde K_t$ on the same history type, let $\mu_t$ be the actual first process's prefix law. If $d_t(h)$ bounds row event TV, then

$$\operatorname{TV}(\mu_T,\widetilde\mu_T)
\le \min\left\{1,\varepsilon_0+
\sum_{t<T}\int d_t(h)\,\mu_t(dh)\right\},$$

where $\varepsilon_0$ bounds initial-law TV.

**Proof.** Insert the hybrid obtained by applying $\widetilde K_t$ to $\mu_t$. The first discrepancy is at most the $\mu_t$-average row defect, by integrating the row event inequalities for the measurable sections of each joint event. The second is at most the previous prefix TV by contraction under a common probability kernel. Induct and cap at one.

If row defects are at most $\eta_t$ on a declared good-history set $E_t$ and at most one elsewhere, the average row defect is bounded by
$\eta_t+\mu_t(E_t^c)$. Reachability information can therefore reduce a budget **only with a quantitative visit/exit bound**. Repeat the analysis separately under baseline and intervention laws; baseline unreachability does not imply intervention unreachability.

For reported numerical outputs satisfying pointwise errors $b_0,b_J$, append those reporting errors using G-MARGIN. Do not put them into the true model's definition of $\kappa$.

## Q-DISCOUNT — A useful whole-path class

**Atlas:** E1-P01. Let
$f(\omega)=\sum_{t\ge0}w_t g_t(\omega_{0:t})$ with
$w_t\ge0$, $\sum_t w_t<\infty$, and $0\le g_t\le1$. The series is uniformly absolutely convergent. If prefix errors are bounded by $e_t$, then

$$|\mathbb E f-\widetilde{\mathbb E} f|\le\sum_t w_t e_t.$$

**Proof.** Apply G-SCORE to each finite term, sum finitely, then use the deterministic tail bound $\sum_{t\ge n}w_t$ for each law.

For normalized discounted state scores, $w_t=(1-\beta)\beta^t$, $0\le\beta<1$, matched starts, and Q-GEOMETRIC,

$$\boxed{
|\mathbb E f-\widetilde{\mathbb E} f|
\le\frac{\beta\eta}{1-\beta(1-\eta)}.}
$$

Indeed $(1-\beta)\sum_t\beta^t[1-(1-\eta)^t]$
is the difference of two geometric sums. The $t=0$ error is zero. With initial mismatch $\varepsilon_0$, the bound becomes
$1-(1-\varepsilon_0)(1-\beta)/(1-\beta(1-\eta))$.

A different useful theorem assumes summable time-varying defects. Prefix common masses then give a full-product-law TV bound
$1-(1-\varepsilon_0)\prod_{t\ge0}(1-\eta_t)$.
To justify the full-law step, finite-coordinate events form an algebra generating the product sigma-algebra; approximate an event in the sum of the two finite probability measures by that algebra and pass its error to zero. With constant positive error the product lower bound vanishes, correctly giving only the trivial bound one.

Exact infinite survival is outside the summable-score class. An arbitrarily small recurring leak can change its probability from one to zero. Do not use Q-DISCOUNT to certify that tail indicator.

## Q-REGIME — Conditional transfer with the missing gates supplied

**Atlas:** E1-P02. Fix the original fine/coarse specifications, type-respecting map, compatible comparison sets, matched intervention labels and grounded property factorization. Suppose independent certificates establish each model's original Exact-GR and any requested confirmatory/grounding gates. Suppose Q-GEOMETRIC or the existing linear theorem gives a margin-error bound $e$.

Then $\kappa_{\mathrm{fine}}>e$ implies positive coarse margin, and $\kappa_{\mathrm{coarse}}>e$ implies positive fine margin. Combining the corresponding positive margin with the **independent** regime and grounding certificates gives the original uniform-PR conclusion on that side.

**Proof.** G-MARGIN gives $\kappa_{\mathrm{coarse}}\ge\kappa_{\mathrm{fine}}-e$ and conversely. Apply the existing original positive-margin-to-uniform-constitution theorem, then the appropriate regime constructor.

This is not an equivalence of bare positivity when $e>0$, and it is not a proof of either Exact-GR certificate from a small quotient defect. A separate support-invariance premise may establish coarse invariance; a separate ergodic theorem may establish its occupation target. Distinct targets must not be relabelled as the same $\nu$. The old leakage counterexample is an acceptance test for this theorem's hypothesis list.


\newpage

# A — Deriving the long-run robustness inputs

**Source basis:** SRC-023, SRC-020, SRC-021. Exact references and canonical hashes are in the source register; theorem IDs in this chapter denote the new paper derivations.

**Atlas:** A3-K01, A3-I01, A3-C01, A3-F01, A3-P01. These are related, but the dependency graph is not a single compulsory chain. In particular, the finite occupation factorization and a directly dual contraction proof do not require general Polish Kantorovich--Rubinstein duality.

## A-KR-FIN — Finite coupling/dual equality

On a finite metric space $(Y,d)$ and probability vectors $\mu,\nu$, define

$$W(\mu,\nu)=\min_{\gamma\ge0}
\left\{\sum_{ij}d(i,j)\gamma_{ij}:
\sum_j\gamma_{ij}=\mu_i,\quad\sum_i\gamma_{ij}=\nu_j\right\}.$$

Then

$$W(\mu,\nu)=\max_{\operatorname{Lip}(f)\le1}
\sum_i f(i)(\mu_i-\nu_i).$$

The finite test functions are bounded, so this is exactly the finite interpretation of the existing `W1DualLE` predicate, with absolute values handled by $f\mapsto-f$.

**Proof without assuming a transport-duality oracle.** The coupling polytope is nonempty (use $\mu\otimes\nu$), closed and bounded, so a minimizing $\gamma$ exists. Form the finite residual bipartite graph. A forward edge from source $i$ to target $j$ costs $d(i,j)$. A reverse edge from target $j$ to source $i$ is present when $\gamma_{ij}>0$ and costs $-d(i,j)$. A negative residual cycle would permit adding a sufficiently small flow around that cycle, preserving every row/column sum and strictly lowering cost. It therefore cannot exist.

Add a super-source with zero-cost edges to all vertices. Shortest path values $h$ exist: every path can have nonnegative cycles removed, leaving a simple path in a finite graph. For each residual edge $u\to v$, $h(v)\le h(u)+c(u,v)$. Set $u_i=-h(\mathrm{source}\ i)$ and $v_j=h(\mathrm{target}\ j)$. Then $u_i+v_j\le d(i,j)$, with equality wherever $\gamma_{ij}>0$ because the reverse edge also exists. Hence

$$\sum_i\mu_i u_i+\sum_j\nu_jv_j=\sum_{ij}\gamma_{ij}d(i,j).$$

Put $f(i)=\min_j[d(i,j)-v_j]$. The triangle inequality makes $f$ 1-Lipschitz, $f\ge u$, and $f(j)\le-v_j$ by using the diagonal term. Thus the displayed transport cost is at most $\mu f-\nu f$. Conversely, any 1-Lipschitz $f$ satisfies $f(i)-f(j)\le d(i,j)$, so its expectation difference is bounded by the cost of every coupling. The bounds coincide.

**Build:** finite coupling arrays, residual cycles, minimum simple paths, and the dual predicate bridge. Rational input distances/masses admit rational optimum certificates. A constructive vertex-enumeration method is described in D-LP below; the abstract existence proof above does not require a Python optimizer.

## A-KR-POLISH — First-moment extension

**Selected larger scope:** complete separable metric $Y$, its Borel sigma-algebra, and $\mu,\nu$ with finite first moments. Coupling $W_1$ is the infimum of expected distance over couplings. Then

$$W_1(\mu,\nu)\le c\quad\Longleftrightarrow\quad
\operatorname{W1DualLE}(\mu,\nu,c).$$

**Proof.** The weak direction follows by integrating $|f(x)-f(y)|\le d(x,y)$ against a coupling for each bounded 1-Lipschitz test.

For the reverse direction, fix a base point. For every $n$, choose a finite measurable quantization map $T_n$ such that

$$e_n=\int d(y,T_ny)(\mu+\nu)(dy)\longrightarrow0.$$

Construct it by tight approximation for the finite weighted measure $(1+d(y,y_0))(\mu+\nu)$, cover the chosen compact set by finitely many small balls, use the first ball in a fixed order, and send the complement to $y_0$. The weighted outside mass and ball radius bound the error.

Apply finite duality to $(T_n)_\#\mu,(T_n)_\#\nu$. Extend a finite optimal potential to $Y$ by the McShane minimum of $f(c_i)+d(y,c_i)$ and truncate to a finite interval containing all its values at the centers. This preserves 1-Lipschitzness, is Borel and bounded, and agrees at the centers. Its finite expectation difference is at most the assumed dual bound plus $e_n$.

Lift a finite optimal coupling to the original cells using their normalized restricted measures; cells of zero mass carry no positive coupling coefficient. The triangle inequality bounds its original cost by the finite cost plus another $e_n$. Therefore $W_1(\mu,\nu)\le c+2e_n$, and sending $n\to\infty$ proves the claim. A general optimal coupling need not be constructed for this inequality. The product coupling has finite cost, so no infinite-minus-infinite rearrangement occurs.

**Proof obligations:** weighted tightness, measurable finite quantization, finite conditional cell normalization, integrable cost, McShane extension/truncation and finite duality. These should be separate lemmas with explicit types. Do not claim the arbitrary-sigma-algebra source theorem already supplies these assumptions. A fixed common supnorm-one test class is not substituted for all individually bounded 1-Lipschitz tests.

## A-COMPLETE — Completeness needed for a fixed point

The first-moment probability space on a complete separable metric space is complete for $W_1$.

**Proof construction.** From a Cauchy sequence choose a subsequence with successive $W_1$ distances at most $2^{-k-2}$. Choose successive couplings with expected distance at most $2^{-k-1}$. Standard-Borel conditional kernels glue them into a joint sequence $(Z_k)$ with the prescribed marginals. The expected sum of distances is finite, so the sum is finite almost surely. Completeness of $Y$ gives a limit $Z$. The tail sum bounds $\mathbb E d(Z_k,Z)$ and tends to zero. The triangle inequality with $Z_0$ gives a finite first moment for $Z$. Its law is the $W_1$ limit of the subsequence, and the Cauchy property gives convergence of the whole sequence.

The gluing uses conditional kernels; it is a named analytic dependency, not permission to postulate a coupling with all marginals without constructing it. A finite-space implementation can instead use the closed probability simplex and requires none of this general-state machinery.

## A-CONTRACT — Derive the encoded dual contraction directly

**Atlas:** A3-C01. If for all $x,y$ and every bounded measurable 1-Lipschitz $f$,

$$|Kf(x)-Kf(y)|\le\rho d(x,y),\quad\rho\ge0,$$

then $K$ satisfies the existing `IsW1Contraction K rho`.

**Proof.** For $\rho>0$, $Kf/\rho$ is a bounded measurable 1-Lipschitz test. Apply the supplied input dual bound and multiply by $\rho$; kernel integration identifies $\mu(Kf)=(\mu K)f$. For $\rho=0$, $Kf$ is constant and the expectation difference is zero. This argument establishes the source predicate for **all** probability laws and all real admissible input bounds, not just measures with finite first moments.

A measurable row coupling with expected distance at most $\rho d(x,y)$ supplies the displayed premise by integrating the Lipschitz inequality. A shared-noise random map $F(x,\xi)$ with
$\mathbb E d(F(x,\xi),F(y,\xi))\le\rho d(x,y)$ is one explicit certificate.

For a finite discrete metric, $W_1=\operatorname{TV}$ and the Dobrushin coefficient
$\max_{x,y}\operatorname{TV}(K_x,K_y)$ supplies contraction. A Doeblin minorization $K_x\ge\varepsilon\lambda$ gives coefficient at most $1-\varepsilon$. On a different finite metric with minimum nonzero distance $\ell$ and diameter $D$, the simple TV route gives at best $\rho=D(1-\varepsilon)/\ell$; it is useful only when this is below one. Do not erase this metric factor.

## A-INVARIANT — Existence, uniqueness and convergence

**Atlas:** A3-I01. Assume $K$ maps first-moment probabilities to first-moment probabilities and is $W_1$-contractive with $0\le\rho<1$. Then there is a unique invariant probability in that class, and

$$W_1(\mu K^n,\pi)\le\rho^nW_1(\mu,\pi).$$

**Proof.** Let $\mu_n=\delta_{y_0}K^n$. Adjacent distances are at most $\rho^nW_1(\delta_{y_0},\delta_{y_0}K)$, so their geometric tail makes the sequence Cauchy. A-COMPLETE gives a limit $\pi$. Contraction makes the action of $K$ continuous, so $\pi K=\pi$. Two invariant laws have distance at most $\rho$ times their distance, forcing equality. Iteration proves the stated convergence.

One sufficient moment condition is that each row is in the first-moment class and
$W_1(K_x,K_{y_0})\le\rho d(x,y_0)$, with $\int d(y,y_0)K_{y_0}(dy)=b<\infty$. Coupling and the triangle inequality give
$\int d(y,y_0)K_x(dy)\le\rho d(x,y_0)+b$, then integrate against $\mu$.

Apply this independently to $K$ and $\widetilde K$ when both invariants are to be generated automatically. The old perturbation theorem requires only the baseline to contract **if** an invariant of $\widetilde K$ is separately supplied. A small row defect alone does not prove uniqueness for the perturbed kernel: perturb the mixing two-state kernel with off-diagonal entries $\varepsilon$ to the identity, changing every row by only $\varepsilon$ while creating multiple invariant laws.

## A-FACTOR-FIN — Four actual occupation-property factorizations

**Atlas:** A3-F01. This is an explicit property subclass, not a derivation for every arbitrary `RegimePropertyMap`. Let the four actual finite kernels have a unique recurrent class, and let $h:Y\to V$ be a finite descriptor. Existing C2 results give, for every initial law, almost-sure empirical occupation convergence to the unique invariant law of each kernel, and hence to its descriptor image.

Define once, before comparison, the measurable descriptor-occupation limit map $L_h(\omega)$, with a fixed default law when the empirical sequence does not converge. For finite $V$, measurability follows from the coordinatewise Cauchy criterion; limits remain in the closed probability simplex. Let $\Phi$ be a continuous Lipschitz real functional on that simplex. It is bounded by compactness. Define the original full-path property

$$\psi(\Lambda)=\int \Phi(L_h(\omega))\,\Lambda(d\omega).$$

For each of the four actual path laws, $L_h=h_\#\pi$ almost surely. Therefore
$\psi(\mathbb P_y)=\Phi(h_\#\pi)$ for every comparison start. This proves all four components of the existing `hfac` premise instead of assuming them. Combine with the independently generated contractive perturbation bundles and the old `occupationMargin_robust` theorem.

No general KR theorem is needed for this finite factorization. No factorization is inferred for survival, a time-zero property, or another frozen property. Existing original `RegimePropertyMap` places no blanket measurability restriction on arbitrary functionals; the measurability above is what licenses this particular integral construction.

## A-FACTOR-REGEN — A nonfinite sufficient profile

For a standard-Borel/Polish model with $K=\varepsilon\lambda+(1-\varepsilon)R$, $0<\varepsilon\le1$, regenerate by independent Bernoulli coins at every transition. The invariant law is explicitly

$$\pi=\varepsilon\sum_{n\ge0}(1-\varepsilon)^n\lambda R^n.$$

Its mass is one; shifting the geometric series shows $\pi K=\pi$. After the first regeneration, blocks are iid, have geometric lengths with mean $1/\varepsilon$, and finite expected absolute reward for any bounded observable. The iid strong law for block lengths and rewards gives time-average limit $\pi f$. The unfinished terminal block is negligible: for iid integrable block length/reward, the $n$th block magnitude divided by $n$ tends to zero, using the summable tail bound and Borel--Cantelli. The finite initial block is negligible almost surely.

Apply this to a countable convergence-determining bounded-continuous class to obtain weak empirical convergence. To obtain $W_1$ empirical convergence on an unbounded descriptor, additionally prove an integrable regenerative first-moment condition and apply the same law to the distance and its truncations. This supplies tail uniform integrability; weak convergence alone is insufficient. A bounded Borel $\Phi$ continuous for the resulting limit topology then yields the same full-path factorization. To instantiate the old margin theorem, $\Phi$ must also satisfy its exact dual-Lipschitz predicate; a functional defined only on first-moment laws is not automatically a function with that global source property.

## A-PRIMITIVE — Typed metric error budgets

**Atlas:** A3-P01. Give $Y=S\times X$ metric $a\,d_S+b\,d_X$, $a,b>0$. Suppose action-law error is bounded in coupling $W_1$ by $\delta_\alpha$; world-law error at fixed $(y,a)$ by $\delta_P$; and update-law error at fixed $(y,a,x')$ by $\delta_U$. Suppose the chosen reference world is $L_{Pa}$-Lipschitz in action, and reference update is separately $L_{Ua}$-Lipschitz in action and $L_{Ux}$-Lipschitz in next world. Require measurable conditional couplings, or use the finite implementation where they can be explicitly selected.

Sequential coupling gives

$$\boxed{\delta_K\le
 a\delta_U+(b+aL_{Ux})\delta_P+
 [aL_{Ua}+(b+aL_{Ux})L_{Pa}]\delta_\alpha.}$$

**Proof.** Couple actions with mean distance approaching $\delta_\alpha$. Conditional world distance is at most $\delta_P+L_{Pa}d_A$. Conditional strategic-update distance is at most $\delta_U+L_{Ua}d_A+L_{Ux}d_X$. Integrate and form $a d_S+b d_X$. Approximate couplings introduce arbitrarily small positive errors, which are removed by taking the infimum. With actual optimal finite couplings no limiting error is needed.

For same-model contraction, suppose the corresponding old-state Lipschitz constants are $L_\alpha,L_{Py},L_{Uy}$. The same derivation gives sufficient factor

$$\rho=aL_{Uy}+(b+aL_{Ux})L_{Py}
+[aL_{Ua}+(b+aL_{Ux})L_{Pa}]L_\alpha.$$

Prove $\rho<1$ for the intended model; do not merely name it a contraction. An easier bounded-diameter route already exists: reuse `W1DualLE.of_eventTV` and A2's actual primitive TV bound. No unrestricted TV-to-$W_1$ conversion is valid on unbounded metrics.

**Final A3 build order.** Implement A-CONTRACT and finite A-FACTOR first using existing dual/C2 machinery. Implement finite KR and the stationary constructor in parallel. Add A-COMPLETE/A-KR-POLISH only when the first-moment space and measurable coupling lemmas have been checked against the pinned library. The complete general-state wrappers carry these extra hypotheses explicitly; they do not replace the wider, already valid conditional dual theorem.


\newpage

# D — One finite-monitor theorem and its solver consequences

**Source basis:** SRC-012, SRC-013, SRC-014. Exact references and canonical hashes are in the source register; theorem IDs in this chapter denote the new paper derivations.

**Atlas:** D2-R01 and D2-P01 through D2-P09. The selected finite contracts below are new paper derivations. They reuse the existing genuine finite-history laws and D2 event bridges. They do not enlarge a policy's information silently, and a time-dependent controller is not relabeled as one frozen strategic intervention.

## D-MONITOR — Sufficient finite summaries

Let $Y$ be a nonempty finite state space, $C(y)$ a nonempty finite admissible control set, and $K_c(y,z)$ rational stochastic rows. Fix horizon $N$. A finite monitor has state $s\in S$, initial state $s_0=i(y_0)$, deterministic updates

$$s_{t+1}=u_t(s_t,y_t,c_t,y_{t+1}),$$

and bounded terminal reward $r(y_N,s_N)$. Dependence on the chosen control may be omitted for a state-event monitor. Define

$$V_N(y,s)=r(y,s),$$

$$V_t(y,s)=\max_{c\in C(y)}\sum_zK_c(y,z)
 V_{t+1}\bigl(z,u_t(s,y,c,z)\bigr),\quad 0\le t<N.$$

Then $V_0(y,i(y))$ is the supremum of expected terminal reward over **all nonanticipating behavioral full-history policies**, and an admissible deterministic policy depending only on $(t,y,s)$ attains it. For rational data, every $V_t$ is rational and a fixed tie-breaking order selects a deterministic rationally computable maximizer.

**Proof.** Construct the actual finite chronological state/control law by multiplying policy probabilities and controlled rows. Its monitor pushforward is obtained by the stated deterministic recursion; prove this by induction on prefix length. At a history ending in $(y,s)$, the conditional expectation of the terminal reward is bounded inductively by

$$\sum_{c\in C(y)}\sigma_t(c\mid H_t)
 \sum_zK_c(y,z)V_{t+1}(z,u_t(s,y,c,z))\le V_t(y,s).$$

This uses only convex averaging and finiteness; the behavioral probabilities may be real, not just rational. A maximizing control at every $(t,y,s)$ gives equality inductively. The initial law version follows by integration. Histories having zero probability need no conditional-probability division: define their continuation by the same policy kernels and prove the unconditional finite-sum recursion first.

**Source bridge.** For deterministic state-history policies, identify this law with the existing `HistoryPolicy`/partial-trajectory law by equality of initial state and all selected transition rows. Then specialize the monitor reward and reuse `ResidenceValue`'s literal-event identity. Do not define the event as “whatever the Bellman evaluator returns.”

**Build:** `ReverseSolver/FiniteMonitor.lean`, `MonitorHistoryBridge.lean`, `BehavioralFinitePolicy.lean`, `MonitorOptimality.lean`. Export `monitor_probability_eq_history_probability`, `monitor_value_dominates_behavioral_history`, and `monitor_deterministic_maximizer_attains`. This closes D2-P01 for the ordinary single-model finite expected objective, independently of compact residence reduction.

## D-RESIDENCE — Exact compact state for the accepted retryable objective

**Atlas:** D2-R01. Freeze target $G$, entry deadline $T$, and duration $m$ measured in **transitions after entry**. Observe through $N=T+m$. The event remains

$$\exists e\le T\;\forall j\le m:\;Y_{e+j}\in G.$$

Use a current streak $k\in\{0,\ldots,m+1\}$ and a completed flag $b$. Initialize

$$k_0=\mathbf1_G(y_0),\qquad b_0=\mathbf1\{k_0=m+1\}.$$

For a new observation $z$, set

$$k'=\begin{cases}\min(m+1,k+1)&z\in G,\\0&z\notin G,\end{cases}
\qquad b'=b\lor(k'=m+1).$$

Terminal reward is $b_N$. At a fixed original horizon, $(t,y,k,b)$ is sufficient. A reachable-state implementation may suppress $k$ once $b$ is true, but its decoding must preserve the monitor semantics.

**Monitor proof.** Induct on the observed word. The streak is the capped length of the last consecutive target suffix, and $b$ is true exactly when some completed target block of length $m+1$ has appeared. A completed block by $N=T+m$ has entry $e\le N-m=T$; conversely every successful entry by $T$ completes by $N$. This establishes the literal event, including time-zero membership and $m=0$. Combine with D-MONITOR and the existing D2 full-history theorem to conclude equality of the two optimal values and actual policy-value attainment.

The physical kernel still runs after success. Only the monitor remembers success. For a completed-by-$D$ objective use $N=D$; entry deadline $T$ is not substituted for $D$.

**Complexity contract.** A dense evaluator has $O(N|Y|^2(m+2)C_{\max})$ arithmetic operations up to a constant for the Boolean flag, and $O(|Y|(m+2))$ rolling value storage, plus the chosen policy table. This is an operation count, not a bit-complexity claim for growing exact rationals.

## D-FIRST — First-ever entry without retries

**Atlas:** D2-P02. This is a different event:

$$\tau_G\le T,\qquad Y_{\tau_G+j}\in G\quad(0\le j\le m).$$

Use phases `waiting`, `active(k)`, `failed`, `succeeded`. An initial target observation starts the active phase at count one; for $m=0$ it immediately succeeds. While waiting, a first target observation at time $t\le T$ starts the run; after $T$, waiting becomes failed. In an active phase, a nontarget observation fails permanently, while a target increments the count and count $m+1$ succeeds. Both terminal phases are absorbing **in the monitor only**. The induction invariant says the first target has either not occurred, is being followed by the unbroken initial stay, or has permanently succeeded/failed. Apply D-MONITOR.

The word $(1,0,1,1)$ with $T=2,m=1$ satisfies retryable residence but fails this first-entry objective. This counterexample is a required regression.

## D-AVOID — Combined residence before danger

**Atlas:** D2-P03. Choose the precise convention before coding. The selected success event is

$$\exists e\le T:\quad
\left(\forall j\le m,\;Y_{e+j}\in G\right)
\land\left(\forall t\le e+m,\;Y_t\notin D\right).$$

Thus danger has precedence at time zero and at a simultaneous target/danger observation. Danger **after completed success** does not undo this event. Add a `failed_before_success` flag; when unfinished, check danger before streak updates. Once complete, retain the success flag. The literal-event equivalence follows by the same prefix induction, then D-MONITOR supplies the optimum.

A separate hard-risk event is $\{\exists t\le N:Y_t\in D\}$. Its monitor must keep updating an `ever_danger` flag even after success. Failure to reach $G$ and hitting $D$ are not complements. A variant forbidding danger through the entire horizon is supported by replacing terminal reward with `success AND NOT ever_danger`; it has a different theorem name and event.

## D-LP — Exact finite hard-risk optimization

**Atlas:** D2-P04. Use a finite augmented state $z$ carrying all success/risk monitors. Let $P_t(z,c,z')$ be its actual controlled rows. Let $R(z),D(z)\in[0,1]$ be terminal success and risk scores. Define nonnegative occupancies $x_t(z,c)$ and state masses $d_t(z)$ by

$$d_0=\mu,\qquad \sum_cx_t(z,c)=d_t(z),$$

$$d_{t+1}(z')=\sum_{z,c}x_t(z,c)P_t(z,c,z').$$

Maximize $\sum_zR(z)d_N(z)$ subject to $\sum_zD(z)d_N(z)\le\rho$ and the flow equations. Infeasible risk budgets produce a proved infeasibility result for this stated class, not a made-up policy.

**Policy/flow equivalence.** Every history policy gives occupancies by its actual state/action marginals and therefore satisfies flow. Conversely, on $d_t(z)>0$ define $\pi_t(c\mid z)=x_t(z,c)/d_t(z)$, and use a fixed admissible action at zero-mass states. Induction gives exactly those state and control marginals. Thus optimizing the finite flow polytope is equivalent to optimizing over all allowed randomized histories for these expected terminal scores. This is why a risk-constrained solver may need randomization although D-MONITOR's unconstrained optimum does not.

**A complete rational reference constructor.** For rational data the feasible set is a closed bounded polytope: every flow variable lies in $[0,1]$. Enumerate full-rank active-constraint selections, solve the corresponding rational linear systems exactly, discard infeasible points, and maximize the rational objective over the remaining vertices. Establish completeness as follows. In the affine hull of a nonempty bounded polytope, a nonvertex point lies on a nonzero feasible line through that point. Extend in both directions until a new inequality is active; boundedness makes both endpoints finite. The point is a convex combination of the endpoints, each in a face of smaller dimension. Induct on face dimension to express every feasible point as a convex combination of vertices. Some vertex therefore attains at least its objective. Every vertex is isolated by a full-rank active constraint set, so enumeration finds it. For a singleton or dimension-zero polytope the unique point is already a vertex. Dependent equalities must be reduced or handled by an explicit rank test.

This supplies a mathematical total solver, but not an efficient implementation. A practical LP solver may propose a candidate; a small exact checker validates it independently.

**Optional dual certificate.** For $\lambda\ge0$ and rational functions $v_t$, require

$$v_N\ge R-\lambda D,\qquad
v_t(z)\ge\sum_{z'}P_t(z,c,z')v_{t+1}(z')\quad\forall c.$$

Every feasible policy then has success at most $\mu v_0+\lambda\rho$, by telescoping and the risk inequality. An attaining primal policy whose success equals this bound is optimal. This checker needs weak duality only; claiming every candidate has such a certificate requires a separate strong-duality theorem or the complete vertex construction above.

**Exact witness:** success $4/5+p/10$, danger $p/10$, budget $\frac{1}{20}$ force $p\le1/2$. The optimal success is $\frac{17}{20}$ at $p=1/2$; $p=1$ is infeasible.

## D-ROBUST — Nature's timing is part of the theorem

**Atlas:** D2-P05. The first closed contract is a finite perfect-information game: after observing the current augmented state and the **realized** control, nature selects a row from a nonempty finite set $\mathcal K_t(z,c)$. The choice can depend on the past, independently at every decision node (rectangularity). Then

$$V_t(z)=\max_c\min_{p\in\mathcal K_t(z,c)}\sum_{z'}p(z')V_{t+1}(z').$$

**Proof.** Reverse induction. Nature's minimizing row bounds every controller's value above by the displayed quantity, including mixed controls when nature sees their realization. The controller's maximizing control bounds its value below against every allowed nature strategy. Finite extrema yield deterministic time-state saddle strategies for this ordered game.

A **different** contract lets nature see the controller's distribution but not its private draw, and choose one jointly indexed model $\theta$ for the stage. The stage operator is

$$\max_{\lambda\in\Delta C}\min_\theta\sum_c\lambda_c
 \sum_{z'}K_\theta(z,c,z')V_{t+1}(z').$$

The finite rational maximin is an LP with constraints $v\le\sum_c\lambda_cQ_{\theta c}$ for every $\theta$, plus simplex constraints. D-LP's vertex method supplies the exact optimum. Mixing can help: matching-versus-opposite rewards has value $\frac{1}{2}$, while deterministic committed choice has worst-case value zero. Do not interchange these two stage games.

If nature chooses one hidden model for the **whole horizon**, local row minimization is generally false. With no controls, two permitted models have survival factors $(1/10,9/10)$ and $(9/10,1/10)$. The true worst-model two-step survival is $\frac{9}{100}$; a rectangular row adversary gives $\frac{1}{100}$. This strict counterexample must remain alongside the theorem. Model commitment needs an enlarged information state or explicit whole-model optimization, not relabeling.

## D-BELIEF — Partial observation of a hidden augmented state

**Atlas:** D2-P06. Fix finite hidden state $z$ containing the physical state **and every event monitor**, finite controls with a specified observation-admissible menu, and observation kernel $O_t(o\mid z',c)$. At time $t$ the controller knows its observations and past actions, not $z$. A belief $b_t$ is the conditional law of the full hidden augmented state. After control $c$ and observation $o$,

$$p(o\mid b,c)=\sum_{z,z'}b(z)P_t(z,c,z')O_t(o\mid z',c),$$

$$b'(z')=\frac{O_t(o\mid z',c)\sum_zb(z)P_t(z,c,z')}
 {p(o\mid b,c)}.$$

At a zero denominator use a fixed default belief; its branch weight is zero. Conditional finite-sum identities prove this Bayes update and the belief-controlled history law. A belief over the physical state alone need not remember whether a hidden past target run succeeded.

For a common finite control menu, terminal value is $V_N(b)=b\cdot R$ and

$$V_t(b)=\max_c\sum_o p(o\mid b,c)V_{t+1}(b'_{c,o}).$$

**Finite alpha-vector construction.** Set $\Gamma_N=\{R\}$. For each control $c$ and selection $\alpha_o\in\Gamma_{t+1}$ for every observation, include

$$\alpha(z)=\sum_{z'}P_t(z,c,z')\sum_oO_t(o\mid z',c)\alpha_o(z')$$

in $\Gamma_t$. Then $V_t(b)=\max_{\alpha\in\Gamma_t}b\cdot\alpha$. Expand the recursion, cancel Bayes denominators against branch probabilities, and choose a separate continuation maximizer for each observed branch. Zero-probability branches contribute zero. This proves sufficiency, attainment by a finite observation-policy tree, and piecewise-linear convexity; it does not identify the hidden model from observations. Arbitrary belief-dependent legal menus need a separate formulation, not this fixed alpha-vector enumeration.

## D-SAFETY — Infinite retention in a finite controlled model

**Atlas:** D2-P07. For target $G$ define $v_0=\mathbf1_G$ and

$$v_{n+1}(y)=\mathbf1_G(y)\max_{c\in C(y)}\sum_zK_c(y,z)v_n(z).$$

Then $v_n$ decreases pointwise to $v$, and $v(y)$ equals the supremum, over all behavioral histories, of the probability of remaining in $G$ forever. A deterministic stationary policy attains it.

**Proof.** Finite-horizon safety follows from D-MONITOR. Monotonicity and bounds give the limit. Finiteness of states and controls permits exchanging finite sums/maxima with this decreasing limit, yielding the fixed-point equation for $v$. Choose a control attaining it at each state. Repeated fixed-point evaluation, with $v\le\mathbf1_G$, gives $v(y)\le\mathbb P_y^\pi(\text{safe through }n)$. Continuity from above implies $v(y)\le\mathbb P_y^\pi(\text{safe forever})$. Conversely every policy's infinite-safety probability is bounded by every $v_n$, hence by $v$. The two bounds agree. This avoids an unjustified interchange of an infinite-policy supremum and a limit.

The probability-one safe set is the greatest controlled invariant subset. Compute $C_0=G$ and

$$C_{k+1}=\{y\in C_k:\exists c\in C(y),\;K_c(y,C_k)=1\}.$$

The descending finite sequence stabilizes. Controls staying in its limit prove almost-sure safety there. Conversely the set $\{v=1\}$ is controlled invariant by the fixed-point equation and finiteness, so is contained in every $C_k$. A verified policy can first reach such a set and then switch to its safe controller using a monitor flag. This is a controlled-process result; invoking C70's frozen-intervention theorem additionally requires an explicit law/typing bridge.

A single high finite-horizon survival probability never proves infinite survival. For fixed leakage $\varepsilon>0$, $(1-\varepsilon)^n\to0$ is the required negative witness.

## D-BLOCK — Adaptive controls formed from admissible strategic blocks

**Atlas:** D2-P08. At each augmented state choose from a finite certified menu of action/update patches, constructed using the existing disjoint grammar or B-OVERLAP below. Each selected block yields an actual induced row in $\alpha\to P\to U$ order and retains the literal $P$. Reindex those rows into the finite controlled model and prove their equality to the typed block model; then D-MONITOR gives history-law and optimum correspondence.

The controller is selected before the action/world/update stage. Choosing an update patch after observing $x'$ is a different information structure unless the preselected patch is itself a lawful kernel reading $x'$. Choosing different blocks over time does not create a single original frozen intervention.

## D-CLASS — A closed asymptotic optimization contract

**Atlas:** D2-P09. The selected first implementation optimizes over a **finite menu of deterministic stationary policies**, not arbitrary adaptive asymptotic strategies. Enumerate the policies $\pi\in\prod_yC(y)$. For each, derive the actual rational $K^\pi$, compute its genuine bottom classes, their C11 stationary descriptor laws $\nu_C^\pi$, and C10 absorption probabilities $h_C^\pi(y)$. For a predeclared bounded functional $F$ with exact evaluation on these rational laws,

$$J^\pi(y)=\sum_C h_C^\pi(y)F(\nu_C^\pi)$$

is the expectation of $F$ applied to the actual random descriptor occupation limit. The existing C2 class-selection law proves the equality, and finite argmax proves an attaining optimum over the declared stationary menu. A decidable target-law predicate is obtained by taking $F$ to be its indicator. Distinct physical classes with the same descriptor law must receive the same descriptor-target label, without being merged as physical states.

General history-policy asymptotic optimization, maximal-end-component synthesis and continuous occupation reward objectives are **not** asserted by this finite-menu contract. They require a separately quantified end-component/mean-payoff theorem. This residual scope must remain visible when the atlas row is updated.

**D build dependencies.** D-MONITOR comes first and supports D2-R01/P01/P02/P03/P08. D-LP then supports risk and the hidden-private-draw robust stage. D-BELIEF is a separate finite-observation layer. D-SAFETY is a monotone fixed-point result. D-CLASS depends on C2/C10/C11, not on partial observation or risk constraints.


\newpage

# C — Total stationary certificates and nonfinite occupation scope

**Source basis:** SRC-015, SRC-016, SRC-019. Exact references and canonical hashes are in the source register; theorem IDs in this chapter denote the new paper derivations.

**Atlas:** C11-P01 and C-P01. Existing C10 already has a total rational Dirichlet/Cramer certificate theorem and actual typed absorption-event bridges. Existing C2 already gives unique invariant probability on each finite genuine recurrent class. Neither result is recommissioned here.

## C11-REFERENCE — One nonsingular matrix for each bottom class

Let $K$ be a nonempty finite rational stochastic matrix. Compute its genuine bottom strongly connected classes by the existing finite graph procedure. For one class $C$ of size $m\ge1$, let $P=K|_{C\times C}$. It is stochastic because $C$ is closed and irreducible because $C$ is strongly connected. With $\mathbf1$ the length-$m$ vector of ones, set

$$M_C=I-P^{\mathsf T}+\mathbf1\mathbf1^{\mathsf T},\qquad
p_C=M_C^{-1}\mathbf1.$$

The exact rational implementation is Cramer's rule, not a floating inverse. For index $j$, define

$$p_C(j)=\frac{\det(M_C[j\leftarrow\mathbf1])}{\det(M_C)}.$$

Extend $p_C$ by zero outside $C$. Enumerate every bottom class once in canonical order. This constructs `referenceStationaryFamily K` and must satisfy

$$\operatorname{checkStationaryFamily}
   (K,\operatorname{referenceStationaryFamily}(K))=\mathrm{true}.$$

### C11-NULL — Nonsingularity, including periodic classes

**Step 1: right harmonic functions are constant.** If $Pf=f$, choose a coordinate maximizing the real vector $f$. The convex-average equality forces every positive-probability successor of that coordinate to have the same maximum. Irreducible reachability propagates this equality to every state. Thus $\ker(I-P)$ is the one-dimensional constant subspace. This uses neither aperiodicity nor a convergent sequence of transition matrices.

**Step 2: left nullspace.** Rank equality under transpose implies $\ker(I-P^{\mathsf T})$ has dimension one. Reuse C2's existing normalized invariant probability $\pi_C$ to span it. Its strict positivity follows from irreducibility: a zero coordinate propagates backwards along positive transitions, contradicting total mass one.

**Step 3: $M_C$ has zero kernel.** Suppose $M_Cv=0$. Since $P\mathbf1=\mathbf1$,

$$\mathbf1^{\mathsf T}M_Cv=m\,\mathbf1^{\mathsf T}v=0.$$

Hence $\sum v=0$, and the original equation reduces to $(I-P^{\mathsf T})v=0$. Therefore $v=a\pi_C$, and normalization gives $a=0$. In finite dimension $M_C$ is invertible. The rational determinant is nonzero because its embedding into the reals is nonzero. This embedding step is a required lemma, not a second numerical nonsingularity test.

### C11-CHECK — Why the constructor is accepted

The rational Cramer vector solves $M_Cp_C=\mathbf1$. The real invariant vector also solves this equation: $(I-P^{\mathsf T})\pi_C=0$ and $\mathbf1\mathbf1^{\mathsf T}\pi_C=\mathbf1$. Uniqueness therefore identifies the rational vector's real cast with $\pi_C$. Nonnegativity, strict class positivity, normalization and stationarity follow. The zero extension has full-state balance: a row starting in $C$ cannot leave $C$, and outside-class entries are zero.

The class list is duplicate-free and complete by the existing bottom-class enumeration theorem. Instantiate `ClassStationaryConditions` for every entry and prove each Boolean check true by its exact decidable propositions. Then instantiate the existing family checker and its typed stationary/observed-law bridge. The final theorem returns successful checking for **every** valid nonempty finite rational matrix; it does not impose the Python producer's twelve-state resource limit on the mathematics.

**Constructivity boundary.** The existing real invariant law is used only to prove the explicit determinant algorithm correct. The returned numbers are rational determinants, not `Classical.choose` of an unspecified real solution. A faster exact Gaussian solver may be added only after proving equality with this reference or supplying independently checked output certificates. JSON parsing remains outside the Lean kernel unless separately formalized.

**New modules:** `ReverseSolver/C11ReferenceStationary.lean`, `C11ReferenceCompleteness.lean`, `C11ReferenceTypedBridge.lean`. Reuse existing C11 checker declarations and the C2 finite invariant API. Do not edit historically protected solver files.

**Destructive cases:** omitted/duplicated class; a non-bottom SCC; wrong full-state support; signed or unnormalized vector; changed transition entry; determinant-zero fake certificate; singleton class; periodic two-cycle; all-absorbing diagonal matrix; direct rational-to-real cast mismatch. The independent supplied script checks several exact finite instances, not the universal theorem.

## C-CLUSTER — Compact Feller empirical limits

**Atlas:** C-P01. A sound first extension beyond finite states is the following. Let $Y$ be a nonempty compact metric space with its Borel sigma-algebra, and let $K$ be a Feller Markov kernel. For any initial law, almost surely every weak empirical cluster point is invariant. Consequently the distance of empirical laws to the invariant-law set tends to zero. If there is a unique invariant law, the empirical laws converge almost surely to it.

Write $L_n=n^{-1}\sum_{t<n}\delta_{Y_t}$. Choose a countable supnorm-dense family in $C(Y)$. For one bounded continuous $f$, define martingale differences

$$D_{t+1}=f(Y_{t+1})-Kf(Y_t).$$

They have conditional mean zero and bounded second moments. Orthogonality gives $\mathbb E(\sum_{t<n}D_{t+1})^2\le4\|f\|_\infty^2n$. Chebyshev along $n=k^2$ gives summable probabilities for every fixed positive error. Borel--Cantelli implies the normalized sums tend to zero on that subsequence; between consecutive squares, bounded increments and a gap $2k+1=o(k^2)$ extend convergence to all $n$.

Telescoping endpoints now gives

$$L_n(Kf-f)=\frac{f(Y_n)-f(Y_0)-\sum_{t<n}D_{t+1}}n\longrightarrow0.$$

Intersect the countably many probability-one sets. Compactness of $Y$ makes its probability space weakly compact. If $L_{n_j}\Rightarrow\pi$, Feller continuity makes both $f$ and $Kf$ continuous, so $\pi Kf=\pi f$ for the dense tests. Uniform approximation extends to all continuous tests; equality of their integrals implies $\pi K=\pi$. Every cluster point is thus invariant, proving invariant existence as well. If distance to the closed invariant set did not vanish, a subsequence bounded away from it would have a cluster point in it, a contradiction. If that set is a singleton, the same subsequence argument gives full convergence.

This is a theorem about cluster sets, not a promise of a single random limit when several invariant laws exist. The compactness/tightness and Feller assumptions are substantive. On a Polish noncompact state space, the same argument works **conditional on almost-sure tightness** and a countable measure-determining continuous class with the required continuity of $Kf$. Do not assert a nonexistent countable supnorm-dense family in all of $C_b(Y)$, and do not infer almost-sure tightness from arbitrary marginal bounds.

## C-RANDOM — A stationary random-law profile

For a stationary Markov law on a Polish Borel state space with invariant initial law $\pi$, use the shift-invariant sigma-algebra $\mathcal I$. A regular conditional law of $Y_0$ given $\mathcal I$ defines a random probability $\Lambda$. Birkhoff's theorem gives, simultaneously for a countable convergence-determining bounded-continuous class,

$$L_n f\longrightarrow\mathbb E[f(Y_0)\mid\mathcal I]=\Lambda f\quad\text{a.s.}$$

Hence $L_n\Rightarrow\Lambda$ almost surely. In the compact Feller profile, C-CLUSTER also gives $\Lambda K=\Lambda$ almost surely. A general measurable stationary Markov variant needs its own proof of invariance of the conditional random measure; do not omit that premise by copying the compact argument without Feller continuity.

If an initial law $\mu$ satisfies $\mu\ll\pi$, its whole Markov path law is absolutely continuous with respect to the stationary path law, with density $(d\mu/d\pi)(Y_0)$. Verify this first on finite cylinders, then extend by measure uniqueness. All the preceding almost-sure statements transfer to that path law. This does not include every point start when $\pi$ is nonatomic.

**Analytic imports requiring their own checked declarations:** the stationary shift map and its measure-preserving property, Birkhoff, regular conditional probability existence in the stated Borel profile, measurability of a probability-valued random variable, and the convergence-determining test theorem. These are named dependencies, not new axioms and not implied by the current finite C2 theorem.

## C-FAMILY — Conservative family semantics and limits

Freeze a measurable descriptor and a **predeclared** closed family $\mathcal F$ of descriptor laws. There are different usable predicates: distance to $\mathcal F$ tends to zero; every cluster point lies in $\mathcal F$; or there is an almost-sure random limit taking values in $\mathcal F$. In the compact setting the first two are equivalent by subsequence compactness. The third implies them but is stronger. Under C-RANDOM, prove the actual pushforward $h_\#\Lambda$ belongs to $\mathcal F$ before claiming a family certificate. Continuity of $h$ suffices to push weak convergence through $h$; mere measurability does not.

When $\mathcal F=\{\nu\}$ and the required convergence mode is almost-sure weak, the family condition recovers the original occupation clause. It does **not** recover the other Exact-GR clauses without their independent region invariance, basin and nontriviality proofs. A family chosen after observing the path to contain its outcomes is not this predeclared object.

**Negative cases.** A deterministic homogeneous chain on a countable state space can encode a clock and alternate two descriptor labels in blocks of lengths $2^{2^k}$; averages near the ends of successive blocks oscillate. The homogeneous state must include the block index and within-block clock, rather than sneaking in a time-varying transition. A deterministic chain moving from $n$ to $n+1$ on $\mathbb N$ escapes compact sets and has no tight empirical family. Distinct invariant physical classes may still have equal descriptor laws. These examples defeat unconditional general-state convergence and false physical-class identification.

**Scope disposition:** C-P01 receives exact compact-Feller cluster and stationary random-law contracts here, not a universal arbitrary-measurable-space completion. The broader topology/recurrence programme remains a separately identified extension.


\newpage

# B and X+ — Compatible grammar extensions and a new positive economic witness

**Source basis:** SRC-030. Exact references and canonical hashes are in the source register; theorem IDs in this chapter denote the new paper derivations.

## B-OVERLAP — Compatible patches, not arbitrary conflict resolution

**Atlas:** B-P01. The existing partition grammar is already proved. The selected extension allows overlapping masks only when their replacements agree there. Let a finite bank of action patches have measurable masks $E_i$ and Markov replacement kernels $A_i$ on the original action input space. For an admitted block $I$, require

$$A_i(y,\cdot)=A_j(y,\cdot)\quad
\text{for all }y\in E_i\cap E_j,\quad i,j\in I.$$

Apply the same condition separately to update patches on the actual update input space, which includes $(y,a,x')$. Define the patched kernel by the original kernel outside the union, and by the least-index active replacement inside it. Finite measurable piecewise selection makes it a Markov kernel.

**B-ORDER theorem.** The result is independent of the ordering used to select active patches. Sequentially applying all patches of $I$ gives that same result in any permutation; applying a patch twice is idempotent. Compatible unions agree with composition of their two compatible subblocks.

**Proof.** At each input either no mask is active, leaving the baseline, or every active replacement has the same measure by pairwise agreement. Every claimed construction therefore has the same pointwise row. Kernel extensionality proves equality; actual ordered $\alpha/P/U$ composition, canonical law uniqueness and the original margin transport give the model/path/property consequences. The physical $P$ remains fixed throughout.

A block can still be inadmissible for an unrelated grammar constraint. Compatibility does not make an arbitrary allowed-block family downward-closed. An explicit priority rule for disagreeing patches would be a different, order-sensitive semantics, not this theorem. The two patches assigning $\delta_0$ and $\delta_1$ to the same row provide the mandatory conflict counterexample.

**Modules:** `GrammarRobust/CompatibleOverlap.lean`, `OverlapKernelAssembly.lean`, `OverlapCanonicalBridge.lean`. General nonlinear transformations of kernels need commuting-operator conditions; pairwise row-replacement equality does not cover them.

## B-LOCAL-ORDER — Minimality through lower-set lifting

**Atlas:** B-P02. Let $P,Q$ be posets of admissible blocks and $f:P\to Q$. Let $p:P\to\{\mathrm{true},\mathrm{false}\}$ and $q:Q\to\{\mathrm{true},\mathrm{false}\}$ be matched positivity predicates, for example positivity of the actual constitutive margin. At a block $a$, assume:

1. $p(b)\leftrightarrow q(f(b))$ for every $b\le a$.
2. $b<a$ implies $f(b)<f(a)$.
3. For every $c<f(a)$ there exists $b<a$ with $f(b)=c$.

Then $a$ is minimal positive in $P$ if and only if $f(a)$ is minimal positive in $Q$.

**Proof.** If $a$ is minimal positive, its image is positive. A smaller positive $c$ in $Q$ would lift by condition 3 to a smaller positive $b$, contradiction. Conversely, a smaller positive $b$ would have a strictly smaller positive image by conditions 1 and 2, contradicting image minimality. No injectivity on incomparable blocks or global order isomorphism is used.

The hypothesis is local downset coverage, not arbitrary matching of effect values. Existing coarse-to-fine image-relative results remain valid where this coverage fails. In a finite meet-semilattice, if the nonempty family of positive admissible elements is closed under pairwise meet, its finite meet is positive and below every positive element, giving a unique least positive block. This extra meet-closure is exactly what supplies uniqueness. Two positive incomparable singletons with a nonpositive empty meet show why uniqueness does not follow otherwise; XOR shows positivity need not be monotone under adding components.

**Build:** `GrammarRobust/LowerSetTransport.lean` and `PositiveMeetClosure.lean`; instantiate with actual matched block models, not free-standing Boolean labels whose relation to constitution is assumed without proof.

## XPLUS — New economic model, not a revision of X1

**Atlas:** X1-P01. The old eighteen-state X1 replete-region claim remains false. The following is a **new constructed instance specified in this document**, not an empirical calibration and not a claim of independently authenticated preregistration. Give it a new namespace, e.g. `EconomicWitness`, and a separately recorded selection history.

Let strategic state be `Unit`, world $X=\{0,1,2\}$, and actions $(a_1,a_2)\in\{0,1\}^2$. Worlds $0,1$ are two functioning resource conditions; $2$ is collapse. Interpret action zero as restraint and one as extraction. The physical world kernel is

$$P(x,a)=\begin{cases}
\delta_2,&x=2,\\
\tfrac12\delta_0+\tfrac12\delta_1,&x\in\{0,1\},\ a=(0,0),\\
\delta_2,&x\in\{0,1\},\ a\ne(0,0).
\end{cases}$$

The strategic update is the unit kernel. Set $B=B_0=B_1=\{0,1\}$, descriptor and relevance map $h=g=x$ on the entire world, and target $\nu=\tfrac12\delta_0+\tfrac12\delta_1$. Use the discrete topology and almost-sure weak occupation mode. Baseline both players restrain. Stage reward to player $i$ is $1+a_i$ in a functioning world and zero in collapse; discount $\beta=3/4$.

### XPLUS-EQ — Strategic incentives

Against the baseline opponent define $V_i(0)=V_i(1)=4$, $V_i(2)=0$. Restraint gives $1+(3/4)4=4$, while unilateral extraction gives $2+(3/4)0=2$. At collapse both choices give zero. Thus both-player Bellman equality and all pure/mixed deviation bounds hold. S-VERIFY then proves optimality against all permitted behavioral histories, not merely a stationary one-shot comparison. The advantage identity here is $2\mathbf1\{x\in B,a_i=1\}$.

### XPLUS-GR — All original regime gates

Well-posedness comes from the existing finite typed canonical model. Baseline $K(x,B)=1$ for every $x\in B$. The basin is nonempty, and $B$ has nonempty discrete interior (or positive chosen reference mass). The descriptor takes two values on $B$. Starts zero and one have different state-path laws already at time zero, so the original basin and comparison path-law nontriviality gates hold. The unique recurrent class inside $B$ has invariant law $\nu$, so existing C2 gives the original descriptor empirical convergence for **every** initial law supported on $B$. The collapse class outside $B$ does not violate the basin-quantified theorem.

For any such initial law the next observation is fair on $\{0,1\}$, establishing basin-reachable descriptor nondegeneracy. The relevance map is the world coordinate throughout, including collapse; prove the appropriate original descriptor/relevance factorization with identity maps. This is an explicit mathematical grounding instance. Substantive legitimacy for any real resource system remains an empirical claim, not supplied by these identities.

### XPLUS-PR — Actual strategic constitution

Freeze the descriptor path property

$$\psi(\Lambda)=\Lambda\{\omega:\forall t,\ h(\omega_t)\in\{0,1\}\}.$$

The event is measurable as a countable intersection. Baseline value is one at both comparison starts. Replace player 1's action by constant extraction, keeping player 2's restraint, $P$, and unit update fixed. The actual path reaches collapse at time one with probability one, hence the property value is zero at both starts. Therefore both effects equal one and the **original** uniform constitutive margin is one. Combine the Exact-GR proof and the actual admissible intervention with the existing original PR constructor. Combine descriptor/relevance and nondegeneracy proofs with the original grounded-confirmatory constructor only after matching every field of its Lean structure; do not substitute a weaker hand-written predicate.

This witness demonstrates that economic incentives, nondegenerate occupation and genuine persistence can coexist in a constructed finite model. It does not demonstrate that every learner differs from equilibrium. A learning comparison would be an additional model with its own gates and target law.

**Required modules:** `EconomicWitness/Model.lean`, `Incentives.lean`, `ExactRegime.lean`, `Constitution.lean`. Tests independently reject leakage under baseline, constant descriptor on $B$, singleton comparison, world replacement mislabeled as a strategic intervention, absent off-region relevance, and a changed reward making extraction profitable. None of these modules edits `X1/` or the frozen papers.


\newpage

# E — Five specialized algebraic transfer contracts

**Source basis:** SRC-041, SRC-042, SRC-043, SRC-044, SRC-045. Exact references and canonical hashes are in the source register; theorem IDs in this chapter denote the new paper derivations.

**Atlas:** APP-E01 through APP-E05. The repository's five supporting Weil--CCM papers supply specialized architectures, not universal Permansson conclusions. The contracts here isolate finite algebra that can be proved and reused, with an explicit remaining **model-to-algebra bridge**. A source matrix must come from a specified actual model/feature map; the coding agent must not invent that identification. No result below proves the Riemann hypothesis, eliminates every first-bad state, or establishes real-world causality.

The first implementation profile uses finite real inner-product spaces and symmetric matrices. Complex symmetric/bilinear and complex Hermitian/sesquilinear variants must retain their distinct conjugation conventions. The real derivations are not silently substituted for a complex source theorem.

## E-SCALAR — Seam invisibility gives rank two, not automatically rank one

**Atlas:** APP-E01. Let $H$ be a real symmetric $n\times n$ matrix, $n\ge1$, and choose pivot $p$. Suppose

$$(e_i-e_p)^{\mathsf T}H(e_j-e_p)=0\qquad\forall i,j.$$

Then, with $a_i=H_{ip}-H_{pp}/2$,

$$H_{ij}=a_i+a_j,\qquad H=\mathbf1a^{\mathsf T}+a\mathbf1^{\mathsf T},
\qquad\operatorname{rank}H\le2.$$

**Proof.** Expand the hypothesis to obtain $H_{ij}-H_{ip}-H_{pj}+H_{pp}=0$, then use symmetry. Every column is in the span of $\mathbf1,a$. If the diagonal is additionally constant, $H_{ii}=\delta$, then $2a_i=\delta$ for every $i$, so

$$H=\delta\mathbf1\mathbf1^{\mathsf T}.$$

This is a common-mode rank-one matrix, **not** $\delta I$. Seam invisibility alone does not imply a scalar common mode: $H=\left(\begin{smallmatrix}0&1\\1&2\end{smallmatrix}\right)$ satisfies the seam condition and has determinant $-1$.

For a nested family preserving old matrix entries, constant-diagonal scalars agree across embeddings by looking at one retained diagonal entry. No convergence theorem is required for that consistency, and no positivity is inferred if $\delta$ has unspecified sign.

**Permansson bridge contract.** Given an actual baseline/intervention path-law feature matrix pair $G_0(y),G_J(y)$, prove that their difference $H_y$ has these seam and diagonal properties at every original comparison start. Freeze a test vector $v$ and define the scalar property from the actual matrix functional $v^{\mathsf T}Gv$. Then

$$\Delta_v(y)=|\delta_y|\left(\sum_i v_i\right)^2,$$

and, under the original nonempty comparison-domain and bounded-below infimum conditions,

$$\kappa_v=\left(\sum_i v_i\right)^2\inf_{y\in B_1}|\delta_y|.$$

Prove the matrix functional equals the actual `RegimePropertyMap` value before applying this identity. A zero-sum test vector sees no common-mode defect. This conditional wrapper is a valid algebraic transfer; exhibiting a natural nontrivial Permansson model satisfying its premises is a separately named residual obligation.

## E-DETECT — Persistent finite witnesses under legal approximation

**Atlas:** APP-E02. Let $Q(v)=B(v,v)$ for a continuous bilinear form on a normed space with
$|B(u,v)|\le C\|u\|\|v\|$. Suppose $Q(h)=-\gamma<0$ and a **legal** finite approximant $p$ obeys $\|p-h\|\le\varepsilon$. Then

$$|Q(p)-Q(h)|\le C\varepsilon(2\|h\|+\varepsilon).$$

**Proof.** Write $Q(p)-Q(h)=B(p-h,h)+B(p,p-h)$, apply the bound and $\|p\|\le\|h\|+\varepsilon$. If the right side is less than $\gamma$, then $Q(p)<0$. A source using two control seminorms $a,b$ instead has the exact bound

$$|Q(p)-Q(h)|\le C\bigl[a(p-h)b(h)+a(p)b(p-h)\bigr].$$

Do not replace these source norms with a convenient numerical norm without proving the comparison.

Let $V_N$ be nested legal finite carriers with embeddings $j_{N,M}$, and let their forms satisfy
$Q_M(j_{N,M}v)=Q_N(v)$ for $M\ge N$. Once a legal $p\in V_N$ is negative, its image remains negative at every later carrier. If finite carriers are dense in the stated control topology and preserve the legal constraints, choose an approximation fine enough to satisfy the displayed strict bound, producing finite detection and persistence.

The hard source-specific premise is **legal approximation**, including boundary constraints and the exact embedding identity. Unconstrained density, a numerical grid or changing quadrature does not prove it. A Permansson application must supply the actual discrepancy form, legal feature dictionaries and their canonical-path interpretation. The theorem transfers an existing strict negative witness; it does not conjure one.

## E-SHELL — First-bad reduction with the actual shell dimension

**Atlas:** APP-E03. On a finite orthogonal decomposition $V\oplus W$, let

$$T=\begin{pmatrix}H&B\\B^{\mathsf T}&C\end{pmatrix},\qquad H\succeq0,
\qquad r=\dim W.$$

For every real $\lambda<0$, $H-\lambda I$ is positive definite and invertible. An eigenvector $(v,w)$ for $\lambda$ satisfies

$$v=-(H-\lambda I)^{-1}Bw,$$

$$\left[C-\lambda I-B^{\mathsf T}(H-\lambda I)^{-1}B\right]w=0.$$

Conversely these equations construct an eigenvector from any nonzero shell kernel vector. In particular $w\ne0$: otherwise $v$ would be a negative eigenvector of $H$. Gaussian block elimination gives

$$\det(T-\lambda I)=\det(H-\lambda I)
\det\left(C-\lambda I-B^{\mathsf T}(H-\lambda I)^{-1}B\right).$$

**Proof.** Solve the first block equation, substitute into the second, and multiply block triangular elimination matrices of determinant one. The coercive inequality
$v^{\mathsf T}(H-\lambda I)v\ge-\lambda\|v\|^2$ supplies invertibility.

Only if $r=1$ is the shell equation scalar:

$$f(\lambda)=c-\lambda-b^{\mathsf T}(H-\lambda I)^{-1}b=0.$$

Its derivative is

$$f'(\lambda)=-1-b^{\mathsf T}(H-\lambda I)^{-2}b<0.$$

The derivative follows from differentiating the inverse identity. Scalar monotonicity is not licensed when the shell dimension exceeds one. “Cubic shell” in the source denotes a particular carrier/degree structure, not a universal one-dimensional successor quotient.

For a nested hierarchy, a least index with a negative witness exists by well-ordering **if** the set of bad indices is nonempty. Earlier nonnegativity then licenses this block theorem. The source-specific next step is proving the actual nested carriers, shell dimension and intertwining/source identities. Their names are not hypotheses automatically satisfied by arbitrary strategic models.

## E-SINGULAR — Compatibility at zero shift

**Atlas:** APP-E04. For finite symmetric $H$, $\operatorname{Ran}H=(\ker H)^\perp$. Thus $Hx=b$ is solvable iff $b$ is orthogonal to the whole kernel. All solutions differ by a kernel vector. If $H\succeq0$ and $b=Hx$, then

$$\begin{pmatrix}H&b\\b^{\mathsf T}&c\end{pmatrix}\succeq0
\quad\Longleftrightarrow\quad c-b^{\mathsf T}x\ge0.$$

The scalar $b^{\mathsf T}x$ is independent of the chosen solution, since $b$ is orthogonal to the kernel. The equivalence follows by completing the square:

$$v^{\mathsf T}Hv+2t b^{\mathsf T}v+ct^2
=(v+tx)^{\mathsf T}H(v+tx)+(c-b^{\mathsf T}x)t^2.$$

If $b\notin\operatorname{Ran}H$, choose $z\in\ker H$ with $b^{\mathsf T}z\ne0$. Taking $v=sz,t=1$ makes the quadratic form $2s b^{\mathsf T}z+c$, negative for some $s$. Replacing a missing inverse by a pseudoinverse without this compatibility condition is therefore invalid.

For the positive-semidefinite case, the safe negative resolvent retains the kernel obstruction exactly:

$$(-\lambda)\Pi_{\ker H}(H-\lambda I)^{-1}b=\Pi_{\ker H}b,
\qquad\lambda<0.$$

On the kernel, the resolvent is multiplication by $-1/\lambda$. This identity does not prove that zero-shift preimages exist.

### E-SOURCE — Denominator-free source rigidity

To preserve the source paper's structure, state the additional data explicitly. Let $H_\pm$ be self-adjoint predecessor blocks, let $D:V_+\to V_-$, and let $n_->0$ be the squared norm of the odd shell. Let $b_\pm$ be coupling vectors and $a,d\in V_-$. Suppose a source functional $\Phi$ and normalized even coupling $\beta$ satisfy, for $z\in\ker H_+$,

$$H_-Dz=\beta(z)d+\Phi(z)a,$$

$$\frac{\langle b_-,Dz\rangle}{n_-}=\beta(z)+\Phi(z).$$

Suppose also $H_+x_+=b_+$ and $H_-x_-=b_-$, and $\beta(z)=\langle b_+,z\rangle/n_+$ with $n_+>0$. Self-adjointness gives $\beta(z)=0$ on $\ker H_+$. Hence $H_-Dz=\Phi(z)a$ and

$$\Phi(z)=\frac{\langle x_-,H_-Dz\rangle}{n_-}
=\Phi(z)\frac{\langle x_-,a\rangle}{n_-}.$$

Consequently

$$\boxed{\Gamma_0\Phi(z)=0,\qquad
\Gamma_0=1-\frac{\langle x_-,a\rangle}{n_-}.}$$

One may conclude $\Phi|_{\ker H_+}=0$ only with the **additional** hypothesis $\Gamma_0\ne0$. Otherwise a source-visible kernel vector forces $\Gamma_0=0$. Do not divide away the exceptional branch.

For zero-shift trial vectors $u_\pm$ with shell coordinate one, assume the actual transported response yields $w=Du_+-u_-\in V_-$ and

$$H_-w=\sigma_+d+\Phi(u_+)a,$$

$$\frac{\langle b_-,w\rangle}{n_-}
=\sigma_++\Phi(u_+)-\sigma_-.$$

Pair the first identity with $x_-$, use the second, and rearrange to obtain

$$\sigma_-=\alpha_0\sigma_++\Gamma_0\Phi(u_+),
\quad\alpha_0=1-\frac{\langle x_-,d\rangle}{n_-}.$$

These coefficients are attached to the selected preimages; their individual preimage-independence or equality to negative-shift limits is **not** claimed. The matrix/source identities must be proved from the actual specialized construction or explicitly supplied by a separately proved bridge. The generic linear algebra above does not identify a production Weil--CCM source moment on its own.

## E-GRAM — Explicit separating direction and perturbation margin

**Atlas:** APP-E05. In a finite real inner-product space, take $c>0$ and vectors $x,y$. Define

$$A=c(xx^{\mathsf T}-yy^{\mathsf T}),\qquad
\Delta=\|x\|^2\|y\|^2-\langle x,y\rangle^2.$$

If $\Delta>0$, set $w=\|x\|^2y-\langle x,y\rangle x$. Direct expansion gives

$$\langle x,w\rangle=0,\quad\langle y,w\rangle=\Delta,
\quad\|w\|^2=\|x\|^2\Delta,$$

$$w^{\mathsf T}Aw=-c\Delta^2<0.$$

Thus a unit normalization has negative Rayleigh value

$$-\gamma=-\frac{c\Delta}{\|x\|^2}.$$

For any symmetric perturbation $E$ with operator norm below $\gamma$, the same normalized vector remains negative because $|\langle w,Ew\rangle|\le\|E\|\|w\|^2$. The linear functional $M\mapsto w^{\mathsf T}Mw$ is nonnegative on the positive-semidefinite cone and strictly negative at $A$, giving an explicit separating witness.

A positive-semidefinite additional component $P$ may mask the negative block. Negativity for $A+P$ requires $w^{\mathsf T}Pw<c\Delta^2$; it is not inherited merely because $A$ is one summand. A signed rank-one representation and the actual Gram gap must themselves be certified from the modeled feature operator. The source paper's legal witness construction and a Permansson path-feature realization are separate, explicit bridges.

## E build disposition

Build these as optional modules under a new research namespace, e.g. `Specialized/SeamReduction`, `FiniteDetection`, `ShellSchur`, `SingularCompatibility`, and `GramSeparation`. They prove reusable conditional algebra, with tests for every denominator, nullspace, sign and dimension premise. **All five remain conditional specialized transfers until a named actual Permansson subclass supplies the model-to-algebra identifications.** Source-specific imported formal declarations require their own source and axiom audit; possession of a PDF is not a Lean import.


\newpage

# Implementation contract and proof acceptance

## The actual delivery unit

This package supplies paper theorems and derivations for explicit targets corresponding to every atlas ID. It does not supply a compiling replacement repository. The coding agent's work is to formalize the stated definitions, bridges and proofs, and demonstrate acceptance on the actual pinned source. It must not weaken a target merely to achieve a green build.

The registry `registries/closure_contracts.json` is the per-atlas routing table. Its `paper_status`, `formal_status` and `residual_scope` fields are independent. `PAPER_DERIVATION` means the derivation appears here; **every new formal status starts as `NOT_LEAN_VERIFIED`**. `SCOPED_DERIVATION` or `CONDITIONAL_TRANSFER` must remain visible after a narrower theorem compiles.

## Existing source interfaces to reuse

The source register records exact local canonical blob hashes for the inspected providers. The following are important anchors, not permission to assume a missing theorem:

| Source | Reuse |
|---|---|
| `X1/TypedModels.lean` | Actual action/world/update kernels, `inducedKernel_atom_entry` |
| `X1/Comparison.lean` | `Jaction`, `Jupdate`, `Jjoint`, `comparisonSet`, negative Exact-GR theorem |
| `X1/FiniteOutputs.lean` | `baselineProperty_eq_kernelTerminal`, `constitutiveEffect_eq_finiteEffect`, `constitutiveMargin_eq_finiteInf` |
| `X1/MPECertificate.lean` | Both-player Bellman and pure/real-mixed one-shot inequalities |
| `X1/OccupationTargets.lean` | Rational-to-actual baseline atoms and Poisson target identification |
| `MultiAgent/Protocols.lean` | Strict action/update key factorization and exogenous common update |
| `ReverseSolver/ResidenceEvent.lean` / `ResidenceValue.lean` | Literal event, finite-history probability and existing full-history optimum |
| `ReverseSolver/C11ClassStationaryCertificate.lean` / `C11StationaryFamily.lean` | Exact stationary and complete-family checkers |
| `MultipleLimit/FiniteClassInvariantMeasure.lean` | Finite-class invariant probability existence/uniqueness |
| `Probability/KantorovichDual.lean` / `KantorovichTV.lean` | Existing dual predicate and bounded-diameter conversion |
| `Perturbation/ContractiveOccupation.lean` | Exact global dual contraction predicate, four-process margin theorem |
| `Quotient/ApproxPrefix.lean` / `ApproxMargin.lean` | Existing linear defect bounds and typed comparison interfaces |
| Frozen `Probability/CommonPartKernel.lean` | Measurable common subkernel where its exact typeclass premises hold |

Relative research paths in this table are under `PermanssonResearch/`; the last row is under `PermanssonLean/`. The source-register validator must check the actual filenames: a near-matching theorem title is not a usable import. Provider APIs have to be inspected in the pinned environment before committing new declarations.

## X1 target interface: no ambiguity about the final object

Within namespace `PermanssonResearch.X1`, add an explicit finite type `NumericalVariant` with constructors baseline/action/update/joint. Define its actual model by returning `model m` or the existing `Jaction/Jupdate/Jjoint m` applied model. Define `rationalEntry : Mode -> NumericalVariant -> Y -> Y -> Rat` from X-ATOM, not by taking an opaque real matrix's rational approximation.

The new declarations must establish these exact mathematical signatures:

```text
rationalEntry_nonneg:
  forall mode variant y z, 0 <= rationalEntry mode variant y z

rationalEntry_sum:
  forall mode variant y, sum_z rationalEntry mode variant y z = 1

actualKernel_atom_eq_rationalEntry:
  forall mode variant y z,
  (actualModel mode variant).inducedKernel y {z}
    = ENNReal.ofReal (Rat.cast (rationalEntry mode variant y z))

rationalTerminal_eq_actual:
  forall mode variant n y,
  ENNReal.ofReal (Rat.cast (rationalTerminal mode variant n y))
    = kernelTerminal (actualModel mode variant).inducedKernel n y

checkedTable_equals_rationalTerminal:
  for the declared checked table, every t in {0,1,2,3} and y,
  table[mode,variant,t,y] = rationalTerminal mode variant t y
```

For each of the six constants $c$ in X-MARGIN, the final declaration concludes, using the **existing** definitions and objects:

```text
constitutiveMargin
  (model m) (specification m) (family m) property (comparisonSet m) (Jkind m)
    = (c : Real)
```

These are interface specifications, not precompiled Lean snippets. Do not leave `sorry`, a custom axiom, a Boolean `accepted=true` field, `native_decide`, or an external numerical oracle in their place. Normal kernel-checked rational reflection and theorem application are permitted. A table-check theorem should reduce to finite exact equations and inequalities, followed by a general soundness theorem linking it to the actual kernel and original margin.

The candidate table is `certificates/x1_exact_tables.json`. Its serialized content has 8 matrices, 576 horizon values and 54 effect entries. The JSON decoder is not itself trusted mathematical evidence. A generator may emit Lean literals; the resulting terms and equations must be checked by Lean, including mutations of already-emitted literals.

## Generic interface records: fields the agent may not omit

**Action trace.** Finite state/action spaces; initial law; explicit player index; full observed alternating histories; nonanticipating behavioral own-action kernel; independent fixed opponent action kernel conditional on current state; actual conditional world/update law; reward, discount and bounds; exact state-marginal bridge.

**Finite monitor.** Finite state and control sets; nonempty permitted controls; stochastic rows; fixed original deadline; monitor initializer, time-indexed update, terminal reward; history summary recursion; actual history-law pushforward; policy information. Risk and hidden-state variants add their own fields rather than overloading a Boolean goal flag.

**Quotient shared mass.** Fine/coarse spaces, measurable quotient, baseline and coarse Markov kernels, every-row defect, common subkernel, jointly measurable density/lift theorem, matched starts/initial common mass. Any countably-generated or standard-Borel premise appears in the exported theorem.

**Contractive model.** Metric and Borel compatibility; Markov kernel; exact source `IsW1Contraction` or an explicitly different first-moment restriction; finite initial dual gap; invariant probabilities or a theorem generating them; both row-error budgets; explicit property and all four actual factorizations. A `P1`-only Lipschitz functional cannot be passed to the existing all-probability-law predicate without an extension theorem.

**Strict autonomy.** The original `TwoPlayerGenerator` product structure, common-update exogeneity, own-key factors, baseline initial law, baseline support/AE occupation at every time, supported action and update agreement, common treated mechanism and physical world. A support agreement on a single output is not mechanism agreement.

**Stationary family.** Positive state count, actual rational matrix, genuine bottom classes, canonical class enumeration, explicit rational determinant solver, full-state nonnegativity/normalization/support/balance, and original C11 typed identification.

**Specialized transfer.** The finite algebraic spaces and maps; exact symmetry/conjugation convention; every sign, rank, dimension, range, continuity or nonzero denominator assumption; and an actual model-to-feature identity. The adapter must expose an unmet model hypothesis instead of constructing a certificate from a filename.

## Proof-oriented build sequence

The following are work units, not promised GitHub PR numbers. Dependencies shown are mathematical, not chronological obligations to finish every preceding row.

| Unit | New proof content | Entry condition |
|---|---|---|
| U01 | X-ATOM and rational kernel typing | Existing X1 source read and unchanged |
| U02 | X-DP, exact table checking, X-MARGIN | U01 |
| U03 | S-TRACE, S-VERIFY, S-X1 | Existing MPE conditions; independent of U02 |
| U04 | M-AUTONOMY, M-CLOSURE, finite M-NOSEPARATION | Exact strict/support hypotheses reviewed |
| U05 | D-MONITOR and behavioral law bridge | Existing D1/D2 law interfaces |
| U06 | D-RESIDENCE, D-FIRST, D-AVOID | U05 |
| U07 | C11-REFERENCE/NULL/CHECK | Existing C2/C10/C11 foundations |
| U08 | Q-LIFT and Q-GEOMETRIC | Common-kernel/RN instance audit |
| U09 | A-CONTRACT and A-FACTOR-FIN | Existing dual calculus and C2 |
| U10 | Finite KR and invariant construction | Finite linear-algebra/transport records |
| U11 | A-KR-POLISH/COMPLETE, larger factorization | Analytic dependencies checked individually |
| U12 | D-LP and robust stage games | U05 and exact polytope constructor |
| U13 | D-BELIEF and D-SAFETY | Separate hidden-state and infinite-event specifications |
| U14 | F-SWAP, F-N, F-CLOCK, F-FEAS, F-LUMP, F-CORR | Exact permitted information per target |
| U15 | B-OVERLAP/LOCAL-ORDER and D-BLOCK/CLASS | Existing grammar, U05; C11 for class outputs |
| U16 | C-CLUSTER/RANDOM/FAMILY | Compactness, conditional law and ergodic APIs |
| U17 | XPLUS model and original grounded PR | U03 plus existing GR/grounded constructors |
| U18 | Specialized finite algebra and adapter contracts | Each source-specific hypothesis approved |

F-CAUSE is separately reviewed as an SCM identification/nonidentification target and is not inserted into the protocol-distance theorem. Q-LOCAL/DISCOUNT/REGIME and A-PRIMITIVE are wrappers after their stated input lemmas, not additional universal assumptions.

## Independent acceptance obligations

For every theorem, report the exact statement, source file, declaration name, hypotheses, reused declarations, proof method, new test methods and residual nonclaims. The supplied `registries/acceptance_tests.json` lists required adversarial objectives. At minimum:

- **X1:** all eight actual kernel mappings, all 18 states, all nine comparison starts, all six original margins; changed world/update timing, horizon, denominator, omitted start, mislabeled intervention and corrupted emitted Lean literal must be rejected for the intended reason.
- **Strategies:** a nonstationary allowed policy and exact finite telescoping identity including terminal value; exclude current-opponent/future-noise access; test both indexed players and all starts.
- **Autonomy:** positivity/support closure, stochastic anchors, update agreement and exogenous common coordinate; a reactive counterexample must fail a hypothesis, not be counted as strict MA2.
- **Quotients/metrics:** non-Markov projection, every-row defects, zero/one error boundaries, nontrivial horizons, unbounded-distance TV failure, and one missing member of the four-process factorization.
- **Solvers:** literal-word event equivalence, time zero and $m=0$, retries, danger precedence, hidden monitor state, randomization when risk demands it, nonrectangular nature, and finite versus infinite survival.
- **Stationary/grammar/specialized:** periodic classes, complete class lists, singular matrices, source dimension/coupling consistency, incompatible overlapping patches, nonmonotone positivity and rank-two rather than rank-one seam defects.

Fixture tests do not replace a generic theorem. A negative test must be rejected by the claim it attacks: invalid JSON is not evidence that the Lean checker rejects a false arithmetic theorem. A resource timeout is not a mathematical counterexample or impossibility proof.

## Formal integration and protected history

Use additive files under `PermanssonResearch/`, direct root imports and separately named executable tests. Existing protected historical files, manuscript/export bytes, application schema and dependency pins stay unchanged. Do not rewrite a frozen calculation receipt to mark a new theorem proved; issue new versioned evidence and update only the appropriate nonfrozen current crosswalk.

The exact-source acceptance process remains: current head and genuine synthetic-merge build; original and research Lean targets; transitive axiom allowlist; source placeholder scan; full executable/application/integrity checks; appropriate new theorem-level adversaries; independently reviewed statement scope; and explicit user-controlled merge. The one-time no-Lean-change condition from maintenance PR #77 does **not** apply to new research PRs; the permanent frozen-source boundary still does.

A new focused workflow can interact with the hardening contract's reviewed workflow inventory. Do not bypass that checker. Prefer the existing full research discovery/import/audit path until a separate reviewed workflow-profile change is genuinely required.

## Honest completion labels

A paper derivation here can become a Lean theorem in exactly its selected scope. The five optional specialized rows cannot become universal GR/PR results merely because their linear algebra compiles. General-state rows cannot lose tightness/Borel/moment premises, and risk or robust rows cannot lose policy/nature order.

Final closure of any broader atlas goal requires listing the residual question and either proving it, producing a valid impossibility theorem, or retaining it as open. This package makes the coding contract exact; it does not turn broad research phrases into unqualified existence claims.


\newpage

# Atlas-to-theorem coverage and residual scope

Every input atlas ID occurs once. These counts describe mapped work packages, not universal solved theorems or new Lean declarations.

| Atlas ID | Paper derivations | Disposition |
|---|---|---|
| X1-N01 | X-ATOM | PAPER DERIVATION |
| X1-N02 | X-DP, X-TABLE | PAPER DERIVATION |
| X1-N03 | X-MARGIN | PAPER DERIVATION |
| X1-S01 | S-TRACE, S-VERIFY, S-X1 | PAPER DERIVATION |
| F1-MA2 | M-DATA, M-AUTONOMY, M-CLOSURE, M-NOSEPARATION | SCOPED DERIVATION |
| E1-G01 | Q-LIFT, Q-GEOMETRIC | SCOPED DERIVATION |
| A3-K01 | A-KR-FIN, A-KR-POLISH | SCOPED DERIVATION |
| A3-I01 | A-COMPLETE, A-INVARIANT | SCOPED DERIVATION |
| A3-C01 | A-CONTRACT | PAPER DERIVATION |
| A3-F01 | A-FACTOR-FIN, A-FACTOR-REGEN | SCOPED DERIVATION |
| A3-P01 | A-PRIMITIVE | SCOPED DERIVATION |
| D2-R01 | D-MONITOR, D-RESIDENCE | PAPER DERIVATION |
| A2-P01 | Q-PRIMITIVE | PAPER DERIVATION |
| A2-P02 | Q-LOCAL | SCOPED DERIVATION |
| E1-P01 | Q-DISCOUNT | SCOPED DERIVATION |
| E1-P02 | Q-REGIME | SCOPED DERIVATION |
| F1-P01 | F-SWAP | PAPER DERIVATION |
| F1-P02 | F-N | PAPER DERIVATION |
| F1-P03 | F-CLOCK | SCOPED DERIVATION |
| F1-P04 | F-FEAS | SCOPED DERIVATION |
| F1-P05 | F-LUMP | SCOPED DERIVATION |
| F1-P06 | F-CORR | SCOPED DERIVATION |
| F1-P07 | F-CAUSE | SCOPED DERIVATION |
| D2-P01 | D-MONITOR | PAPER DERIVATION |
| D2-P02 | D-FIRST | PAPER DERIVATION |
| D2-P03 | D-AVOID | PAPER DERIVATION |
| D2-P04 | D-LP | SCOPED DERIVATION |
| D2-P05 | D-ROBUST | SCOPED DERIVATION |
| D2-P06 | D-BELIEF | SCOPED DERIVATION |
| D2-P07 | D-SAFETY | SCOPED DERIVATION |
| D2-P08 | D-BLOCK | PAPER DERIVATION |
| D2-P09 | D-CLASS | SCOPED DERIVATION |
| C11-P01 | C11-REFERENCE, C11-NULL, C11-CHECK | PAPER DERIVATION |
| C-P01 | C-CLUSTER, C-RANDOM, C-FAMILY | SCOPED DERIVATION |
| B-P01 | B-OVERLAP, B-ORDER | SCOPED DERIVATION |
| B-P02 | B-LOCAL-ORDER | SCOPED DERIVATION |
| X1-P01 | XPLUS, XPLUS-EQ, XPLUS-GR, XPLUS-PR | SCOPED DERIVATION |
| APP-E01 | E-SCALAR | CONDITIONAL TRANSFER |
| APP-E02 | E-DETECT | CONDITIONAL TRANSFER |
| APP-E03 | E-SHELL | CONDITIONAL TRANSFER |
| APP-E04 | E-SINGULAR, E-SOURCE | CONDITIONAL TRANSFER |
| APP-E05 | E-GRAM | CONDITIONAL TRANSFER |

## Residual scopes

**X1-N01** — None inside the fixed finite atom target; general intervention families are not claimed.

**X1-N02** — No arbitrary external JSON decoder or approximate arithmetic correctness theorem.

**X1-N03** — No Exact-GR/PR promotion; the old replete region remains leaky.

**X1-S01** — Clairvoyant/correlated-current-noise, risk-sensitive or strategic-world-changing deviations are excluded.

**F1-MA2** — Impossibility is scoped to these exact information and agreement premises; arbitrary measurable targets and weaker agreement are not universally resolved.

**E1-G01** — Arbitrary measurable spaces without the stated density/common-kernel bridge remain outside the proof.

**A3-K01** — No equality for arbitrary sigma-algebras, no implicit first moments or supnorm-one replacement.

**A3-I01** — Only uniqueness within the declared class; perturbed invariant uniqueness needs its own sufficient condition.

**A3-C01** — Does not need general KR for the direct dual result; unbounded metrics cannot silently use a TV coefficient.

**A3-F01** — Not factorization of every arbitrary preexisting property; regeneration/analytic prerequisites remain explicit.

**A3-P01** — Coupling interpretation uses KR when needed; bounded-diameter TV wrapper reuses existing theorem without that dependency.

**D2-R01** — No physical absorption or arbitrary nonlinear objective; entry and completion deadlines remain distinct.

**A2-P01** — The shared-mass lemmas are reused; no independence of error events is assumed.

**A2-P02** — Empirical identification and arbitrary numerical uncertainty are not inferred from deterministic output-error ledgers.

**E1-P01** — Generic tail/survival functionals under fixed positive defect are not stable.

**E1-P02** — Small approximate defect alone cannot transfer exact invariance or full PR status.

**F1-P01** — No symmetry assumption on the actual world or rewards.

**F1-P02** — Not all correlated games; countably infinite products are not this target.

**F1-P03** — An endogenous common clock is not strict; the frozen baseline is not altered.

**F1-P04** — General measurable selection and arbitrary nonrectangular joint constraints require separate statements.

**F1-P05** — Structural causal exogeneity is not identified from one observed law or an unmarked state process.

**F1-P06** — The mediator law is not automatically exogenous or publicly observed.

**F1-P07** — Dynamic adaptation requires a separate sequential SCM and identification bridge.

**D2-P01** — Does not extend deterministic sufficiency to risk-constrained or hidden-model robust objectives.

**D2-P02** — No substitution for the existing retryable event.

**D2-P03** — Other post-success risk conventions require separately named events.

**D2-P04** — Polynomial efficiency is not proved; more general risk functionals require new state/convexity results.

**D2-P05** — Static hidden model commitment is not rectangular; no generic max/min interchange.

**D2-P06** — Arbitrary belief-dependent menus, empirical identification and general infinite-horizon POMDP theory are excluded.

**D2-P07** — General nonfinite infinite retention or finite-horizon extrapolation is not supplied.

**D2-P08** — Overlapping incompatible patches and post-draw unauthorized control choice remain inadmissible.

**D2-P09** — All-history asymptotic synthesis, MEC/mean-payoff objectives remain a broader unproved target.

**C11-P01** — No verified external parser or runtime scalability claim; C10 total absorption is already proved.

**C-P01** — Arbitrary nonfinite/measurable all-initial-law convergence is false; noncompact tightness and conditional-law hypotheses remain explicit.

**B-P01** — Arbitrary conflicting patches require declared priority/order semantics rather than this commutative theorem.

**B-P02** — No arbitrary bijection or coarsening preserves minimality; positivity need not be monotone.

**X1-P01** — Not original X1, not empirical calibration or authenticated preregistration; no learner comparison is asserted.

**APP-E01** — Actual Permansson feature-matrix identification and source-specific complex variant remain separate.

**APP-E02** — Actual legal source approximation/feature bridge and existence of a strict witness must be supplied.

**APP-E03** — One-dimensional cubic shell and actual source intertwining are not generic; no elimination of all first-bad states.

**APP-E04** — No unjustified inverse, no nonzero Gamma conclusion, and no automatic production-source identification.

**APP-E05** — Other PSD summands can mask the witness; actual path-feature and legal-witness realization remain separate.



\newpage

# X1 exact arithmetic appendix

These are candidate rational certificate literals, computed independently for this paper specification. The final Lean implementation must prove their equality to the actual typed kernels and original property. Full state order, matrices, all horizons zero through three and all 54 effects are in `certificates/x1_exact_tables.json`.

## Horizon-three outputs at all nine replete starts

For E, all nine starts have baseline and reset value $\frac{227}{500}$, and action/joint value $\frac{3171}{4000}$. The corresponding effects are $\frac{271}{800}$, $0$, $\frac{271}{800}$.

For L the following table retains every start. Action and joint terminal values coincide, but their full next-state and path laws need not coincide.

| Memory $(q_1,q_2)$ | Baseline | Action or joint | Update reset |
|---|---:|---:|---:|
| $(0,0)$ | $\frac{2062936471}{6400000000}$ | $\frac{3171}{4000}$ | $\frac{20543}{51200}$ |
| $(0,1)$ | $\frac{686994469}{2560000000}$ | $\frac{3171}{4000}$ | $\frac{185549}{512000}$ |
| $(0,2)$ | $\frac{121690031}{512000000}$ | $\frac{3171}{4000}$ | $\frac{41417}{128000}$ |
| $(1,0)$ | $\frac{686994469}{2560000000}$ | $\frac{3171}{4000}$ | $\frac{185549}{512000}$ |
| $(1,1)$ | $\frac{8381459}{32000000}$ | $\frac{3171}{4000}$ | $\frac{41417}{128000}$ |
| $(1,2)$ | $\frac{1172162957}{5120000000}$ | $\frac{3171}{4000}$ | $\frac{145787}{512000}$ |
| $(2,0)$ | $\frac{121690031}{512000000}$ | $\frac{3171}{4000}$ | $\frac{41417}{128000}$ |
| $(2,1)$ | $\frac{1172162957}{5120000000}$ | $\frac{3171}{4000}$ | $\frac{145787}{512000}$ |
| $(2,2)$ | $\frac{5050479049}{25600000000}$ | $\frac{3171}{4000}$ | $\frac{62953}{256000}$ |

## Exact absolute effects

| Memory | Action or joint effect | Update effect |
|---|---:|---:|
| $(0,0)$ | $\frac{3010663529}{6400000000}$ | $\frac{504938529}{6400000000}$ |
| $(0,1)$ | $\frac{1342445531}{2560000000}$ | $\frac{240750531}{2560000000}$ |
| $(0,2)$ | $\frac{284197969}{512000000}$ | $\frac{43977969}{512000000}$ |
| $(1,0)$ | $\frac{1342445531}{2560000000}$ | $\frac{240750531}{2560000000}$ |
| $(1,1)$ | $\frac{16986541}{32000000}$ | $\frac{1972791}{32000000}$ |
| $(1,2)$ | $\frac{2886717043}{5120000000}$ | $\frac{285707043}{5120000000}$ |
| $(2,0)$ | $\frac{284197969}{512000000}$ | $\frac{43977969}{512000000}$ |
| $(2,1)$ | $\frac{2886717043}{5120000000}$ | $\frac{285707043}{5120000000}$ |
| $(2,2)$ | $\frac{15243920951}{25600000000}$ | $\frac{1244820951}{25600000000}$ |

The learner action/joint infimum is attained at $(0,0)$; its update infimum at $(2,2)$. An illustrative point calculation at $(1,1)$ cannot replace either full comparison-domain minimum.

## Executed-check record

The included independent checker passed 27 test methods with zero failures, errors or skips. It additionally rejects mutations of each of the 54 supplied absolute effects, each of the six minima, a minimizing start, a stochastic-but-wrong matrix, a horizon, a table entry and intervention labels. This is executed finite evidence, not a deductive check of the entire manuscript or a Lean build.


\newpage

# Source references

All repository references below are pinned to `39279799834ae536bda715dedecdc11a32bf6c82`. Full URLs and byte hashes are in `sources/source_register.json` and `SOURCE_REGISTER.md`. These sources establish the pre-existing interfaces and limits. New paper derivations are not attributed to an old source merely because they reuse its definitions.

**SRC-001** — Research / X1/Parameters.lean

**SRC-002** — Research / X1/TypedModels.lean

**SRC-003** — Research / X1/Comparison.lean

**SRC-004** — Research / X1/FiniteOutputs.lean

**SRC-005** — Research / X1/MPECertificate.lean

**SRC-006** — Research / X1/OccupationNumerics.lean

**SRC-007** — Research / X1/OccupationTargets.lean

**SRC-008** — Research / MultiAgent/Protocols.lean

**SRC-009** — Research / MultiAgent/ProductGame.lean

**SRC-010** — Research / MultiAgent/ProtocolWitnesses.lean

**SRC-011** — Research / MultiAgent/AdaptationBound.lean

**SRC-012** — Research / ReverseSolver/ResidenceEvent.lean

**SRC-013** — Research / ReverseSolver/ResidenceValue.lean

**SRC-014** — Research / ReverseSolver/ResidenceContracts.lean

**SRC-015** — Research / ReverseSolver/C11ClassStationaryCertificate.lean

**SRC-016** — Research / ReverseSolver/C11StationaryFamily.lean

**SRC-017** — Research / ReverseSolver/C11TypedStationaryBridge.lean

**SRC-018** — Research / ReverseSolver/RationalCramerCertification.lean

**SRC-019** — Research / MultipleLimit/FiniteClassInvariantMeasure.lean

**SRC-020** — Research / Probability/KantorovichDual.lean

**SRC-021** — Research / Probability/KantorovichTV.lean

**SRC-022** — Research / Probability/EventTVCalculus.lean

**SRC-023** — Research / Perturbation/ContractiveOccupation.lean

**SRC-024** — Research / Perturbation/PrimitiveTV.lean

**SRC-025** — Research / Quotient/ApproxPrefix.lean

**SRC-026** — Research / Quotient/ApproxMargin.lean

**SRC-027** — Core / Probability/CommonPartKernel.lean

**SRC-028** — Core / Regime/ConstitutiveMargin.lean

**SRC-029** — Core / Regime/GeneratedRegime.lean

**SRC-030** — docs/V020\_IMPLEMENTATION\_INDEX.md

**SRC-031** — docs/PERMANSSON\_V020\_MATHEMATICAL\_INTEGRATION\_SPEC.md

**SRC-032** — docs/LANE\_X1\_COMMONS.md

**SRC-033** — docs/D2\_RESIDENCE\_OBJECTIVE.md

**SRC-034** — docs/LANE\_F1\_MULTIAGENT\_PROTOCOLS.md

**SRC-035** — docs/LANE\_A3\_CONTRACTIVE.md

**SRC-036** — docs/LANE\_E1\_APPROX\_QUOTIENT.md

**SRC-037** — Specialized source / README.md

**SRC-038** — verification/research/x1\_commons.py

**SRC-039** — verification/research/test\_x1\_commons.py

**SRC-040** — docs/x1/commons-calculation.json

**SRC-041** — Specialized source / Explicit\_Gram\_Witnesses\_Off\_Critical\_Pair\_Blocks\_2026-08-25\_v1\_2\_PROOFREAD.pdf

**SRC-042** — Specialized source / Scalar\_Defect\_Reduction\_Finite\_Weil\_CCM\_Dictionaries\_2026-08-30\_v0\_1\_PROOFREAD.pdf

**SRC-043** — Specialized source / Zero\_Shift\_Source\_Rigidity\_Weil\_CCM\_2026-09-10\_v0\_3.pdf

**SRC-044** — Specialized source / First\_Bad\_Cubic\_Rigidity\_Weil\_CCM\_2026-09-08\_v0\_2.pdf

**SRC-045** — Specialized source / Persistent\_Finite\_Detection\_Off\_Critical\_Zeros\_Weil\_CCM\_2026-09-03\_v0\_2.pdf


**Analytic background:** Martin Hairer, *Convergence of Markov Processes* (26 May 2021); official mathlib kernel Radon–Nikodym and matrix adjugate documentation. Online documentation is not a substitute for checking the pinned library. Full references are in the companion source register.