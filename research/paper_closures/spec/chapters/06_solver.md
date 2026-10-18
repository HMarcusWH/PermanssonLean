# D — One finite-monitor theorem and its solver consequences

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
