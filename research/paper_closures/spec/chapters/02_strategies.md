# S — Unrestricted discounted-strategy verification

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
