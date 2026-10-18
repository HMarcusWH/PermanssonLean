# Q — Shared-mass proofs and quantitative transport

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
