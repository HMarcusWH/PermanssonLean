# A — Deriving the long-run robustness inputs

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
