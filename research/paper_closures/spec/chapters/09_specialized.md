# E — Five specialized algebraic transfer contracts

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
