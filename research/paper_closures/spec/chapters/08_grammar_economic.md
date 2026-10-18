# B and X+ — Compatible grammar extensions and a new positive economic witness

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
