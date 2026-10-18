# C — Total stationary certificates and nonfinite occupation scope

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
