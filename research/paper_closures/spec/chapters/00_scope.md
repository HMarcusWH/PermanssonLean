# Mathematical build contract: scope and authority

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
