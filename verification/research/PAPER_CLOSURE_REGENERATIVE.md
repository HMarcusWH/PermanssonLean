# Nonfinite regenerative occupation factorization

This track uses an actual original Markov kernel with a supplied every-row
decomposition `K = ε seed + (1−ε) R`, with `0 < ε ≤ 1`. The implementation
uses `r=1−ε`, including `r=0`, and supplies an explicit epsilon constructor.
It imposes no finite-state or Feller premise on the regenerative theorem.

The geometric measure `(1−r) Σ rⁿ seed Rⁿ` is constructed and proved to have
mass one and to be invariant under the original kernel. For every bounded
measurable observable, the actual residual-kernel resolvent is measurable,
bounded by `M/(1−r)`, and solves the original kernel's Poisson equation with
the geometric law's expectation. The previously verified actual canonical
bounded-innovation strong law and a bounded endpoint telescope then prove
all-initial time-average convergence, with the original time-zero-inclusive
positive-horizon convention.

For weak empirical convergence on noncompact second-countable spaces, the
proof uses indicators of finite intersections of a countable topological
basis. These form a countable measurable neighborhood pi-system. One shared
almost-sure event and the pinned pi-system Portmanteau theorem give actual
weak empirical convergence. No noncompact uniform density of all bounded
continuous functions is used.

The general full-path observable is the real limit of a fixed bounded
continuous functional of the descriptor empirical laws, with fixed default
`Φ(fallback)`. Its measurable construction is independent of all compared
kernels. Whenever the actual descriptor empirical laws converge to `ν`,
the observable equals `Φ(ν)`. The resulting original path-probability
functional therefore factors for all four actual baseline/intervention
typed models and every comparison start. For compact descriptors, a
separate literal measurable probability-valued limit with a fixed fallback
law gives the corresponding full-path factorization as well.

The original constitutive-margin comparison keeps its full comparison sets,
the original global dual-Lipschitz functional predicate, both baseline
contraction bounds and every-row defects. Both invariant laws are generated
from regeneration. Explicit first moments of the constructed laws discharge
the original finite-gap gate; no perturbed-kernel contraction is added.

All eleven Lean sources compile under pinned Lean 4.34.0. The discovered
integration test passed, freshly auditing all 87 named declarations and their
transitive axioms; the source-bound receipt permits only `propext`,
`Classical.choice`, and `Quot.sound`. The noncompact real-line half-reset
regression covers every initial law and rejects a false reset decomposition.

A general global measurable probability-valued weak
limit selector and unbounded-descriptor empirical Wasserstein convergence
with its tail and moment conditions remain separate construction obligations.
