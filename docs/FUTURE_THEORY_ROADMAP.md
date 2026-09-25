# Future Permansson theory roadmap

**RESEARCH / NOT PART OF v0.1.8. No theorem-completion claim is made here.**

These are proposed next research directions, not missing proofs in the frozen
core. The [formalization map](FORMALIZATION_MAP.md), v0.1.8 paper, immutable Lean
snapshot and Appendix E non-core boundary retain their existing scope.

## A. Constitutive quasi-regimes

Starting point: v0.1.8 Sections 4.2-4.4 already define killed-kernel finite
persistence and optional QSD certification; Section 5 separately defines strategic
constitution. A finite-horizon constitutive certificate could combine these without
weakening the definition of Exact PR.

Work to do: freeze the horizon, survival requirement, descriptor/property, basin
and intervention; define a subordinate finite-horizon class; prove the exact
hypothesis-to-certificate implications; carry property-output error budgets and
support/identification uncertainty through the finite comparison. Keep a QSD
certificate independent of the statewise finite-survival requirement.

Acceptance tests: positive examples, leaky/zero-margin counterexamples, off-by-one
exit tests, adversarial QSD examples, and a direct theorem/Lean interface. Do not
rename a finite-survival result `ROBUST_PR` under the existing application schema.

## B. Grammar-robust constitution

Starting point: Section 5.4 says component attribution is grammar-relative. Compound
blocks may matter when singleton interventions do not. A change in coordinates is
not automatically a matched substantive intervention.

Work to do: specify a frozen family of admissible component decompositions and
semantic transport maps; distinguish minimal constitutive blocks, joint necessity,
substitutability and invariance across matched grammars. Determine which statements
require closure assumptions; do not assume a unique minimal grammar or monotonicity
of constitutive effects under aggregation.

Acceptance tests: synergistic and redundant components, incomparable minimal sets,
reparameterization counterexamples, hard target-closure failures, and a preservation
theorem with explicit hypotheses. Existing intervention-family equivalence is a
starting substrate, not an already-proved grammar-lattice theorem.

## C. Multiple-limit / regime-family semantics

Starting point: Definition 4.3 requires one declared limiting occupation law across
the admissible basin. A future regime-family object might permit initial-state-
dependent limiting laws or an ex ante set of admissible limits.

Work to do: distinguish convergence to a set, convergence to a random law, and
state-indexed deterministic limits; specify topology, measurability, initial-law
quantifiers and intervention transport; prove conservative recovery when the limit
family is a singleton. A large post-hoc set containing every observed outcome is
not a substantive classification.

Acceptance tests: multistability, mixtures of recurrent classes, nonconvergent
occupation sequences and overbroad limit sets; then a direct GR/PR transfer result
and a versioned application contract. Do not silently replace nu in v0.1.8.

## Promotion rule

Each lane needs a stable definition, explicit scope, proof and counterexamples,
executable tests, paper-to-Lean crosswalk, and its own version/release boundary.
Until those exist, no stubs or assumed theorems are added to `PermanssonLean/`.
The application standard only records existing theory; it does not implement these
research lanes by issuing stronger labels.
