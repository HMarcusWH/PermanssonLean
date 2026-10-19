# NEXT-06 / B-02 non-global local order fixture

`PermanssonResearch/GrammarRobust/LocalOrderPositiveFixture.lean` instantiates the existing `minimalPositive_iff_of_lowerSet_lifting` at the actual `Nat` lower set below 2 using the tail-collapsing map `folded n=min n 2`.

This map is **provably not globally injective**, and thus is not a global order isomorphism. It nevertheless transports the **entire** strict lower set of the selected element. The fixed positive predicate is `n=2`; both sides of the existing original local-minimality theorem are nonvacuously satisfied. No positivity-monotonicity or unique-minimizer assumption is substituted.

The fixture addresses the positive B-02 local-order acceptance gap. It is not a theorem about arbitrary regime properties or an empirical regime. The other NEXT-06 cases (D-05 committed nature, D-06 hidden completion flag, D-08 joint-only certified controls, D-09 nonlinear policy-class boundary and B-01 raw overlap conflicts) still need their own model-bound fixtures.

No modification to existing theorem providers or frozen core. Pinned Lean 4.34, full Research axiom and original build, negative review, source-bound H/S, and preservation gates are required before formal acceptance.
