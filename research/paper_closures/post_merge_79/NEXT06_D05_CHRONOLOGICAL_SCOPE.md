# NEXT-06 / D-05 — actual two-stage path-law separation

The previously compiled `SolverBoundaryWitnesses.whole_model_commitment_strictly_exceeds_rectangular` is exact **scalar arithmetic**. This new witness defines all four atoms of a normalized two-observation finite probability law with one fixed model across both stages (two possible committed models) or a row-reselected model on the second stage. It applies `FiniteProbabilityLaw.expectation` to the same path event (`stage0 success AND stage1 success`) in both protocol classes.

At the two fixed model choices, the event probability is 9/100 for each; for the switching two-stage nature choice it is 1/100. These are actual constructed path probabilities; their independent Python rational enumeration has four tests.

**Boundary:** This finite fixture does NOT identify an unobserved real model, assert that an arbitrary controller/nature policy has the same law, or replace the `RectangularFiniteGame` general saddle theorem. It instantiates a nontrivial chronological probability-law distinction with explicitly declared conditional row products. The new Lean source remains unaccepted until actual pinned compiler and axiom checks pass. Historical scalar theorem and all frozen source files remain unchanged.
