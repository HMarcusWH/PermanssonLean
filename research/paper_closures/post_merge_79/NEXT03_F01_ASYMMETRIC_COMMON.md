# NEXT-03 / F-01 — actual asymmetric player swap

This Lean fixture instantiates the original typed `TwoPlayerGenerator` with different deterministic player-one/player-two actions and a physical kernel and common strategic-update kernel that both depend on the first action. Reindexing the realized action pair produces a different physical event and different common-update event. The tests invoke the **actual `PlayerSwap.generator` and `PlayerSwap.physical` implementations**, not an abstract coordinate permutation; the initial state and action rows are explicit. The same concrete model instantiates the existing full canonical `PlayerSwap.actual_pathLaw` theorem.

A positive Lean compiler run is followed by a syntactically well-typed false-value mutation in the actual common-update theorem. Its failure must be a semantic proof rejection rather than a missing import, parser or resource failure.

Scope is finite Boolean F-01 asymmetric swap acceptance. It does not prove arbitrary-measurable player product recovery (NEXT-05), any general correlated product, or real-world causal identification. No original module/pin edits.
