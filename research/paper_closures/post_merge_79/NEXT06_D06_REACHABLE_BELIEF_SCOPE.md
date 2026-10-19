# NEXT-06 / D-06 — two reachable histories from the same fixed initial law

A single initial hidden-completion prior `pure false` is coupled to one action-observation model. A fair observation-admissible controller chooses false or true with probability 1/2 independently of the hidden flag. Each action is recorded in the observable word and the physical readout is always `Unit`. The hidden completion flag becomes the actual chosen action. Thus the two different one-step observable words are reachable with probability 1/2 each *in the same chronological law*, and the posterior completion belief is respectively 0 or 1.

The Lean source uses the existing `Model.chronological_word_integral`, `Model.filter` and `ObservationPolicy` interfaces; it does not compare two unrelated pure initial priors. Independent Python tests calculate the joint event probabilities, branch denominators, and posterior values using exact Fractions.

**Scope:** This demonstrates necessity of the full augmented completion flag even when physical observations are identical. It does not claim that a controller can observe hidden flags directly, that an unmarked observable history suffices to identify every empirical hidden model, or that arbitrary policies admit a stronger original theorem. No original source changes. This is a new source pending genuine Lean 4.34.0 and transitive axiom verification.
