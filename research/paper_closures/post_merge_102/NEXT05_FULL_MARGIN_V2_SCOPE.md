# NEXT-05.2 full-path original-margin matched-protocol adapter

B=5c43060060be6b29ce1c626dd05c1fde7b98bb37.
Source: MeasurableProductTwoMargin.lean.
The source defines the original whole-path pullback of the *same* coarse
RegimePropertyMap, proves baseline full path equality, and shows intervention
equality under a separately admitted binary-side Jbar and exact typed
kernel-intertwining hJ. A full original B1 infimum is used without dropping
starts, under the explicit equality Bbar1.states = q.stateMap '' B1.states.

Caveat: This does not itself construct the binary intervention family
matching the source CL/OL protocols. Finite and measurable conditional-product
generator CL/OL constructors and the source/binary canonical-path theorems
provide inputs, but the final Jbar/hJ adapter for each CL/OL is separate
and must be proved before unconditional claim promotion.

CI compiler check and axiom audit required; numerical checks are not Lean.
