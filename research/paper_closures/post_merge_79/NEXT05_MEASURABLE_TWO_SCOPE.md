# NEXT-05.1 — arbitrary measurable two-player coordinate interface

This small Lean adapter reconstructs a binary original two-player generator
from the existing finite-index product generator with I=Fin 2 but arbitrary
measurable coordinate spaces. It does not require those spaces to have finite
carriers, countable atoms or measurable singletons. The state/world/update
pullbacks retain all realized action/world inputs, including asymmetric
common updates. It proves both coordinate inverse laws and measurability and
an actual action-kernel pushforward identity using the existing measurable
productKernel_two theorem, not a point-atom enumeration.

**Not yet full NEXT-05:** the common/private update kernel conjugacy,
complete induced strategic-world kernel equality, CL/OL intervention-family
transport, initial-law transport and canonical entire-path law equality must
be proved separately. The earlier finite FiniteProductTwo theorem remains
unchanged. No infinite-player or correlated-action assertion is made.

The added Python Research test invokes actual pinned Lean compilation,
checks named declarations and allows only classical choice, propext and
quotient soundness in the printed transitive axiom lists. This proof source
is *not* accepted until the full independent Research/CI pipeline passes.
