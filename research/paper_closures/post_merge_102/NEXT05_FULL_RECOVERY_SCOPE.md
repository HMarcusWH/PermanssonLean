# NEXT-05.1 implementation — current-source update and kernel bridge

**Actual integration base:** `6bc86eaa71fb26a5e86e2d7ffd88e4c1af4f0760`. **Status: compiler verification pending; NOT_ACCEPTED.**
This candidate ports the pre-existing unmerged `MeasurableProductTwoUpdate.lean`
source from legacy branch `research/next05-measurable-kernel` (base
`3931e4dccafb47b3cdf70177c0cf337102c90731`) onto the verified
post-PR106 current main *without overwriting* the historical branch.

## Mathematical commitments

- Original arbitrary-measurable two-player `Fin 2` conditional-product
  generator, common/private strategic memories and distinct physical world.
- Full strategic update output pushes through the **strategic** map; it never
  sends an S-valued measure through the joint-state Y map.
- Action and physical row reindexing preserve **both** realized actions and
  the genuine next-world state; no player symmetry assumption.
- The required next step is an unconditional **induced-kernel intertwining**
  proof via all measurable events, using the original kernel, not a sampled
  atom/finite singleton surrogate.
- P-05.2 CL/OL, entire infinite path and margin transport are explicitly
  separate; no empirical/GR/PR certification follows.

## Acceptance gates

Do not certify the lane until the new update **and kernel** modules compile
in the pinned Lean 4.34.0 environment with permitted transitive axioms,
well-typed semantic false-target mutants are rejected for mathematical
reasons, nonfinite measurable types are checked, and all original preservation,
application and Research Lean workflows pass on true GitHub B/H/S.
Historical P-AUDIT full45 and scoped release modes remain pending.

No changes to frozen original core, historical research providers, locks or
publication artifacts.
