# NEXT-05.1 — Measurable two-player update and full induced-kernel bridge

**Draft status: NOT_ACCEPTED / source and CI review pending.**

**B:** `6bc86eaa71fb26a5e86e2d7ffd88e4c1af4f0760`
(the verified post-PR106 integrated baseline). The older unmerged
`research/next05-measurable-kernel` branch, based on
`3931e4dccafb47b3cdf70177c0cf337102c90731`,
was preserved unchanged; the candidate update source was ported onto
a new branch and its ill-typed heterogeneous private-kernel lemma repaired.

## Exact implemented candidate scope

- `MeasurableProductTwoUpdate.lean`: separate `φS` strategic-output
  equivalence and inverse; full `φWorldInput` and `φUpdateInput` realized
  arguments; two differently typed private-output kernel identities; common
  update and `update_map_two` measure pushforward on all measurable sets.
- `MeasurableProductTwoKernel.lean`: source-derived forward world/update
  maps; surjective type-respecting `compression_two`; complete action/world/
  strategic-update kernel conjugacy; `induced_row_map_two` and
  `induced_kernel_intertwines_two` on **every measurable joint-state
  event** through genuine alpha → P → U integration.
- Existing `MeasurableProductTwo.action_map_two` and `MeasurableProduct
  .productKernel_two` are reused unchanged. The finite singleton theorem
  `FiniteProduct.Two.actual_atom` is not used to prove arbitrary-measurable
  equality.
- Tests include pinned compiler theorem/axiom probes, a well-typed false
  private swap, independent rational all-256-transition-atom reproduction,
  mixed non-Dirac initial laws, wrong player action-order, missing realized
  world input, swapped private kernels and correlated-action exclusion.

## Strict limitations and required evidence

The theorem concerns the **conditional-product** generator subclass with
original arbitrary measurable coordinate types. Correlated actions or
updates depending on unmodeled hidden common randomness are not included.
It does not establish original constitutive margins or empirical GR/PR.

The source theorem is merely a **candidate until exact-head and genuine
GitHub synthetic B/H/S checks pass**, including complete Research Lean,
transitive trusted axiom audit `{propext, Classical.choice, Quot.sound}`,
semantic-mutant rejection for proof semantics rather than syntax/resource
failure, and source/integrity/application/workflow preservation. A compiler
failure must not be silently reclassified as partial mathematical success.
The source file and this document alone are not acceptance receipts.

**P-05.2 remains open:** both players' legal CL/OL matched protocol
transport, declared frozen feasible anchors and common physical-world
mechanism, infinite original entire-path law under non-Dirac initial laws,
and any original property/`B₁` constitutive-margin comparison.
Any such claim requires separate compiled proofs and source-bound tests.

No frozen core, previously accepted release, historical PR79 receipt,
existing solver/application provider, toolchain or dependency pin was changed.
No PR merge, tag, paper publication, operational deployment or release
approval is implied by this draft.
