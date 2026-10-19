# NEXT-06 / B-01 compatible and conflicting overlaps

This Lean fixture uses the original `RowPatch.Compatible`, `applyCompatiblePatches_active` and `applyRowPatch_selected` APIs on a genuine overlapping input row in the finite measurable `Bool` space.

- Two different masks (`univ` and `{false}`) with an identical deterministic-true replacement agree on their nonempty overlap; the original generic theorem supplies the assembled row.
- An alternative patch has the same nonempty overlap but deterministic-false replacement. The genuine Dirac row measures differ, so `Compatible` is false and the **raw** folding order matters.

The raw fold is not a compatibility validator. Admission of only certified compatible patches, and any larger typed strategic-world and joint-only block construction, remain separate obligations. This fixture does not resolve D-08 or substitute a fabricated PR status. No frozen core changes; pinned full Lean compilation and genuine H/S CI required.
