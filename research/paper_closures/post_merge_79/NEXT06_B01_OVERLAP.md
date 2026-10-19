# NEXT-06 / B-01: Boolean overlap proof fixture

This additive fixture instantiates the existing `RowPatch.Compatible`, `applyCompatiblePatches_eq_of_membership` and `applyRowPatch_selected` APIs. Two masks (singleton true and the full Boolean input domain) have a genuine, nonempty overlap and the same replacement row. Their order is proved irrelevant. Replacing one with a different deterministic row produces a conflicting overlap whose priority order changes the actual Markov kernel. Incompatibility is proved rather than assumed.

A direct Research root import includes the Lean source in the pinned library build and global axiom audit. A separate real compiler test changes the true compatibility proposition to a false one, preserving both source syntax and proof body; parser/import/resource failures do not count as semantic rejection.

This implements only the B-01 concrete overlap fixture. It does not claim B-02, D-05/06/08/09, or empirical causal identification. Frozen sources, historical receipts and dependency pins remain unchanged.
