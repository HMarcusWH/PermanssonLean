# Finite two-player protocols — numerical profile v1

**Source:** `PermanssonResearch/MultiAgent/FiniteProductProtocols.lean`
(`FiniteProduct.Generator`, `actual_atom`, closed- and open-loop protocols),
`FiniteProductTwo.lean` (binary reduction) and
`MeasurableProductTwoOriginalMarginClosure.lean`. The numeric profile is a
bounded exact-rational implementation; its Lean correspondence is described in
[`MULTIAGENT_LEAN_BRIDGE.md`](MULTIAGENT_LEAN_BRIDGE.md). Application output
reports `lean_status=NOT_EXECUTED`.

## Input

Run `permansson-app finite-multiagent <input.json> --output <new-directory>`.
Labels declare `k0` common states, `k` private states (shared by both players),
`nx` world states and `m` actions (shared by both players), each at most two.
Tables are given in canonical order: joint states lexicographically as
(common, private 0, private 1, world), joint actions as (a0, a1).

- `players[j].action[y]` — player `j`'s action row at joint state `y`;
- `players[j].update[y][a][x']` — player `j`'s private-update row;
- `common_update[y][a][x']` — the common-update row;
- `world[y][a]` — the physical row P over next world states;
- `treated_player`, `replacement` (a mechanism for the treated player) and
  `anchor` (a full two-player profile).

Every row must be stochastic.

## Computed objects

The joint kernel
`K(y, (c', p0', p1', x')) = Σ_a act0(y,a0) act1(y,a1) P(y,a)(x') common(y,a,x')(c') upd0(y,a,x')(p0') upd1(y,a,x')(p1')`
for the baseline, the closed-loop protocol (only the treated player's
mechanism replaced) and the open-loop protocol (the anchor profile installed,
then the same replacement), and the per-state total variation between the
closed- and open-loop rows. P is never changed by a protocol.
`receipts.multiagent` rebuilds all three kernels in the opposite loop order
without importing the producer and requires an exact match.

## Limits

No asymmetric player types, mediated or correlated actions, private clocks,
empirical game identification, independent certification or release
acceptance.
