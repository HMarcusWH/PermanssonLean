# Finite two-player protocols — source-bound Lean bridge candidate

**Development scope:** MA-01 (multi-agent protocols),
`feature/application-successor-full`, PR #115. `finite-multiagent` assembles a
finite two-player protocol from canonical tables and computes the baseline,
closed-loop and open-loop joint kernels (see `NUMERIC_MULTIAGENT.md`);
`receipts.multiagent` independently rebuilds them.

## Mathematical contract

`PermanssonResearch/ApplicationBridge/MultiAgentReceipt.lean`:

- `tableKernel` — a row-stochastic rational table as a Markov kernel with PMF
  rows; `mech` — a player's `FiniteProduct.Mechanism` from its action and
  private-update tables; `generator` — Research's `FiniteProduct.Generator`
  (joint action kernel = actual product of the players' action kernels,
  update = common update × product of private updates); `world` — physical P.
  Joint states and actions are encoded with `finProdFinEquiv`.
- `finite_protocol_induced_kernel` — the induced α/P/U kernel of the assembled
  model has exactly the rational joint rows `jointRow`, via Research's
  `Generator.actual_atom`.
- `closedLoop_component` / `openLoop_component` — Research's closed-loop
  protocol (player `i`'s mechanism replaced) and open-loop protocol (anchor
  profile installed, then the replacement) are the generators of the updated
  tables.
- `checkFiniteMultiAgentProtocol` — decidable: every table row stochastic and
  the declared baseline, closed-loop and open-loop matrices equal the joint
  rows. `checked_protocol_kernels` states all three kernel identities;
  `checked_marked_path_transport` gives Research's binary reduction
  (`FiniteProduct.Two.actual_pathLaw`) and the binary model's atoms;
  `checked_matched_original_margin` instantiates Research's matched closed- and
  open-loop margin closures for this protocol, for every specification,
  comparison set and binary whole-path property.

Physical P is not part of the generator, so no protocol changes it. Not
claimed: asymmetric player types, mediated or correlated actions, private
clocks, empirical game identification.

## Source emission and replay

`proof.multiagent_emit` runs the independent checker and emits the five player
tables (baseline players, replacement, anchor players), the shared tables, the
treated player and the three joint matrices as literal rationals, with
`receipt_checked`, the table-validity theorems, `protocol_kernels` and
`marked_path_transport`.

```bash
python3 -B -m permansson_app finite-multiagent request.json --output /tmp/ma
python3 -B -m permansson_app.proof.multiagent_emit request.json \
  /tmp/ma/multiagent_receipt.json --output /tmp/permansson-multiagent-instance
python3 -B -m permansson_app.proof.control_source_check --family multiagent \
  request.json /tmp/ma/multiagent_receipt.json /tmp/permansson-multiagent-instance
lake env lean /tmp/permansson-multiagent-instance/ReifiedMultiAgent.lean
```

`verification/research/test_application_multiagent_live_lean.py` compiles the
packaged protocol, audits axioms and requires single-line mutations to fail at
`receipt_checked`: a false baseline row entry, the open-loop value given as the
closed-loop one, a non-stochastic action row, a changed replacement mechanism,
a changed anchor profile, the wrong treated player and a changed world kernel.

## Trust boundary

Emission and source rechecks report `lean_status: NOT_EXECUTED`. A compiler
pass is not an authenticated proof receipt, independent mathematical
certification, empirical identification or release approval.
