# Admitted patch grammars — source-bound Lean bridge candidate

**Development scope:** GRAM-01 (finite α/U patch grammar),
`feature/application-successor-full`, PR #115.
`finite-grammar` applies explicitly admitted blocks of declared α/U patches
(no downward closure; overlapping patches must agree on the complete
stochastic row) to a baseline α/P/U model, evaluates each block's exact
finite-horizon survival (or exit) values on comparison states, its effects
against the baseline, the inclusion-minimal blocks whose effect is positive on
the whole comparison set, and four-corner interactions; `receipts.grammar`
independently rechecks it.

## Mathematical contract

`PermanssonResearch/ApplicationBridge/GrammarReceipt.lean`:

- `GrammarChecks` / `checkAdmittedBlocks` / `checkAdmittedBlocks_sound` —
  decidable: baseline and block values against `menuObjective` of each
  block's matrix; the minimal set is exactly the blocks with positive effect
  on every comparison state and no strictly smaller (by component set)
  positive admitted block; every corner's four blocks are `∅`, `{a}`, `{u}`,
  `{a, u}` and its interaction is `v(a ∪ u) - v(a) - v(u) + v(∅)`.
- `actualObjective` — survival (or exit) probability of a realized chain on
  the actual path law; `checked_base_value_actual`,
  `checked_block_value_actual`, `positive_iff_actual`.
- `checked_minimal_positive_blocks` — the minimal set characterized by actual
  probabilities; `checked_four_corner_effects` — every interaction is the
  actual interaction of path-law probabilities.

Which model a block denotes is proved per instance (below). A positive finite
effect is not a constitutive or PR certificate; lower-set transport from the
planned spec is not implemented.

## Source emission and replay

`proof.grammar_emit` runs the independent checker, reflects the baseline
(`base`) and every admitted block's treated model (`block_<i>`), and proves
for each block `block_<i>_held_fixed` (feasibility and P),
`block_<i>_alpha_rows` and `block_<i>_update_rows` (the block's α and U are
the baseline's with exactly its declared patch rows overridden). It then
emits `receipt_checked`, `minimal_positive_blocks`, one `block_value_<i>_<x>`
per block and comparison state and one `four_corner_<r>_<x>` per corner,
each with its exact rational value. Scope: the shared literal reflection
bound, ≤8 blocks, horizon 0..6.

```bash
python3 -B -m permansson_app finite-grammar request.json --output /tmp/g
python3 -B -m permansson_app.proof.grammar_emit request.json \
  /tmp/g/grammar_receipt.json --output /tmp/permansson-grammar-instance
python3 -B -m permansson_app.proof.control_source_check --family grammar \
  request.json /tmp/g/grammar_receipt.json /tmp/permansson-grammar-instance
lake env lean /tmp/permansson-grammar-instance/ReifiedGrammar.lean
```

`verification/research/test_application_grammar_live_lean.py` compiles the
packaged exit grammar and its survival variant, audits axioms, and requires
single-line mutations to fail at the falsified obligation: an over-claimed
minimal set, a false block value, a false interaction, misreported block
components (all at `receipt_checked`), a block without its patch row
(`block_1_alpha_rows`) and a block that changes the world kernel
(`block_1_held_fixed`).

## Trust boundary

Emission and source rechecks report `lean_status: NOT_EXECUTED`. A compiler
pass is not an authenticated proof receipt, independent mathematical
certification, a constitutive certificate, empirical identification or
release approval.
