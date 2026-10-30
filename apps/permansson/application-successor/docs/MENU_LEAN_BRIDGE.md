# Frozen intervention menus — source-bound Lean bridge candidate

**Development scope:** OPT-01 (D0 frozen-menu optimization),
`feature/application-successor-full`, PR #115.
The `frozen-menu` profile evaluates every *declared* α/U intervention of a
baseline α/P/U model by the exact finite-horizon survival (or exit) value of a
region from a start state, and reports the optimum and the complete tie set;
`receipts.menu` independently rechecks it. This increment binds a checked
receipt to the Research D0 correspondence theorems.

## Mathematical contract

`PermanssonResearch/ApplicationBridge/MenuReceipt.lean`:

- `exitTarget region` — leaving the region is hitting its complement, with
  nothing forbidden. `menuObjective` is `rationalHittingValue` of that target
  (exit-by-horizon) or one minus it (survival).
- `MenuChecks` / `checkMenuReceipt` — decidable: every reported member value
  is exact, and `tied` is nonempty and is exactly the set of members at least
  as good as every listed member in the declared direction.
- `checked_value_canonical` — via `rationalHittingValue_eq_canonical_all_horizons`,
  each checked value is the hitting probability (or its complement) in the
  canonical finite-prefix Markov law of that member's matrix.
- `checked_tied_exactly_listed_optima` — the tie set is exactly the listed
  optima. **Optimality is over the declared menu only.**
- `HeldFixed base w` — the member keeps the baseline's feasible-action
  relation and world kernel P.

## Source emission and replay

`proof.menu_emit` runs the independent menu checker, then reflects the
baseline and each member as separate `FiniteWorldInput`s (`base`,
`member_<i>`; `finite_emit.input_definition` now takes a definition name, with
unchanged default output), defines each member as `inducedMatrix member_<i>`,
and emits: `member_<i>_held_fixed`, the undeclared generator held equal
(`member_<i>_update_held_fixed` for α interventions,
`member_<i>_alpha_held_fixed` for U interventions), `receipt_checked`,
`tied_exactly_listed_optima`, `baseline_survival` and one `member_value_<i>`
per member as an actual canonical path-law probability. Scope: shared literal
reflection bound, ≤4 members, 1..6 transitions.

```bash
python3 -B -m permansson_app.proof.menu_emit request.json receipt.json \
  --output /tmp/permansson-menu-instance
python3 -B -m permansson_app.proof.control_source_check --family menu \
  request.json receipt.json /tmp/permansson-menu-instance
lake env lean /tmp/permansson-menu-instance/ReifiedMenu.lean
```

`verification/research/test_application_menu_live_lean.py` compiles the
packaged menu (survival, minimize) and its exit/maximize variant, audits
axioms, and requires single-line mutations to fail at the falsified
obligation: a false member value, an over-claimed tie set, a non-optimal
member as the optimum, a reversed direction, and a member whose undeclared U
row differs from the baseline (`member_1_update_held_fixed`).

## Trust boundary

Emission and source rechecks report `lean_status: NOT_EXECUTED`. A compiler
pass is not an authenticated proof receipt, independent mathematical
certification, a claim about undeclared interventions, empirical
identification or release approval.
