# One-step risk-constrained occupancy (flow) — source-bound Lean bridge candidate

**Development scope:** OPT-05 (risk flow), `feature/application-successor-full`,
PR #115. `one-step-risk` maximizes the expected terminal reward after one
transition from a declared initial law over fully observed randomized Markov
controls, subject to a cap on the next-step risk mass, via the exact LP over
occupancy `q(y, a) = μ(y) π(a | y)`; `receipts.risk_occupancy` independently
rechecks the LP certificate and the reconstructed policy.

## Mathematical contract

`PermanssonResearch/ApplicationBridge/FlowReceipt.lean`:

- `nextLaw`, `expectedReward`, `riskMass` — the one-step next-state law of a
  real randomized policy `π` from `μ` through the controlled rows (for the
  bridge: `controlledMatrix input a`, the fixed-action P·U rows), its
  expected terminal reward and its risk mass; `Admissible options π` —
  a probability over the admitted actions at every state.
- `checkFlowReceipt` / `checkFlowReceipt_sound` — decidable: primal flow
  feasibility (nonnegative, zero off the admitted actions, state masses equal
  `μ`, risk within the cap) and value `D`; dual certificate (`λ ≥ 0` for the
  cap, `w ≥ 0` for the bounds `q ≤ μ`, free `v` for the mass equalities) with
  dual feasibility on every admitted action and `D = Σ v μ + λ cap + Σ w μ`;
  and the reconstructed policy `πr` with `μ πr = q`.
- `checked_risk_optimum` — every admissible **real** randomized policy whose
  risk mass is within the cap has expected reward at most `D`; `πr` is
  admissible, attains `D` and is within the cap. Weak duality is proved
  directly over the reals; no equality to a solver's output is assumed.
- `realized_one_step_atom` — one-step atoms of a realized matrix are its
  entries (C11 typed transition bridge).

One transition only: no multi-stage occupancy, robust-nature or
private-information statement, and no Farkas infeasibility route (the
application reports no optimum without a certificate).

## Source emission and replay

`proof.flow_emit` runs the independent checker, reflects the model and its
admitted actions (`bound_system_lines`), maps the receipt's LP dual by row
label (`mass<y>:le/ge`, `risk_cap:le`, `bound:<flow>`), and emits
`receipt_checked` and `risk_optimum`. It also reflects the reconstructed
policy as its own α/P/U input `policyWorld` and proves `policy_held_fixed`
(feasibility and P), `policy_update_held_fixed`, `policy_rows` (its induced
rows are the policy mixture of the controlled rows), `next_state_law_actual`
(the next-state law equals the realized policy model's one-step atoms mixed by
`μ`) and one `next_state_mass_<z>` per state.

```bash
python3 -B -m permansson_app one-step-risk request.json --output /tmp/risk
python3 -B -m permansson_app.proof.flow_emit request.json \
  /tmp/risk/occupancy_receipt.json --output /tmp/permansson-flow-instance
python3 -B -m permansson_app.proof.control_source_check --family flow \
  request.json /tmp/risk/occupancy_receipt.json /tmp/permansson-flow-instance
lake env lean /tmp/permansson-flow-instance/ReifiedFlow.lean
```

`verification/research/test_application_flow_live_lean.py` compiles the
packaged request (binding cap) and its slack-cap variant (bound duals),
audits axioms, and requires single-line mutations to fail at the falsified
obligation: an understated optimum, a dropped risk multiplier, a flow over the
cap, a wrong reconstructed policy (all at `receipt_checked`) and a policy
world that is not the reconstructed policy (`policy_rows`).

## Trust boundary

Emission and source rechecks report `lean_status: NOT_EXECUTED`. A compiler
pass is not an authenticated proof receipt, independent mathematical
certification, empirical identification or release approval.

When the cap cannot be met, the separate infeasibility route proves it with
per-state risk floors; see
[`RISK_INFEASIBILITY_LEAN_BRIDGE.md`](RISK_INFEASIBILITY_LEAN_BRIDGE.md).
