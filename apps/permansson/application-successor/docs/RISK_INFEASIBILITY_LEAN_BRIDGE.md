# One-step risk-cap infeasibility — source-bound Lean bridge candidate

**Development scope:** OPT-05 (risk-constrained occupancy, Farkas route),
`feature/application-successor-full`, PR #115.
`one-step-risk-infeasibility` certifies that a one-step risk cap cannot be
met (see the infeasibility section of `NUMERIC_RISK_OCCUPANCY.md`), and
`receipts.risk_infeasibility` checks the certificate independently. The
optimum route and its bridge are in [`FLOW_LEAN_BRIDGE.md`](FLOW_LEAN_BRIDGE.md).

## Mathematical contract

`PermanssonResearch/ApplicationBridge/FlowInfeasibilityReceipt.lean` builds
on `FlowReceipt`'s one-step model: fixed-action rows, admitted actions,
initial law `μ`, risk set, and `riskMass` of a real randomized policy.

- `FloorChecks` / `checkRiskFloors` decide four conditions:
  - `μ ≥ 0`;
  - every admitted action at `y` has risk coefficient at least `v y`;
  - some admitted action attains `v y`;
  - `cap < Σ_y v y μ y`.

  The floors with risk-cap multiplier one form the normalized Farkas ray of
  the occupancy program.
- `floor_le_riskMass` and `checked_min_risk` — `Σ_y v y μ y` is the least
  risk mass of every admissible real randomized one-step policy, and a pure
  floor policy attains it.
- `checked_cap_infeasible` — every admissible real randomized policy exceeds
  the cap, so no admissible policy meets it.

One transition only. No multi-stage occupancy, private-information or robust
statement. The bounded LP generator of the optimum route is not involved.

## Source emission and replay

`proof.risk_infeasibility_emit` runs the independent checker and reflects the
model as a `FiniteWorldInput`. The rows are `controlledMatrix input a`, and
the admitted actions are exactly the feasible ones (`options_exact`). It
emits `μ`, the risk set, the cap and the floors `v` as literals, with
`receipt_checked` (`decide +kernel`), `min_risk` and `cap_infeasible`.

```bash
permansson-app one-step-risk-infeasibility request.json --output /tmp/ri
permansson-app lean-emit --family risk-infeasibility request.json \
  /tmp/ri/infeasibility_receipt.json --output /tmp/permansson-risk-infeasibility
permansson-app lean-recheck --family risk-infeasibility request.json \
  /tmp/ri/infeasibility_receipt.json --candidate /tmp/permansson-risk-infeasibility
lake env lean /tmp/permansson-risk-infeasibility/ReifiedRiskInfeasibility.lean
```

`verification/research/test_application_risk_infeasibility_live_lean.py`
compiles two instances and audits axioms: the packaged example (least risk
7/16 against a cap of 1/4) and one with a zero-mass state. It requires
single-line mutations to fail at `receipt_checked`:

- the cap raised to the floor total;
- a floor above an admitted action's risk;
- an unattained floor;
- a changed initial law;
- a changed risk set.

## Trust boundary

Emission and source rechecks report `lean_status: NOT_EXECUTED`. A compiler
pass is not an authenticated proof receipt, independent mathematical
certification, empirical identification or release approval.
