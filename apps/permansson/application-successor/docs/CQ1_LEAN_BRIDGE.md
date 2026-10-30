# CQ-1 finite constitutive certificate — source-bound Lean bridge candidate

**Development scope:** ANA-01 (CQ-1), `feature/application-successor-full`,
PR #115. `finite-cq1` computes region-wide killed survival, prefix-survival
effects on the comparison set and their minimum (see `NUMERIC_CQ1.md`);
`receipts.cq1` independently rechecks the receipt.

## Mathematical contract

`PermanssonResearch/ApplicationBridge/FiniteScoreReceipt.lean`:

- `spec R basin` — a `RegimeSpecification` on the realized model's joint
  states with region `R` and basin `basin ∩ R` (the checks require
  `basin ⊆ R`). Its descriptor, target law and convergence mode are not used
  by the finite certificate.
- `survival K B L x = 1 − rationalHittingValue K (exitTarget B) L x`;
  `survivalProbability_eq` identifies it with the core `survivalProbability`
  of `realizedModel K` (via `ExitReceipt.survival_actual`).
- `prefixScore Q L` — the indicator of staying in `Q` at times `0..L`, a
  bounded measurable `FinitePathProperty`; `baseline_value` and
  `intervened_value` identify its baseline and intervened property values
  with `survival K₀ Q L` and `survival K₁ Q L`, the intervention being
  Research's typed admissible strategic `rationalStrategicIntervention K₀ K₁`.
- `checkCQ1` / `checkCQ1_sound` — decidable: `B₁ ⊆ basin ⊆ R`, two distinct
  comparison states, `0 ≤ η ≤ 1`, `1 − η ≤ survival` at **every** state of
  `R`, `0 < κ`, `κ` below every comparison effect and attained by one.
- `checked_finite_constitutive_certificate` — there is a comparison set
  whose states are exactly `B₁` (path-law nontriviality from the two distinct
  starts, `pathLaw_ne`) with `FiniteConstitutiveCertificate (realizedModel K₀)
  (spec R basin) (researchActionFamily K₀) C (rationalStrategicIntervention K₀ K₁)
  L (prefixScore Q L) (ofReal η) κ`, and the original `constitutiveMargin`
  equals `κ`.

In the realized model every row change is an action-selection change, so the
typed intervention being strategic says nothing about P at the source; that P
and feasibility are unchanged is proved separately on the reflected inputs.
Not claimed: Exact GR/PR, QSD, error-budget transport, terminal scores.

## Source emission and replay

`proof.cq1_emit` runs the independent checker, emits only receipts reporting a
certificate, reflects the baseline and treated models, proves
`treated_held_fixed` (and `treated_update_held_fixed` or
`treated_alpha_held_fixed` for an α-only or U-only intervention), sets
`K₀`/`K₁` to their α/P/U-induced matrices and emits `receipt_checked`,
`finite_constitutive_certificate`, one `region_survival_<y>` per region state
and `baseline_property_<y>` / `intervened_property_<y>` per comparison state.
Scope: the shared literal reflection bound, horizon 0..6.

```bash
python3 -B -m permansson_app finite-cq1 request.json --output /tmp/cq1
python3 -B -m permansson_app.proof.cq1_emit request.json \
  /tmp/cq1/cq1_receipt.json --output /tmp/permansson-cq1-instance
python3 -B -m permansson_app.proof.control_source_check --family cq1 \
  request.json /tmp/cq1/cq1_receipt.json /tmp/permansson-cq1-instance
lake env lean /tmp/permansson-cq1-instance/ReifiedCQ1.lean
```

`verification/research/test_application_cq1_live_lean.py` compiles the
packaged request and its horizon-3 variant, audits axioms, and requires
single-line mutations to fail at the falsified obligation: an overstated
margin, a valid lower bound that no comparison state attains, a persistence
budget below the region minimum, a region-only state that leaks while the
comparison set is unchanged, a comparison set outside the basin (all at
`receipt_checked`) and a treated model whose world kernel P changes
(`treated_held_fixed`).

## Trust boundary

Emission and source rechecks report `lean_status: NOT_EXECUTED`. A compiler
pass is not an authenticated proof receipt, independent mathematical
certification, empirical identification or release approval.

Transport of a checked certificate to an approximate pair under exact row-TV
budgets is a separate bridge; see
[`CQ1_TRANSPORT_LEAN_BRIDGE.md`](CQ1_TRANSPORT_LEAN_BRIDGE.md).
