# CQ-1 certificate transport — source-bound Lean bridge candidate

**Development scope:** ANA-01 (CQ-1, error-budget transport),
`feature/application-successor-full`, PR #115. `finite-cq1-transport`
transports a checked CQ-1 certificate to a declared approximate pair under
exact row-TV budgets (see the transport section of `NUMERIC_CQ1.md`).
`receipts.cq1_transport` checks it independently. The certified bridge itself
is in [`CQ1_LEAN_BRIDGE.md`](CQ1_LEAN_BRIDGE.md).

## Mathematical contract

`PermanssonResearch/ApplicationBridge/CQ1TransportReceipt.lean`:

- `approxPair` — Research's `StrategicApproximationPair` for the realized
  certified model. It consists of the approximate realized baseline, its
  action family, and the typed strategic intervention to the approximate
  treated matrix; the realized world kernel is shared (`rfl`).
- `env δ L = 1 − (1 − δ)^L` — the rational form of `geometricTVEnvelope`
  (`geometricTVEnvelope_cast`).
- `TransportChecks` / `checkTransport` — decidable:
  - `rowTV K₀ A₀ y ≤ δ₀` and `rowTV K₁ A₁ y ≤ δJ` for every row;
  - both budgets lie in `[0, 1]`;
  - `env δ₀ L + env δJ L < κ`.
- `checked_transported_certificate` combines
  `checked_finite_constitutive_certificate`, `realized_uniformTV` for both
  pairs and Research's `transportFiniteConstitutiveCertificate`. The
  approximate realized model gets a genuine `FiniteConstitutiveCertificate`
  for the same specification:
  - the transported comparison set, whose states are exactly `B₁`;
  - persistence error `clampedPersistenceError η (env δ₀ L)`, that is
    `min 1 (η + env δ₀ L)`;
  - margin `κ − env δ₀ L − env δJ L`.

The budgets are exact distances between declared models, not empirical error
estimates. Exact GR/PR and QSD are not claimed.

## Source emission and replay

`proof.cq1_transport_emit` binds only receipts with status
`TRANSPORTED_FINITE_CONSTITUTIVE_CERTIFICATE`. It reflects the certified
baseline and treated model and the approximate pair as `FiniteWorldInput`s.
Each non-baseline model gets a theorem `*_held_fixed` (the certified
baseline's feasible actions and P are kept). It emits the matrices, the
CQ-1 data and the budgets, with `receipt_checked`, `transport_checked` and
`transported_certificate` (literal error and margin).

```bash
permansson-app finite-cq1-transport request.json --output /tmp/tr
permansson-app lean-emit --family cq1-transport request.json /tmp/tr/cq1_transport_receipt.json \
  --output /tmp/permansson-cq1-transport
permansson-app lean-recheck --family cq1-transport request.json /tmp/tr/cq1_transport_receipt.json \
  --candidate /tmp/permansson-cq1-transport
lake env lean /tmp/permansson-cq1-transport/ReifiedCQ1Transport.lean
```

`verification/research/test_application_cq1_transport_live_lean.py` compiles
the packaged example (budgets 1/50, transported margin 301/1250) and a
zero-budget pair, and audits axioms. Single-line mutations must fail:

- at `transport_checked`: an understated budget, a budget whose envelope
  exceeds the margin, and the wrong approximate baseline;
- at `receipt_checked`: an overstated certified margin and an understated
  persistence error.

## Trust boundary

Emission and source rechecks report `lean_status: NOT_EXECUTED`. A compiler
pass is not an authenticated proof receipt, independent mathematical
certification, empirical identification or release approval.
