# Finite CQ-1 constitutive certificate — numerical profile v1

**Source:** `PermanssonResearch/ConstitutiveQuasi/Certificate.lean`
(`FiniteConstitutiveCertificate`) and `docs/CQ1_FINITE_CONSTITUTIVE_CERTIFICATE.md`.
The numeric profile is a bounded exact-rational implementation; its Lean
correspondence for bounded reflected instances is described separately in
[`CQ1_LEAN_BRIDGE.md`](CQ1_LEAN_BRIDGE.md). The application output itself
reports `lean_status=NOT_EXECUTED`.

## Input and computed objects

Run `permansson-app finite-cq1 <input.json> --output <new-directory>`. The
input supplies a complete typed finite strategic-world `α/P/U` baseline, one
declared strategic intervention (`alpha`, `U` or `alpha+U`; feasibility and P
are checked to be unchanged), a region `B`, a basin `B₀ ⊆ B`, a comparison set
`B₁ ⊆ B₀` with at least two states, a property set `Q`, a horizon `L` (`0..16`)
and a persistence budget `η ∈ [0,1]`.

At horizon `L` the profile computes, exactly:

1. the killed survival in `B` (staying in `B` at observation times `0..L`)
   from **every** state of `B` — the region-wide `IsFinitePersistent` gate —
   and its minimum; the gate passes when `min_B survival ≥ 1 − η`;
2. for every comparison state, the property value "stay in `Q` at times
   `0..L`" under the baseline and under the intervention, and the effect
   `|baseline − intervened|`;
3. the uniform margin `κ = min_{B₁} effect` and the states attaining it.

`certificate_status` is `FINITE_CONSTITUTIVE_CERTIFICATE` only when the gate
passes and `κ > 0`; otherwise `NOT_CERTIFIED` with the failed conditions. At
`L = 0` every effect is zero, so no certificate is reported. A comparison set
needs two states because Research's comparison set requires two starts with
different path laws; two distinct starts differ at time 0.

## Independent check and limits

`receipts.cq1.check_cq1` does not import the producer: it expands every
one-step `α/P/U` event of both models, re-derives every survival and property
value, the margin, its attaining states and the status, and requires the
receipt to match exactly.

Not provided: terminal or monitor scores other than prefix survival, kernel or
output error budgets and their transport (`CertificateTransport`), Exact GR,
Exact PR, QSD, empirical identification, independent mathematical
certification or release acceptance. Scope: at most 12 joint states.

## Certificate transport under exact TV budgets (`finite-cq1-transport`)

```bash
permansson-app finite-cq1-transport request.json --output <new-directory>
```

The request wraps a CQ-1 request (the certified baseline and intervention)
and an `approximate` baseline and treated model. Both share the certified
baseline's states, feasible actions and P, and differ from each other only
in the declared target. The receipt embeds the CQ-1 receipt and reports four
groups of values:

- the exact row total variations (half L1) between the certified and
  approximate induced kernels, and their maxima `δ₀` (baselines) and `δJ`
  (treated models);
- the envelopes `e = 1 − (1 − δ)^L`;
- the transported persistence error `min(1, η + e₀)` and margin
  `κ − e₀ − eJ` (status `TRANSPORTED_FINITE_CONSTITUTIVE_CERTIFICATE` only
  when that margin is positive);
- as a consistency check, the approximate pair's own exact minimum region
  survival and margin, which must respect the transported bound.

Research's `transportFiniteConstitutiveCertificate` is the theorem behind
this; see [`CQ1_TRANSPORT_LEAN_BRIDGE.md`](CQ1_TRANSPORT_LEAN_BRIDGE.md). The
budgets are exact distances between declared models, not empirical error
estimates.

`receipts.cq1_transport` sends the embedded receipt through the independent
CQ-1 checker. It sums every induced kernel directly from α, P and U and
recomputes every value.

The packaged example perturbs one α row of each model by 1/20, giving
`δ₀ = δJ = 1/50`. The transported margin is 301/1250 against the original
8/25, while the approximate pair's own margin is 729/2500.
