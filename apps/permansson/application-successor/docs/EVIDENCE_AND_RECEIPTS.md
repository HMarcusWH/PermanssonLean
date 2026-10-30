# Evidence and receipts

The application keeps distinct kinds of evidence distinct. No output merges
them into a single "certified" bit.

## Fields every receipt carries

| Field | Value in this application | Meaning |
| --- | --- | --- |
| `request_identity` | `{profile, sha256}` | semantic identity of the canonical request (typed rational JCS) |
| `lean_status` | `NOT_EXECUTED` | the application never runs Lean |
| `scientific_claims_verified` | `false` | no scientific claim is certified by a numeric result |
| `empirical_identification` | `NOT_IDENTIFIED` | declared models are not identified from data |

Receipts state their own scope too, for example `scope_status`, `timing`,
`policy_class`, `budget_semantics` and `exact_GR_or_PR_certified: false`.
The checker rejects a receipt that changes any of these.

## Levels of evidence

| Level | Produced by | What it supports |
| --- | --- | --- |
| Exact numeric result | engine | the reported rationals for the declared finite model |
| Independent check | `receipts/*` (status `PASS`, `INFEASIBILITY_VERIFIED`, …) | the same values recomputed without the producer; certificates checked directly (saddle sides, Farkas rays, dual feasibility) |
| Source binding | `lean-emit` + `lean-recheck` | the Lean file is exactly the one derived from these request and receipt bytes |
| Instance replay | `lake env lean` on the pinned toolchain, axiom audit, mutations | the instance theorems hold for the literal data |
| Exact-head CI | GitHub Research Lean / application workflows | the library and tests at that commit |
| Independent mathematical certification, release acceptance, empirical identification | outside this application | not produced or claimed here |

## Certificates instead of trust in solvers

Where an optimum or an impossibility is claimed, the receipt carries a
certificate that the checker (and the Lean bridge) verifies directly:

- **LP optimum**: primal and dual feasibility with equal objective values.
- **LP or risk-cap infeasibility**: a Farkas ray. For the one-step risk cap
  these are per-state risk floors whose initial-law total exceeds the cap.
- **Private-stage robust value**: a controller mixture that guarantees `v`
  against every parameter and a nature mixture that holds every control to
  `v`, so no minimax theorem is assumed.
- **Bellman and monitor tables**: every layer is the exact max over admitted
  controls of the previous layer, and attainment is part of the transferred
  theorem.
- **CQ-1 transport**: exact row-TV budgets and the remaining-margin
  condition.

A bounded search that fails to find a certificate is reported as a failure
(for example `RISK_NO_CERTIFICATE`). It is never reported as a proof of the
opposite.

## Reports

`scientific_report.json` binds the capability, request identity, receipt and
independent check. All nine scientific certificate dimensions are `null`,
and `kernel_checked_proof` is `NOT_EXECUTED`.
