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
independent check. The numeric result and the scientific, release and
identification gates are separate fields. Each gate has an explicit state:

| Field | Value | Meaning |
| --- | --- | --- |
| `mathematical_implementation` | `NUMERIC_ONLY` | exact rational computation, no proof object |
| `numerical_verification` | the independent check's status | e.g. `PASS`, `OPTIMAL_VERIFIED`, `INFEASIBILITY_VERIFIED` |
| `kernel_checked_proof` | `NOT_EXECUTED` | the application never runs Lean |
| `independent_mathematical_certification` | `NOT_ASSESSED` | no independent reviewer has certified the mathematics |
| `application_release_acceptance` | `NOT_ASSESSED` | no release scope is accepted |
| `empirical_identification` | `NOT_IDENTIFIED` | declared models are not identified from data |
| `publication_approval` | `NOT_ASSESSED` | nothing is approved for publication |
| `scientific_claims_verified` | `false` | a numeric result certifies no scientific claim |

All nine scientific certificate dimensions (`validity`, `epistemic_mode`,
`selection_status`, `identification_status`, `statistical_status`,
`provenance_status`, `substantive_pr_status`, `direction_status`,
`uniform_gap_status`) are `null`, meaning not assessed. They are never
`VALID`, `PR` or `CERTIFIED`. These states change only with external,
independently reviewed evidence, never as a cleanup.
