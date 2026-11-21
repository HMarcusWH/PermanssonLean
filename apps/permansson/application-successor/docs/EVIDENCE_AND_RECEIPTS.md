# Evidence and receipts

The application keeps distinct kinds of evidence distinct. No output merges
them into a single "certified" bit.

## Raw receipts, checker results and reports

Raw receipts have profile-specific schemas. Their identity and status fields
are not interchangeable with the independent check or scientific report:

| Record | Identity and content | Evidence fields |
| --- | --- | --- |
| `finite-kernel`: `induced_kernel_receipt.json` | `model_semantic_identity`, ordered states and the induced kernel | `lean_status=NOT_EXECUTED`, `scientific_claims_verified=false`, `empirical_identification=NOT_IDENTIFIED` |
| `finite-private-stage`: `private_stage_receipt.json` | `request_identity`, exact value, controller/nature mixtures and both saddle bounds | The same three status fields, plus this profile's `timing` and `scope_status` |
| LP optimal certificate (`Permansson.App.LPOptimalReceipt.v1`) | Exactly `format`, `model_semantic_identity`, `primal`, `dual`, `objective_value` | No `request_identity`, `lean_status`, `scientific_claims_verified` or `empirical_identification` field in the raw certificate |
| Finite-kernel independent check | `receipt_sha256`, `checked_atoms`, `status=PASS` | `proof_status=NOT_EXECUTED`, `claim_status=NUMERIC_EQUALITY_ONLY` |
| LP independent check | `certificate_sha256`, `status=OPTIMAL_VERIFIED` or `INFEASIBILITY_VERIFIED`; the optimum check also records `original_objective` | `proof_status=NOT_EXECUTED` |

Other profiles bind their own model, request, comparison or objective
identity. Their declared scope fields can include `scope_status`, `timing`,
`policy_class`, `budget_semantics` and `exact_GR_or_PR_certified: false`;
the corresponding checker enforces that profile's contract. The
[capability table](CAPABILITY_SCOPES.md) routes each profile to its checker
and numerical guide.

Successful checked numeric-profile commands publish `independent_check.json`
and `scientific_report.json` alongside their profile-specific receipt.
`lp-propose` instead nests its certificate in `proposal.json`; only
`CHECKED_OPTIMAL_CANDIDATE` also produces the check and scientific report.
`NO_CERTIFICATE_FOUND` or `RESOURCE_LIMIT` produces only the proposal and is
inconclusive. `lp-check` consumes an existing optimal or Farkas certificate
and writes the check and scientific report, without copying a new raw
certificate into its output directory.

The native C10/C11 wrapper, `permansson-app run`, has a separate output:
`application_result.json`. It binds provider pins, model bytes, native input
identity and artifact hashes, with `numeric_status=EXACT_RATIONAL_VERIFIED`,
`lean_status=NOT_EXECUTED`, `scientific_claims_verified=false` and
`empirical_identification=NOT_IDENTIFIED`. Its
`independent_application_acceptance` and `release_acceptance` fields are
`NOT_ASSESSED`. Native receipts and logs accompany it; it does not write a
`scientific_report.json` or assess the nine scientific dimensions below.

## Levels of evidence

| Level | Produced by | What it supports |
| --- | --- | --- |
| Exact numeric result | engine | the reported rationals for the declared finite model |
| Independent check | `receipts/*` (status `PASS`, `INFEASIBILITY_VERIFIED`, …) | the same values recomputed without the producer; certificates checked directly (saddle sides, Farkas rays, dual feasibility) |
| Source binding | `lean-emit` + `lean-recheck` | the Lean file is exactly the one derived from these request and receipt bytes |
| Instance replay | `lake env lean` on the pinned toolchain, axiom audit, mutations | the instance theorems hold for the literal data |
| Exact-head CI | GitHub Research Lean / application workflows | the library and tests at that commit |
| Independent mathematical certification, release acceptance, empirical identification | outside this application | not produced or claimed here |

## Manuscript publication and report evidence

The reviewed v2.0.1 paper provides an exposition and source concordance for these
routes; [`PAPER2_MAPPING.md`](PAPER2_MAPPING.md) links the exact edition and review
record. Its availability is a publication event for that manuscript, not a
runtime action by this application. The report's `publication_approval` therefore
remains `NOT_ASSESSED`, alongside its other literal gate values below.

When reviewing a paper claim, keep its hypotheses, numeric receipt, source-bound
candidate, actual compiler receipt, independent research acceptance and empirical
identification as separate evidence. The paper's review does not fill the nine
scientific reporting coordinates or alter historical release/case decisions.

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

`scientific_report.json` uses `model_semantic_identity` for the identity
supplied by the selected profile, which may include separate model and
objective identities. It binds the capability and the canonical receipt and
independent-check hashes. The numeric result and the scientific, release and
identification gates are separate fields. Each gate has an explicit state:

| Field | Value | Meaning |
| --- | --- | --- |
| `mathematical_implementation` | `NUMERIC_ONLY` | exact rational computation, no proof object |
| `numerical_verification` | the independent check's status | e.g. `PASS`, `OPTIMAL_VERIFIED`, `INFEASIBILITY_VERIFIED` |
| `kernel_checked_proof` | `NOT_EXECUTED` | the application never runs Lean |
| `independent_mathematical_certification` | `NOT_ASSESSED` | this result does not assess independent mathematical certification |
| `application_release_acceptance` | `NOT_ASSESSED` | this result does not assess release acceptance |
| `empirical_identification` | `NOT_IDENTIFIED` | declared models are not identified from data |
| `publication_approval` | `NOT_ASSESSED` | this result does not assess publication approval |
| `scientific_claims_verified` | `false` | a numeric result certifies no scientific claim |

These are states of this result, not statements that no external release or
publication exists. The published Linux CPython 3.12/3.13 numeric release is
recorded in [release acceptance](RELEASE_ACCEPTANCE.md#released-versions),
and the manuscript publication is described above. Neither rewrites a
numeric report's fields or releases a later source commit.

All nine scientific certificate dimensions (`validity`, `epistemic_mode`,
`selection_status`, `identification_status`, `statistical_status`,
`provenance_status`, `substantive_pr_status`, `direction_status`,
`uniform_gap_status`) are `null`, meaning not assessed. They are never
`VALID`, `PR` or `CERTIFIED`. These states change only with external,
independently reviewed evidence, never as a cleanup.
