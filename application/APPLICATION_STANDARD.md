# Permansson Application Standard 0.1.0

Status: **DRAFT**. Compatible theory: **v0.1.8**.
Scope: **APPLICATION_CONTRACT_NOT_THEOREM_EXTENSION**.

## 1. Authority and source crosswalk

The authority for GR/PR terminology is [the v0.1.8 paper](../paper/README.md), not
this JSON format. The frozen paper and its Lean coverage are not modified.

| Paper location | Source-derived requirement | Contract representation |
|---|---|---|
| Sections 3, 4.1-4.3 | Typed alpha/P/U process; frozen B, B0, h, nu, convergence; Exact GR distinct from finite persistence | Semantic bindings, explicit primitive inventory and regime assertions |
| Sections 4.4, 15.11 | QSD equation does not replace the uniform finite-persistence gate | Separate finite-persistence and QSD claim references |
| Sections 5.2-5.3 | Relevance g, property psi, comparison B1, component grammar, typed J, held-fixed primitives and hard target closure | Frozen bindings and intervention protocols |
| Section 5.4, Definition 5.1 | Exact GR plus strategic constitution; grounded confirmatory subclass | Regime assertions and protocol-scoped PR reporting |
| Section 5.5 | A null result for one protocol is not global absence of PR | `FROZEN_PROTOCOL` scope only |
| Section 10.5, Table 4 | Mathematical core / semantic pipeline / empirical certificate; one joint pipeline identifier; rooted provenance | Digest, artifact references and provenance DAG |
| Section 10.6 | Quantify over the entire model/state set; one outer structural/statistical uncertainty set; distinguish nonzero effect, direction and uniform gap | Identified-set declarations and independent certificate dimensions |
| Section 10.7, Table 5 | Orthogonal certificate tuple | Exact nine-dimension vocabulary below |
| Sections 12, Appendix C | Fail closed on unsupported exactness, provenance, support, selection or coverage | Necessary consistency checks, never automatic scientific verification |

**Implementation conventions, not new paper theorems:** the JSON envelope, field
names, SHA-256 serialization profile, restricted timestamp/path profiles, file-size
limits, offline registry, individual error codes and example/test organization.
Table 5 gives illustrative values; this draft freezes those values as its wire
vocabulary. Extending that vocabulary requires a new application-standard version,
not a retroactive reinterpretation of the paper.

## 2. Bundle and schemas

One self-contained bundle contains `application.json` and its referenced artifacts.
The envelope has a standard version, compatible theory version, application ID,
artifact registry, regime assertions, semantic pipeline, intervention list,
provenance graph, identified-set report and application certificate.

Every object rejects unknown fields. All field presence is explicit: nullable
bindings mean *not declared/applicable*, not zero, false or success. Exact GR must
have occupation-law and convergence bindings. A quasi-regime may leave them null.
The schemas check shape; the validator additionally checks cross-object constraints.

The five domain schemas are `application_certificate`, `semantic_pipeline`,
`intervention_protocol`, `provenance_graph` and `identified_set`. The common and
bundle schemas compose them using JSON Schema 2020-12. Their `$id` URIs are local
registry identifiers, not a promise that schemas are hosted at those addresses.

The default implementation supports one certificate per frozen protocol. A family
may be registered in `interventions`, and the entire family's semantics is hashed,
but no global `NO_PR` verdict or family-exhaustion certificate is emitted. Separate
protocol-scoped bundles/certificates are required for additional reported protocols.

## 3. Orthogonal certificate vocabulary

These values are transcribed from Section 10.7 / Table 5:

| Field | Values |
|---|---|
| validity | VALID; INVALID |
| epistemic_mode | FORMAL_THEORETICAL; EMPIRICAL_CONFIRMATORY; EMPIRICAL_EXPLORATORY; ASSUMPTION_CONDITIONAL |
| selection_status | FROZEN_REGISTERED; HELD_OUT_OR_SELECTION_ADJUSTED; POST_HOC_EXPLORATORY |
| identification_status | POINT_IDENTIFIED; SET_IDENTIFIED; STRUCTURALLY_UNRESOLVED |
| statistical_status | NOT_APPLICABLE; RESOLVED_AT_DECLARED_COVERAGE; STATISTICALLY_UNRESOLVED |
| provenance_status | SUPPORTED; INSUFFICIENT; NOT_APPLICABLE |
| substantive_pr_status | ROBUST_PR; ROBUST_NONCONSTITUTIVE_UNDER_FROZEN_PROTOCOL; PR_STATUS_AMBIGUOUS; NOT_EVALUATED |
| direction_status | POSITIVE; NEGATIVE; DIRECTION_AMBIGUOUS; NOT_APPLICABLE |
| uniform_gap_status | ESTABLISHED; UNRESOLVED; NOT_APPLICABLE |

A contract-valid record can report `validity=INVALID`. Unresolved identification is
also a valid reported outcome. The validator never rewrites these fields or turns
its own success into `validity=VALID`.

Robust pointwise PR does not require a common direction or a common positive
uniform gap. A metric-valued property need not have a signed direction at all.
Basin-only descriptor nondegeneracy is allowed; forward-active richness is not a
universal gate. Broad formal GR/PR records do not acquire a universal grounding
requirement; valid empirical-confirmatory PR records do require grounding and
confirmatory descriptor nondegeneracy.

## 4. Frozen semantic pipeline

Bindings name content-addressed artifacts defining S x X and state sufficiency;
alpha, P, U and feasibility; B, B0, h, nu and convergence; g, psi and B1;
component grammar; hard structural relations and transport; model-set construction;
and the inferential procedure. A clock binding is required for a date-indexed
intervention represented in the stationary core.

Primitive inventory must include action selection, strategic update, world
transition and feasibility. Additional institutional/information primitives may be
included. Each protocol partitions the inventory into its effective target and
held-fixed components. The nominal target must be contained in the effective target.
The validator checks this declaration; the scientist must establish actual hard
structural closure. Strategic interventions may change alpha and/or U, never P or
feasibility under the same strategic type. Retype a broader structural intervention.

### PERMANSSON_PIPELINE_V1 digest

`pipeline_id` is `sha256:` followed by 64 lowercase hex digits. The certificate must
refer to the same ID. The digest payload is exactly:

1. Domain string `PERMANSSON_PIPELINE_V1`, standard version and compatible theory.
2. `semantic_pipeline` minus `pipeline_id` and `registration_ref`.
3. The complete ordered intervention list, minus the assessment annotations
   `formal_admissibility`, `reachable_support`, and `causal_modularity`.
4. A sorted ID-to-SHA-256 map for every artifact referenced by items 2 and 3.

Serialize with Python `json.dumps(sort_keys=True, ensure_ascii=True,
separators=(",", ":"), allow_nan=False)`, UTF-8 encode, then hash. This is an explicit
versioned serialization convention, **not RFC 8785/JCS**. Object-key order does not
matter; array order does. Artifact locations can change without changing semantics
provided IDs and byte hashes are preserved. Artifact hashes are checked separately.

Registration receipts and evaluation assessments are excluded to avoid a circular
hash of a receipt that itself names the pipeline. Results and provenance can be
appended without rewriting frozen choices; model-set and inference *rules* remain
bound through semantic artifacts. Changed model rules or intervention semantics
require a new pipeline ID and a new freeze/selection account.

`--digest` prints a proposed ID when validation has no errors other than
`PIPELINE_DIGEST`. This permits matching placeholder or stale IDs; a certificate
whose ID differs from the pipeline's declared ID still fails. The command does
not rewrite files, forgive changed artifact bytes, or constitute registration.
Digest-generation success is not input-contract validity; see Section 7 for
mode-specific exits and JSON output. Validation never repairs stale hashes automatically.

**A hash is not an authentic timestamp.** Rehashing edited input with a backdated
self-declared timestamp can fool a consistency checker. Supply an independently
inspectable registration/commit/archive record and have a reviewer verify it.
The CLI checks only the declared chronology and existence/hash of its artifact.

Timestamps use an RFC3339 subset with explicit seconds and `Z` or a known numeric
offset; timezone-naive dates, leap seconds and unknown `-00:00` offsets are rejected.
Chronology compares instants, not text. A held-out/selection-adjusted record requires
its procedure artifact; it is not rejected merely for having a later freeze, since
the validity of selection adjustment is a separate scientific question.

## 5. Rooted provenance

Edges are `node -> depends_on`, from supported claim to its dependencies.
Allowed terminal roots are `EXTERNAL_EVIDENCE`, `DECLARED_IDENTITY_OR_AXIOM` and
`INDEPENDENT_UPSTREAM_RESULT`. Roots cannot depend on other graph nodes; non-roots
(`DERIVATION`, `CLAIM`) must have dependencies. Every node references an existing
hashed artifact. Claim references must resolve to actual `CLAIM` nodes.

The entire graph is checked for duplicate IDs, dangling dependencies, orphaned
non-roots and cycles, including disconnected cycles. Multiple legitimate evidence
roots are allowed. By finite acyclicity plus non-root dependency requirements,
every declared derivation reaches a declared root.

This checks **declared graph structure**, not evidentiary truth or completeness.
A cited assumption does not thereby become established, and a root labelled
external is not automatically authentic or admissible. Undeclared assumptions in
opaque prose cannot be detected by the validator. Report insufficient provenance
or unresolved identification rather than disguising a model assumption as evidence.

## 6. Regime and uncertainty checks

`EXACT_GR` requires an exactness basis, claim reference and occupation semantics.
The validator does not check the argument, Lean proof, interval arithmetic or the
all-initial-law quantifier. `QUASI_REGIME` requires L, eta and a finite-persistence
claim. `QSD_CERTIFIED_QUASI_REGIME` additionally requires a separately named QSD
claim. Both claim IDs may point into one proof artifact, but neither gate silently
substitutes for the other. Quasi-regimes/candidates cannot carry `ROBUST_PR`.

The identified-set report binds to the frozen model-set rule, B1 and inference
procedure. For a robust status it must declare a nonempty full model/state set and
supporting claims. It cannot use a representative/majority model or incomplete
quantification. `EXCLUDED` means zero is excluded throughout that declared set;
`ALL_ZERO` means every admitted effect is zero, not failure to reject a null.
`POSSIBLE` and `NOT_ASSESSED` must not be promoted into either robust conclusion.

An established uniform gap requires a common strictly positive rational lower
bound and its own claim reference. Gap establishment is independent of a common
sign. Statistical resolution requires declared justified coverage of the joint
outer set; zero-containing or unresolved-covered sets remain statistically
unresolved. The validator checks consistency of these declarations, **not coverage
or exhaustion of an infinite model/state set**.

Valid empirical-confirmatory records cannot describe post-hoc exploration as
confirmation. Unsupported intervention-reachable rows or unresolved modularity
must remain structurally unresolved in empirical records. Formal counterfactuals
remain meaningful without that empirical upgrade.

## 7. Input safety and outputs

JSON input is capped at 2 MiB. Duplicate keys, NaN, Infinity and float overflow are
rejected. Artifacts are capped at 8 MiB each and 128 entries per bundle; large
external sources should be represented by bounded, inspectable evidence snapshots.
Paths must be relative POSIX paths without traversal, symlinks, non-regular files,
Windows reserved names or case collisions. The CLI does not execute or fetch input.

### Mode-specific exit codes

| Operation | Exit 0 | Exit 1 | Exit 2 |
|---|---|---|---|
| Validation (without `--digest`) | The input contract conforms. | Schema/consistency violations. | Argument-parsing, input or configuration error. |
| Digest proposal (`--digest`, with or without `--json`) | A proposal was generated; the input need not conform yet. | A violation other than `PIPELINE_DIGEST` prevents a proposal. | Argument-parsing, input or configuration error; no proposal. |

Matching placeholder/stale IDs can produce a digest with exit 0 while retaining
`contract_valid=false` and the `PIPELINE_DIGEST` error. Never use digest-mode exit 0
as a contract-validation gate. After deliberately updating both IDs, rerun
validation without `--digest`; inspect `contract_valid` in machine-readable results.
A raw schema check is not a substitute for cross-file validation.

### Machine-readable results and argument errors

For validation and digest operations, `--json` emits one JSON object on stdout and
includes `contract_valid`, `errors`, `notice` and `scientific_claims_verified=false`.
With `--digest`, it additionally includes `digest_generated` and
`proposed_pipeline_id`; these describe the operation, not scientific validity.
On a successful proposal they are `true` and the proposed ID, without removing
any input-validation errors. On failure they are `false` and `null`.

This JSON contract includes argument-parsing errors such as a missing bundle,
unknown option or an attached value on a boolean flag. They return exit 2 with
`INPUT_OR_CONFIGURATION`, `contract_valid=false`, and no proposal; usage text is
not mixed into JSON stdout or emitted on stderr. Without a JSON request, parser
errors retain the conventional usage/error text on stderr and exit 2.

Output flags must occur before the end-of-options marker `--`; tokens after it
are positional arguments, even when named `--json` or `--digest`. Existing
unambiguous option abbreviations remain accepted, though full names are preferred.
An explicit `--help` or `-h` request retains human-readable help and exit 0. Help
is not a validation/digest result and performs neither operation, even with `--json`.

## 8. Review and versioning

Before accepting an empirical certificate, an independent reviewer still needs to
inspect model sufficiency, exactness, relevance, component grammar, counterfactual
feasibility, modularity, support, source authenticity, model-set construction,
coverage, multiplicity, optional stopping and selection adjustment. This package
supplies an auditable container for that review; it does not perform it.

All examples are synthetic. No historical Hormuz, Russia-Ukraine, MIDR, fraud or
other application is reclassified by this PR. Existing release provenance and
formal theorem coverage remain unchanged. Future changes to these wire rules
must version the application standard independently of the theory.

Implementation references: JSON Schema Draft 2020-12 at
<https://json-schema.org/draft/2020-12/> and jsonschema's offline registry API at
<https://python-jsonschema.readthedocs.io/en/stable/referencing/>. These govern
serialization/validation mechanics, not GR/PR mathematics.
