# Historical documentation errata

[Current documentation](README.md) · [Compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md) · [Verification and reproduction](VERIFICATION.md)

**Recorded 21 November 2026**, against repository baseline
`09c4341c22dfb22c750bfb02d4eaa4486782b77d`. These current explanations correct
reading and reproduction guidance for preserved artifacts. They do not replace
the historical bytes, regenerate their hashes or change scientific acceptance.
The manuscript's separate 58-item revision register remains unchanged.

## Unresolved-identification fixture

Audit item **DOC-09** concerns the historical
[`unresolved_identification` example](../../application/examples/unresolved_identification/).
Its three records disagree about the declared model set and sampling:

| Record | Statement or binding |
| --- | --- |
| [Specification](../../application/examples/unresolved_identification/specification.md#model-set-and-inference-procedure) | The formal model set is the singleton model defined there, with no sampling uncertainty; comparison covers both declared initial states |
| [Argument](../../application/examples/unresolved_identification/argument.md) | The model-set rule retains all support/modularity-compatible completions, including zero effects; simultaneous statistical coverage remains unresolved |
| [Application JSON](../../application/examples/unresolved_identification/application.json) | `semantic_pipeline.bindings.model_set_rule` and `inference_procedure`, plus `identified_set.rule_ref` and `inference_procedure_ref`, all reference `spec`; the same record sets `sampling_applicable: true`, `quantification: "INCOMPLETE"`, `coverage: "UNRESOLVED"` and `zero_effect: "POSSIBLE"` |

The preserved identities are:

| Artifact | SHA-256 |
| --- | --- |
| `specification.md` | `55bc61bfff5ab419910ed8bc8b666f8dcca4dd84f4f9245eeabf78ca05e94f20` |
| `argument.md` | `66e359aa98a5764051cda527525cc6b0ae6a111fe1a5881cb4927996cbe826ee` |
| `application.json` | `7b3ee590d38674d1049981654a2dbe5f8cc61c30344bd4c2a5d58d14b38cab03` |

The [structural validator](../../application/validator/validate_application.py)
returns `contract_valid: true` and `scientific_claims_verified: false` for this
packet. Those outcomes are consistent with its contract: it checks serialization,
artifact bindings and declared reporting consistency, not the semantic agreement
of opaque scientific prose. This erratum identifies an illustrative narrative
inconsistency; it does not invalidate the structural PASS or establish empirical
identification, occupation convergence or a robust PR claim.

The fixture and the original [application boundary](../APPLICATION_BOUNDARY.md)
remain unchanged. A corrected illustrative specimen would need a distinct
version, coherent model-set/sampling declarations and regenerated artifact and
pipeline identities. See [application compatibility](APPLICATION_COMPATIBILITY.md#historical-fixture-caveat)
for the current reading route.

## Original closure-draft formatting and abstract

Audit item **DOC-15** concerns the original
[closure-draft README](../../research_papers/mathematical_closure/README.md)
and [manuscript abstract](../../research_papers/mathematical_closure/main.tex).
The README escapes its starting-commit code span and shell-code fences, so they
render as literal punctuation. The [current detached-build instructions](VERIFICATION.md#detached-original-closure-draft-build)
provide the same starting commit and two commands with ordinary Markdown
delimiters.

The abstract's opening sentence combines the noun phrase “programme connecting”
with the bare verbs “recover” and “formalize”. A grammatical wording for a
separately identified successor draft is:

> This working draft presents an explicitly scoped research and proof-integration
> programme that connects canonical strategic–world path laws to original
> constitutive margins, recovers arbitrary-measurable conditional-product
> two-player models, and formalizes a finite nonlinear occupation counterexample.

This proposed copyedit is recorded here without altering the original abstract.
Both files are among the [builder's thirteen canonical source members](../../release/mathematical-closure-1/build.py),
which the [draft rehearsal](../../verification/research/pr113_draft_rehearsal_auth.py)
and [archive integrity checker](../../release/mathematical-closure-1/archive_integrity.py)
bind to exact archived bytes. The original source members, archives and build
receipts retain those identities. Any successor draft requires its own source
and build identities. **DRAFT / NOT ACCEPTED / NOT PUBLISHED** remains the
original draft's status; neither this copyedit nor a successful byte check
supplies independent acceptance or publication authority.

## Q05 baseline and intervention sentence

Audit item **DOC-16** concerns the unmatched inline-code delimiter and stray
parenthesis in the [Q-05 source-scope note](../../research/paper_closures/post_merge_112/Q05_NONIDENTITY_SOURCE_SCOPE.md#typed-fixture-frozen-numerical-target).
Read the affected sentence as:

Baseline fine strategic update writes `s_next=false`; intervention writes
`s_next=true`; coarse update remains `()`.

The three assignments are unchanged. This is an editorial correction, with no
change to the numerical target, theorem/receipt identities or the note's
`EXACT_RATIONAL_CANDIDATE_NOT_LEAN_CERTIFIED` status. The dated note and its
immutable source entry in the [v1.1.1 module manifest](../reference/MODULE_MANIFEST_v1.1.1.json)
at `c5a36cd6189e2a249d5f4bc11f31698917dc8b10` remain unchanged.
