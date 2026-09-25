# Offline application validator

From the repository root, install `application/requirements.txt`, then run:

```bash
python application/validator/validate_application.py path/to/application.json --json
```

Python interface:

```python
from pathlib import Path
from application.validator.validate_application import load_json, validate_document
path = Path("path/to/application.json")
result = validate_document(load_json(path), path.parent)
assert result["scientific_claims_verified"] is False
```

The JSON Schema registry is bundled, versioned and closed to network retrieval.
Only bundle-local files are read. Validation does not write files or execute proof,
data-transformation or other application code. Use `--digest` to print a proposed
semantic-pipeline identifier; review and record it explicitly in the manifest and
certificate before external registration. It is not an auto-repair switch.

Exit codes and the digest algorithm are specified in
[APPLICATION_STANDARD.md](../APPLICATION_STANDARD.md). Input/configuration errors
exit 2; contract violations exit 1; a conforming record exits 0. `validity=INVALID`
is a possible value *inside* a conforming record and is not the CLI exit status.

## Digest proposals and certificate links

`--digest` tolerates only `PIPELINE_DIGEST`, so matching placeholder or stale IDs
can be replaced deliberately. The certificate's `pipeline_id` must still match
the pipeline's declared ID. A mismatch remains `CERTIFICATE_PIPELINE` and exits 1,
even when the pipeline already has its correct digest. Artifact/hash, chronology,
schema and all other errors remain failures; no input is rewritten.

## Machine-readable digest proposals

Combine the options in either order:

```bash
python application/validator/validate_application.py path/to/application.json --digest --json
```

The command emits one JSON object, never a bare hash or mixed JSON/text. It retains
`contract_valid`, `errors`, `notice`, and `scientific_claims_verified=false`, and
adds these command-result fields on both success and failure:

| Field | Meaning |
|---|---|
| `digest_generated` | Whether the digest operation produced a proposal. |
| `proposed_pipeline_id` | The proposed `sha256:...` identifier, or `null` on failure. |

Exit 0 in digest mode means a proposal was generated; it does **not** necessarily
mean the input bundle already conforms. Matching placeholder/stale IDs produce a
proposal while retaining `contract_valid=false` and the `PIPELINE_DIGEST` error.
After deliberate updates to both IDs, rerun validation without `--digest`.

Certificate mismatches and other contract violations exit 1 with no proposal.
Input/configuration errors exit 2 with no proposal. Both failure paths retain the
same JSON field set. These are CLI-result fields, not new application-certificate
or semantic-pipeline fields. No input, artifact, or scientific status is changed.
Plain `--digest` still prints only the proposed identifier on success; ordinary
`--json` validation without `--digest` retains its existing result shape.

## Timestamp precision

Freeze/evaluation comparisons retain every accepted fractional-second digit. The
parser compares a timezone-aware whole second and an exact decimal fraction; it
never rounds or truncates the fraction to microseconds or the Decimal context.
Equivalent instants with different offsets or trailing fractional zeros compare
equally. The existing restrictions on naive dates, leap seconds and unknown
`-00:00` offsets are unchanged.

## Raw evidence in Git

`.gitattributes` defaults `application/**` to `-text`. Only explicitly scoped,
authored source/configuration files are normalized to LF. Keep evidence in a
bundle directory such as `application/bundles/<id>/` (or a nested example): its
payloads retain their exact bytes even when named `.md`, `.json`, `.py` or `.txt`.
Do not add blanket text rules over evidence paths or recompute hashes to conceal
line-ending changes. Regression tests exercise real Git index/checkouts with
`core.autocrlf=true`, `false` and `input`, including binary and mixed-ending data.
