# Permansson research companion v0.2.0

This kit produces a separately versioned research companion. Its claims have
their own assumptions and open boundaries; it does not certify completion of
every item in the v0.2.0 mathematical integration specification. The original
v0.1.8 paper, formal core, provenance, dependency pins, application contracts and
historical D0/D1 providers remain unchanged.

- [Read the primary PDF](output/pdf/Permansson_Research_Companion_v0.2.0.pdf)
- [Download the matching TeX source](output/pdf/Permansson_Research_Companion_v0.2.0.tex)
- [Inspect the theorem map and full assumptions](output/pdf/theorem-map.json)
- [Inspect accepted source, CI and review evidence](acceptance-evidence.json)

`manuscript.json` is the single content source. The builder emits matching
Unicode TeX and a ReportLab PDF in `output/pdf/`, together with full JSON and
CSV theorem maps. The PDF is generated from the JSON, rather than compiled
from TeX. Every theorem-map entry retains the full statement, assumptions,
derivation, source module, declaration and open boundary. The TeX targets
XeLaTeX or LuaLaTeX with the DejaVu Serif/Sans fonts installed.

## Build and inspect

Python 3.12 or later with `reportlab`, `matplotlib` and `pypdf` is required.
Run from the repository root:

```text
python -m pip install -r release/v0.2.0/requirements.txt
python release/v0.2.0/build_release.py --draft --source FULL_RESEARCH_SHA
python release/v0.2.0/verify_release.py --allow-draft
```

Draft mode is explicit and visible in the document and metadata. It permits
pending claim statuses or unavailable source providers, records them in the
manifest, and supplies no accepted-source assertion. A final build omits
`--draft`, requires complete `acceptance-evidence.json`, and rejects pending
or unknown statuses. Scientific `OPEN` boundaries are valid content in a final
companion and must state what remains unproved.

Render the PDF using Poppler and inspect every page before publication:

```text
pdftoppm -r 120 -png release/v0.2.0/output/pdf/Permansson_Research_Companion_v0.2.0.pdf release/v0.2.0/tmp/pdfs/page
```

Create `tmp/pdfs/` first. Check all pages for readable equations, intact Unicode,
page breaks, headings, source names, overlapping text and clipped content.
The programmatic verifier checks content and metadata, but visual acceptance
still requires inspection of the rendered pages.

## Final acceptance evidence

Root evidence has `schema_version: 1`, `repository: "HMarcusWH/PermanssonLean"`,
the immutable `accepted_source_sha`, baseline
`6191a1acbf00867042a21c8e6c4a532af43017bc`, `acceptance_status: "accepted"`, and
one receipt per C69, C70, E1, F1, A3, D2 and X1. A2/B2 are prior research
providers; no new acceptance receipts are invented for them.

Each receipt supplies `anchor`, `source_sha`, `base_sha`,
`synthetic_merge_sha`, `pr`, `acceptance_status`, `research_run_id`, `workflow_runs`,
`c10: {status: "pass", source_head_sha, logs_url}`,
`counts: {declarations, tests, imports}`,
`review: {status, commit_sha, url}`, and `open_findings: []`.
Accepted review statuses are `pass`, `approved` and `no_findings`.
Workflow records contain their real Actions `name`, integer `run_id` and
`conclusion: "success"`, with `head_sha` bound to the receipt's source head.
The Research Lean record also has `checked_sha` equal to the synthetic merge.
Required families are original Lean, Research Lean,
executable verification and Application contract. Focused workflows are
required per anchor: C69 restart; C70 restart plus random entry; E1 those two
plus approximate quotients; F1 multi-agent protocols; A3 contraction plus
approximate quotients; D2 residence; X1 commons. The
Application contract record also includes the successful Ubuntu and Windows
`jobs: [{name, id, conclusion}]`.

Before a final build, fetch all source/base/synthetic commits referenced by
the evidence into the local Git object database. The verifier checks actual
synthetic-merge parent order and provider-head ancestry. It requires the final
selected source tree to equal X1's checked
synthetic tree. X1's actual source head must contain every manuscript provider.
These checks validate captured receipts; they do not independently contact
GitHub or manufacture evidence.
Root review must obtain those receipts directly from the actual jobs, logs and
review threads at the exact heads.

The kit also preserves the original C10 machine-evidence ZIP for every accepted
anchor under `evidence/c10/`. Publisher artifact identifiers and SHA-256 digests
are recorded in `artifact-origins.json`. Verification reads ZIP members without
extracting them: it checks the publisher digest, exact member inventory, each
nested digest, the source/base/synthetic/PR binding, and the specification hash
against the canonical Git blob at that head. These are receipts for the
original constructed six-state C10 golden, including when collected by X1's
integration run; they are not numeric certificates for the X1 commons model.

## Preservation and integrity

`manifest.json` records SHA-256 digests of the actual new kit files and a
canonical Git-blob inventory of protected historical files. Git blob SHA-1,
file mode and SHA-256 of canonical blob bytes are recorded. Windows CRLF
working copies are therefore not confused with changes to committed source.
Frozen trees are compared to the complete baseline: original Lean core,
paper, provenance, application contracts, toolchain and dependency manifests,
plus baseline ReverseSolver modules and D0/D1 documentation/executable inputs.
New D2 modules are separate research additions.
Historical verification archives, the original release JSON and paper
verification manifest, `CITATION.cff`, and the original Lean verification
inputs are also protected by their canonical baseline blobs.

The manifest deliberately excludes its own hash, avoiding a self-reference
cycle. Build intermediates under `tmp/` and Python caches are excluded.
Environment versions and the exact Lean/mathlib pins are recorded. After any
change to manuscript, evidence, scripts or other kit files, rebuild the kit
before verification or release.
New text files must have physical LF line endings before hashing; the local
`.gitattributes` retains those bytes across Windows and Linux checkouts.

The verifier checks artifact hashes, canonical preservation, exact namespace
provider lookup at the declared research commit, full theorem-map content,
matching JSON/TeX/PDF metadata and the narrative text in both renderings.
Provider lookup is a conservative source check; actual Lean elaboration and
the transitive axiom audit come from the accepted CI receipts.

## Package an accepted kit

After a successful final build and visual inspection, run:

```text
python release/v0.2.0/package_release.py
python release/v0.2.0/package_release.py --verify
```

The first command performs strict final verification and creates the
deterministic archive `release/Permansson_v0.2.0_research-kit.zip` and its
`.sha256` companion. The archive contains the kit, including its manifest,
with fixed 17 October 2026 entry metadata. It lives outside the kit to avoid
an archive/manifest hash cycle. The second command checks the archive and
its digest without modifying them. Drafts cannot be packaged as accepted kits.
