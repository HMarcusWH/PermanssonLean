# Normative build specification: Permansson v0.2.0 hardening

**Specification:** `PERMANSSON-HARDENING-1`  
**Starting commit A:** `d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618`  
**Starting tree:** `72ad841cc5b3cffc5f82979a9739b7fd03d75e15`  
**Status:** implementation contract, not an implemented or deployed product.  
**Scope names:** `HARDENING.F1`, `HARDENING.F2`, `HARDENING.F3`. These are maintenance findings, not the mathematical MultiAgent/F1 lane.

**Repository amendment:** archival CLI examples include candidate source binding, and K4 explicitly requires a separate actual-candidate Lean-scope report. The byte-identical supplied specification is preserved in [supplied/02_Implementation_Spec.md](supplied/02_Implementation_Spec.md).

MUST means an acceptance requirement. MAY means an explicitly optional implementation detail. The original package's `sources/Original_Proposal.txt` was not supplied; see the [companion provenance register](00_README.md). Audit corrections are explicit in `01_Proposal_Audit.md`.

## 1. Non-negotiable scope

Implement source preservation, exact TeX export comparison, historical archival replay, their tests, CI and a separately authorized enforcement rollout. Add or change **no Lean theorem, definition, mathematical premise, scientific status, application schema, toolchain pin or accepted release byte**.

For this maintenance PR, the complete `PermanssonLean/` and `PermanssonResearch/` trees and both Lean root files must be identical to A. That is a one-time acceptance condition for this PR, not an ongoing prohibition on future additive research. Do not wire a universal “no new Lean files” policy into the new workflow.

Do not run `lake update`, call the accepted `build_release.build()` or PDF generator, rewrite the old manifest, change archived C10 bytes, modify the accepted ZIP, or give the new maintenance receipt the old scientific acceptance identity. The permitted source changes are new verification/archival tooling, its tests, new CI, proposed settings, new archival data, and active documentation outside protected paths.

Default branch allocation: `maintenance/v020-integrity-and-archive` from A, provided that name is unused. Inspect live main and open PRs before allocating a number. “#77” is not hardcoded anywhere.

## 2. Fixed identities and roles

Use separate constants and report fields:

```text
FROZEN_CORE = c018f79ea4ce46f4f679ad5bca254509778fc53c
HISTORICAL_BASELINE = 6191a1acbf00867042a21c8e6c4a532af43017bc
RESEARCH_SOURCE = 5822cdff0fc360d9e368e10ff5f7576c3141a1b3
ACCEPTED_RELEASE = d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618
ACCEPTED_RELEASE_TREE = 72ad841cc5b3cffc5f82979a9739b7fd03d75e15
RELEASE_PR_HEAD = cdbe7ed5124781be495404122fac1de3315cb6ec
RELEASE_PR_SYNTHETIC = c70362b97ae7d0828a569fa15e194f9861b22b46
```

`C` is the candidate commit currently being verified, not any of those fixed source roles. On a PR, `H` is its head, `B` its base, and `S` its genuine GitHub synthetic merge. For the PR workflow, `C=S`. Local preflight also verifies `C=H`. After integration, `M` is the final merge commit. Require `tree(S)=tree(M)` and ordered parents `[B,H]` at acceptance.

The expected reference digest table is supplied in `registries/authority_pins.json`. In particular:

| Accepted input | SHA-256 |
|---|---|
| Original release manifest | `6065ec5431430f6804ebabffe636170d8bb349f08cfa817776b05a85bb6fe127` |
| Manuscript JSON bytes | `8022291f1ec19961578bdcb60f205fdec31057982bf9a78f6b9610bd3b184239` |
| Accepted builder | `a711fce840920846e9ffdd55b2580ebe358233ca7b432bffa78af315be69ffa6` |
| Accepted verifier | `abe1cd70491b4976ab7e3d1f06c405508e2fde7e3890f818a89b97ed88841dc2` |
| Accepted TeX | `3524da1f1ef92cfee179917efebeb3c2786b8ad484653d2f1c8f4d8036952416` |
| Accepted release ZIP | `4db31db5b805ad2f455f27e5a2e013cd13ea257984e174f6453af8f8db5b1f6c` |

The audited reference registry is useful test/review data. A copied candidate registry is not an independent authority: production derives its expected data from A and cross-checks these fixed pins.

## 3. File-level build layout

### 3.1 New source files

| New path | Responsibility and acceptance boundary |
|---|---|
| `.github/workflows/research-integrity.yml` | Three always-on independent jobs; no path filters; read-only token; exact context capture |
| `.github/repository-rules/main.proposed.json` | Reviewable disabled deployment payload; no settings changes on import |
| `verification/integrity/__init__.py` | Package marker only; no imports with side effects |
| `verification/integrity/policy.py` | Frozen identities, approved digest pins, closed-root policy and production limits |
| `verification/integrity/git_objects.py` | Sanitized bounded Git subprocesses, object/type/mode reads, NUL-delimited trees, batch blob reads |
| `verification/integrity/inventory.py` | Derive and validate 340 historical plus 29 release reference entries |
| `verification/integrity/preservation.py` | Pure candidate-object comparisons and fail-closed CLI |
| `verification/integrity/maintenance_scope.py` | One-time K4 CLI comparing both complete Lean trees and both roots with A; not a permanent required check |
| `verification/integrity/tex_export.py` | Trusted reference extraction, isolated renderer invocation, exact candidate-byte comparison |
| `verification/integrity/_tex_worker.py` | Minimal subprocess harness; only calls accepted `tex_document` |
| `verification/integrity/ci_context.py` | Validate event/head/base/checked SHA; emit source context, never mutate repository |
| `verification/integrity/reports.py` | Common deterministic report serialization and error codes |
| `verification/integrity/run_tests.py` | Fail-closed unittest discovery/execution; zero tests, missing required mappings and unexpected skips are errors |
| `verification/integrity/test_coverage.json` | Explicit mapping of required executable case IDs to test methods/subtests and suite names; live/rollout cases remain separately evidenced |
| `verification/integrity/tests/` | Reference, preservation, export, import-isolation, context and workflow contracts |
| `verification/archive/__init__.py` | Package marker only |
| `verification/archive/acquire_evidence.py` | Explicitly invoked networked acquisition into temporary output; never a required-PR network downloader |
| `verification/archive/create_bundle.py` | Read approved Git objects, create disposable staging refs, build full historical bundle |
| `verification/archive/manifest.py` | Strict archive manifest/ref/object inventory validation; no publisher authentication claim |
| `verification/archive/verify_bundle.py` | Empty-repository import, object/source checks, accepted checkout restoration and legacy verifier replay |
| `verification/archive/offline_smoke.py` | Linux network-namespace launcher and isolation attestation; fail closed if unavailable |
| `verification/archive/_offline_worker.py` | Nonroot child entry point; validates actual isolation, restores history, runs accepted replay |
| `verification/archive/tests/` | Actual disposable Git graph and archive/evidence adversaries |
| `verification/integrity/schemas/check-report.schema.json` | Versioned report contract |
| `verification/archive/schemas/archive-manifest.schema.json` | Versioned supplement inventory contract |
| `verification/integrity/requirements.txt` | Pinned `pypdf==6.10.0` for legacy replay only; F1/F2 remain standard-library-only |
| `docs/V020_HARDENING.md` | Operator guide, trust boundaries, stage status and acceptance links |

Do not edit `release/v0.2.0/verify_release.py` or its old workflow to achieve always-on checking. The new required path makes the old path-filtered workflow nonessential for ordinary merges, while leaving its historical implementation intact.

### 3.2 New archival data

Use `archival/v0.2.0/supplement-1/` for the initial separately versioned archival record:

```text
archival/v0.2.0/README.md
archival/v0.2.0/supplement-1/
  history.bundle
  archive-manifest.json
  archive-manifest.sha256
  refs.json
  objects.jsonl
  accepted-source-receipts.json
  evidence/
    acquisition-index.json
    pr76.json
    final-code-review-comment.json
    acceptance-comment.json
    review-threads.json
    final-review-submissions.json
    runs/                    # captured final-run/job metadata and logs
    R-c10-artifact-metadata.json
    R-c10.zip                # original publisher bytes, not regenerated
  tooling/
    verification/integrity/  # precise verified dependency closure of standalone tools
    verification/archive/
  OFFLINE_REPRODUCTION.md
```

`accepted-source-receipts.json` is a convenience copy of A's receipt, pinned by its original bytes. It does not acquire a new acceptance status. Existing seven C10 publisher ZIPs can be restored from `history.bundle`; duplicating them is unnecessary.

Raw evidence must be acquired before final packaging. Do not commit empty evidence files, fake capture timestamps, invented HTTP headers, invented signer identities, `PASS` placeholders, or a new C10 run relabeled as the historical R artifact.

The historical bundle contains no maintenance commit. Supplemental tooling is ordinary content-hashed data alongside it; see §9.5 for the anti-cycle construction order.

## 4. Common API, CLI and error discipline

### 4.1 Typed objects

Implement immutable Python data classes equivalent to:

```python
@dataclass(frozen=True)
class GitEntry:
    path: bytes
    mode: str
    object_type: str
    oid: str

@dataclass(frozen=True)
class ProtectedEntry:
    path: bytes
    group: Literal['historical', 'release_v020']
    mode: str
    oid: str
    sha256: str
    size: int

@dataclass(frozen=True)
class CheckContext:
    repository: str
    accepted_release: str
    checked_sha: str
    checked_tree: str
    event: Literal['local', 'pull_request', 'push', 'workflow_dispatch']
    pr_number: int | None
    head_sha: str | None
    base_sha: str | None
    run_id: int | None
    run_attempt: int | None
```

The production CLI accepts a target candidate SHA and repository path, not a replacement reference SHA. Full hexadecimal commit IDs are required; reject abbreviated identifiers and revision expressions. Test constructors may supply small fixture policies internally, but no fixture-policy switch or environment override is exposed by production commands.

### 4.2 Command contracts

```text
python -B -m verification.integrity.preservation --repo ROOT --candidate FULL_SHA --report OUT.json
python -B -m verification.integrity.tex_export --repo ROOT --candidate FULL_SHA --report OUT.json
python -B -m verification.integrity.ci_context --repo ROOT --event-file EVENT --report CONTEXT.json
python -B -m verification.integrity.run_tests --suite SUITE --report OUT.json
python -B -m verification.archive.acquire_evidence --output NEW_DIRECTORY
python -B -m verification.archive.create_bundle --repo ROOT --evidence CAPTURE_DIR --output NEW_DIRECTORY
python -B -m verification.archive.offline_smoke --repo ROOT --candidate FULL_SHA --supplement DIRECTORY --scratch NEW_EMPTY_DIRECTORY --report OUT.json
```

`verification.archive.offline_smoke` is the supported ordinary acceptance launcher: it establishes the required network namespace and privilege profile before invoking the verifier. `verification.archive.verify_bundle` is an internal namespace-child interface, not an alternate ordinary acceptance command; a bare invocation outside the enforced profile must return BLOCKED/nonzero. Do not bypass the launcher to obtain an acceptance result.

For candidate-bound CI and K4 archival acceptance, `--repo` and `--candidate` are both required on the launcher. ROOT is the tested candidate checkout and FULL_SHA is its complete candidate commit ID; on a PR this is the actual current genuine synthetic S. The parent capture binds the archive report to C before the isolated child restores accepted A. An implementation's standalone artifact-replay mode without these arguments supplies no candidate source binding and cannot discharge K4. Keep candidate C verification and accepted-A archival replay separately labeled.

`acquire_evidence` is the only online evidence-fetching command. Fetching missing Git objects is an explicit preparation action, not an automatic fallback inside either preservation or offline validation. Validators never update policy, refresh manifests, overwrite source files or create remote refs.

Exit codes: `0=PASS`, `1=verification FAIL`, `2=usage/input format error`, `3=BLOCKED infrastructure or authorization prerequisite`. All nonzero codes fail CI. A blocked local run is not counted as an adversary successfully rejected. Reports distinguish failure reason from execution limitations.

No `assert` implements a production rejection; optimized Python must not disable checks. Use explicit exceptions caught at the CLI boundary. Unexpected exceptions are nonzero failures with bounded diagnostics, never converted to warnings or empty success reports.

### 4.3 Reports

Every report records schema/version, check name, status, error code, repository, accepted source, checked SHA/tree, runtime versions, scope, completed stages, counts, and bounded evidence references. PR runs record H/B/S and run/attempt separately. A child cannot reuse a report from another SHA without a context mismatch.

Use `schema_version=1`; UTF-8; LF; sorted keys for machine output. Timestamps and run IDs may vary, but comparison/inventory payloads have deterministic ordering. Write reports atomically outside frozen source directories. Do not trust a report merely because its own status is PASS; CI must use subprocess exit status and validate context and required completed stages.

`ci_context.py` exposes `capture_context(repo, candidate, event_file=None) -> CheckContext`. Every production verifier invokes it, not merely the preliminary workflow step. In CI it reads the actual GitHub event/environment, verifies candidate equals checkout HEAD and the event SHA, and rejects disagreement with a supplied event file. Outside CI it labels reports `local`. Its standalone command writes a context record, not a fourth required check report; use `format="Permansson.Hardening.CIContext.v1"`, the CheckContext fields above, and a SHA-256 of the raw event file when one exists. The three check reports embed the same context fields. Missing context/run evidence blocks genuine-PR acceptance rather than being filled with invented values.

Recommended error families are in the supplied schema and test plan. Precise codes include `E_REFERENCE_MISSING`, `E_REFERENCE_ID`, `E_POLICY_INVENTORY`, `E_PROTECTED_MISSING`, `E_PROTECTED_TYPE`, `E_PROTECTED_MODE`, `E_PROTECTED_CONTENT`, `E_CLOSED_ADDITION`, `E_IMPORT_ORIGIN`, `E_TEX_MISMATCH`, `E_BUNDLE_HASH`, `E_BUNDLE_PREREQUISITE`, `E_BUNDLE_REFS`, `E_BUNDLE_IMPORT`, `E_GIT_FSCK`, `E_PARENT_BINDING`, `E_TREE_BINDING`, `E_OBJECT_INVENTORY`, `E_EVIDENCE_HASH`, `E_CAPTURE_ID`, `E_C10_CONTENT`, `E_LEGACY_VERIFY`, `E_NETWORK_NOT_ISOLATED`, and `E_REVIEW_INELIGIBLE`.

## 5. Canonical Git access

### 5.1 Repository preflight

Resolve the actual Git directory and common directory, reject a source-only ZIP with no object database, and require `A^{commit}` and `C^{commit}` to exist as commit objects. Verify `A^{tree}` equals the fixed accepted tree. A production candidate must descend from A; that requirement does not apply to isolated internal unit-fixture policies.

Inspect and report dangerous inherited repository/object-store redirections before clearing them. Run Git with replacement objects disabled. Reject nonempty replace refs, grafts, shallow boundaries, promisor/partial-clone configuration and alternate object-store dependencies for the full-history replay context. Clear inherited variables that redirect Git directories, namespaces, index, object directories, alternates or configuration. Do not enable lazy fetch. These conditions are particularly strict for the purported empty offline restore.

Use a known Git executable, argument lists rather than a shell, a fixed repository root, and subprocess timeouts. Set predictable locale, disable prompts/pagers, use a temporary HOME/XDG configuration context, and do not load user credential helpers in offline operations. Apply a protocol deny-by-default policy in offline Git commands, allowing only the explicit local bundle path for the import.

A local incomplete checkout may be repaired by a separate documented acquisition step. A validator must never silently repair it.

### 5.2 Tree and blob primitives

Use `git ls-tree -r -z --full-tree COMMIT` and parse NUL-separated records. Do not parse human-readable Git diffs or infer renames. Preserve raw path bytes until diagnostics are serialized. Fixed protected paths are ASCII, but unrelated new paths may contain spaces, tabs or newlines; they must not break parsing or become command fragments.

Use Git entry modes `100644`, `100755`, `120000`, `160000` and object types when classifying differences. Directory entries may need a nonrecursive lookup to detect a protected root replaced by a symlink or gitlink. Never follow repository symlinks to read protected content.

Use `git cat-file --batch` for content and size. Validate every returned OID/type/header length and exactly the declared payload length. Independently compute SHA-256 on canonical blob bytes. Reference and candidate checks include both Git OID/mode equality and the stored SHA-256. Bounded batch output is required; do not allocate arbitrary declared sizes.

Default production budgets for this release: manifest at most 2 MiB, protected blob at most 64 MiB, combined protected bytes at most 128 MiB, Git subprocess timeout 60 seconds. Measure the actual envelope in CI. A needed increase is a reviewed policy change, not a command-line waiver.

### 5.3 CRLF and dirty worktrees

Committed Git bytes define this check. A CRLF checkout of the same committed blob must pass. A newly committed CRLF conversion of a protected blob must fail. Uncommitted working-tree edits do not change the target commit; reports explicitly say `canonical_commit_objects`, not “working directory is unmodified.”

Real code/test execution must use a clean isolated checkout of the intended tested commit. Do not infer execution correctness from a canonical-object comparison when the interpreter is actually running arbitrary dirty working files.

## 6. HARDENING.F1: preserve exactly the approved boundary

### 6.1 Reference construction

`load_reference_inventory(repo) -> tuple[ProtectedEntry, ...]` must:

1. Require A and its exact tree.
2. Read A's `release/v0.2.0/manifest.json`; verify its fixed SHA-256 before parsing.
3. Parse JSON with duplicate-key rejection. Require the original schema/version and the historical baseline/research-source identities.
4. Read the 340 historical entries. Require unique valid paths, canonical mode/OID/hash shapes and exact count. Cross-check each entry against A's tree and actual canonical payload. Preserve the historical entry semantics; do not regenerate the set from candidate path patterns.
5. Read the accepted tree under `release/v0.2.0/` plus the two exact outer archive paths. Require exactly 29 distinct files. Do not trust the candidate directory listing to determine this set.
6. Derive mode, object ID, SHA-256 and size for those 29 reference blobs from A.
7. Require disjoint groups and union count 369; return sorted entries and a deterministic inventory digest.

The convenience 369-entry registry supplied with this specification must match that derivation. It is not a replacement for it.

### 6.2 Closed-root policy

Treat these roots and their descendants as closed:

```text
PermanssonLean
paper
provenance
application
verification/destructive
verification/v0.1.8_release_gate
verification/lean
release/v0.2.0
```

For each closed root, the candidate's descendant path set and root type must equal A's. A committed addition under `tmp/` or `__pycache__/` inside a closed root is still forbidden. The old verifier's temporary-file exclusions do not authorize a new tracked file in a frozen directory.

The roots themselves matter: `paper` is not the same as `paper2`; use component-aware prefix matching, not an unbounded `startswith('paper')`. Empty Git directories have no standalone content; compare actual entries and root topology.

All other historical protection is baseline-only. Preserve entries already in the 340-file inventory, while allowing unlisted ordinary research modules, new documentation outside closed roots, and `release/v0.2.1/...`. No blanket lock on `PermanssonResearch/`, `ReverseSolver/`, `docs/`, or `release/` is authorized.

### 6.3 Comparison algorithm

`compare_preserved(reference, reference_tree, candidate_tree, read_blob) -> CheckResult`:

- Validate target identity first; reference absence is `E_REFERENCE_MISSING`.
- Detect protected ancestor/type replacement without dereferencing links.
- For each pinned path: absent → `E_PROTECTED_MISSING`; different object type/symlink/gitlink → `E_PROTECTED_TYPE`; executable bit only → `E_PROTECTED_MODE`; different blob or SHA-256 → `E_PROTECTED_CONTENT`.
- Compute candidate-only entries under each closed root → `E_CLOSED_ADDITION`.
- Return all differences in bounded deterministic order, with the first primary error selected by the documented precedence above.
- PASS only when all 369 entries and every closed-root set match.

Renames are deletion plus addition; do not allow similarity heuristics to rescue them. A comment-only edit is a content edit. Candidate manifest edits and repaired outer checksums cannot update the expected reference.

### 6.4 Trust-sensitive changes

Separately report changes to the new checker, policy constants, archive tooling, schemas, workflows and proposed rules. This notification does not authenticate review. Deployment rules and human review supply that part. Do not add a self-hash that the same candidate can freely regenerate and call the checker tamper-proof.

## 7. HARDENING.F2: full deterministic export comparison

### 7.1 Reference isolation

`render_accepted_tex(repo) -> bytes` extracts exactly these trusted files from A into a new temporary directory:

```text
release/v0.2.0/build_release.py
release/v0.2.0/verify_release.py
release/v0.2.0/manuscript.json
```

The worker harness is maintained outside the frozen kit. Check builder/verifier/manuscript hashes before import. Launch a fresh subprocess using:

```text
python -I -S -B ABSOLUTE_WORKER_PATH TRUSTED_TEMP_DIR
```

The worker inserts only the trusted temporary directory for the two reference modules, imports `build_release`, verifies both modules' actual `__file__` paths, reads the raw accepted JSON bytes, and calls:

```python
result = build_release.tex_document(
    json.loads(manuscript_bytes),
    '5822cdff0fc360d9e368e10ff5f7576c3141a1b3',
    hashlib.sha256(manuscript_bytes).hexdigest(),
    False,
).encode('utf-8')
```

Use binary stdout or a fresh temporary output file. Do not re-encode through the console locale. No newline normalization, Unicode normalization, whitespace trimming, math normalization or LaTeX pretty-printer is allowed. Require clean subprocess termination, bounded stderr, output at most 2 MiB, and a 30-second timeout.

The accepted export must independently match the fixed expected SHA-256 and length before comparison with the candidate. This is a regression check on the reference call itself. The full renderer runs; do not replace it with comparison only against a pinned TeX hash.

### 7.2 Candidate comparison

Read `C:release/v0.2.0/output/pdf/Permansson_Research_Companion_v0.2.0.tex` by Git object ID. Require a regular-file type/mode and exact byte equality with the generated output. On mismatch, emit `E_TEX_MISMATCH`, both digests and lengths, and the first differing byte offset; a bounded escaped context or unified diff is diagnostic only.

F2 must not invoke F1 as a prerequisite inside its comparator. It must detect an altered equation even if candidate manifest/receipt hashes were consistently repaired. The full CI requires both checks, but they are independently testable predicates.

### 7.3 Explicit exclusions

Do not import candidate builder/helper modules, execute the old build entry point, regenerate PDF images, write `manifest.json`, or update a receipt. No ReportLab, matplotlib, pypdf, TeX engine or font installation is required for this specific check. A complete old release replay separately needs pypdf. Exact TeX correspondence does not assert fresh PDF visual review or correctness of the source mathematics.

## 8. Evidence acquisition contract

### 8.1 Inputs to capture

Read the seven milestone source receipts from A. Capture final R independently from the accepted PR #76 record:

```text
source   cdbe7ed5124781be495404122fac1de3315cb6ec
base     5822cdff0fc360d9e368e10ff5f7576c3141a1b3
synthetic c70362b97ae7d0828a569fa15e194f9861b22b46
main     d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618
```

Acquire original R C10 ZIP `12106535829` from run `39045919534`; enforce the published SHA-256 and 9,377-byte length before parsing. Retain raw artifact metadata and acquisition provenance. Do not repackage it or use X1's older C10 ZIP as a substitute.

Capture the final code-review comment `6235925253`, acceptance comment `6236142249`, PR metadata, paginated review submissions and review threads, and final run/job metadata and logs. Freeze their acquisition dates as actual observed times. The old final review is a code-review artifact, not an unrestricted mathematical peer-review certificate.

### 8.2 Authentication and file handling

Acquisition may use an explicit read-authorized token or connector. Do not grant write or administration permissions for downloading evidence. Never embed tokens, authorization headers, cookies or temporary signed download URLs in the supplement. Record original API endpoint, request time, response time if observed, content digest, HTTP status and non-sensitive version/ETag metadata actually returned. A normalized tool response must be labeled normalized, not passed off as a raw HTTP byte capture.

Reject wrong repository, PR, run, source head, artifact ID or digest; follow paginated reads to completion. A missing or expired artifact blocks historical archival completion unless an independently retained byte-identical original is supplied and verified. A new successful CI run can be useful new evidence but is not the historical object.

Downloaded bytes go into a new temporary directory, with output overwrite forbidden by default. Bounded streaming limits precede parsing. All archive members must be checked for inventory, size and safe path before decompression, following the already fixed C10 boundary. Hashes authenticate against a trusted external digest; a digest stored only beside a file is not independent publisher authentication.

## 9. HARDENING.F3-A: full-history supplement construction

### 9.1 Required references

Use the exact 36 names and 26 distinct commit IDs in `registries/archive_commit_registry.json`. Names live under `refs/archive/permansson/v0.2.0/`. Four name the release, research source, historical baseline and original core; each of C69/C70/E1/F1/A3/D2/X1/R has `head`, `base`, `synthetic` and `main` refs.

Do not resolve their meanings through live branch tips, dates, abbreviations or `refs/pull/N/merge` at packaging time. A current pull ref can change. Fetch immutable objects explicitly during preparation and verify their full IDs.

### 9.2 Disposable staging repository

Create a new bare staging repository with sanitized configuration. Fetch or copy the exact approved commit closures into it from the acquired object database. The source database must not be shallow, promisor-backed or borrowing alternates for the final self-contained claim. Materialize only the 36 named refs in staging; verify every ref points directly to the expected commit.

Inspect actual commit objects: each milestone's synthetic and main merge has ordered parents `[base, head]`; their trees are identical; seven accepted main merges are ancestors of G, and R main is A with the exact accepted tree. `FROZEN_CORE` and `HISTORICAL_BASELINE` must be resolvable and included in the restored history.

Then create a full bundle from the exact names:

```text
git -C STAGING bundle create --version=2 history.bundle \
    refs/archive/permansson/v0.2.0/release \
    ... every other exact approved ref ...
```

Pass refs as an argument list or validated stdin. Do not use `--all`, revision exclusions, ranges, `--since`, a shallow cutoff, or an object filter. Do not alter refs in the user's working repository; do not push the staging refs remotely.

### 9.3 Object and ref inventory

Enumerate the complete reachable object closure of the 36 refs, sorted by object ID. Record each object's OID, type, size and SHA-256 of its uncompressed canonical payload. Use bounded `cat-file` batch reads. `objects.jsonl` is the actual full closure, not just the 26 named commits.

Record the exact ref-to-commit map in `refs.json`. Both files are inventoried in `archive-manifest.json`. Parent/tree relationships belong to milestone records and are checked independently of fsck.

Default limits: bundle 256 MiB, uncompressed object closure 1 GiB, 200,000 objects, any single object 128 MiB, input metadata 8 MiB. These are explicit release-profile safety budgets, not measured current sizes. Record measured sizes when the real bundle is created; do not silently raise limits when validation fails.

### 9.4 Manifest and hashes

The archive manifest records format/version, accepted source/tree, fixed provenance roots, ref and object inventory digests/counts, bundle digest/size/format, captured-evidence file digests, R C10 identity/digest, tooling digests, dependency requirements and precise reproduction levels.

It must inventory every delivered supplement file except itself and its own detached checksum. This self-exclusion is exact and explicit. No arbitrary file exclusion or “ignored directory” is permitted in the supplement. The detached manifest checksum is an integrity aid; publication of its hash outside the archive is the independent comparison point.

Missing fields, unknown format versions, duplicate keys, duplicate paths, traversal components, symlinks, extra files, malformed hashes and count disagreement fail. Do not require a byte-identical independently rebuilt Git bundle across Git versions: require the delivered bundle's exact published digest and the reconstructed object/ref closure. Byte reproducibility of the older ZIP remains separately enforced.

### 9.5 Tooling and self-reference

Build tooling at a clean pre-packaging maintenance commit `T`. Copy the exact source bytes needed for offline replay under `tooling/`, recording `T` and source blob/content hashes. The history bundle still ends at A plus its declared historical synthetic roots; it does not contain T or the later supplement commit.

Generate the supplement outside the repository first; verify it; then commit its files as a new maintenance commit. If tooling changes later, update the tooling copy and its manifest in a new supplement candidate, preserving all accepted historical inputs. Final maintenance head and merge acceptance remain in a subsequent external receipt.

This yields an acyclic dependency graph: historical source/evidence → bundle/tooling files → supplement manifest → maintenance integration → external acceptance. No file is required to predict its own future commit or archive hash.

## 10. HARDENING.F3-A: independent offline restore

### 10.1 What “offline” requires

Prepare Python 3.13, Git and `pypdf==6.10.0` before the offline boundary. Preservation and TeX tests use only the standard library; the frozen full release verifier imports pypdf. Do not install ReportLab/matplotlib or Lean/mathlib merely to replay the existing release artifacts.

The canonical CI adapter is a new Linux network namespace created with `unshare --net`, with execution dropped back to the runner's ordinary UID/GID before processing candidate inputs. Capture the parent namespace identity and verify the child uses a different namespace with no external route; require a denied outward socket attempt, not merely a timeout. Clear supplementary groups and capabilities and set no-new-privileges before starting the child parser. Close inherited nonstandard file descriptors. Clear inherited proxy/credential variables. Do not run an untrusted archive parser as root. Git protocol restrictions provide defense in depth but do not by themselves prove absence of arbitrary Python networking.

If namespace isolation is unavailable, return BLOCKED/nonzero. A future container-based adapter is possible, but requires separately tested network/credential/mount isolation; it is not an automatic fallback to online execution.

### 10.2 Clean-room restore algorithm

`verify_supplement(supplement, scratch, require_isolation=True)` must:

1. Require a new empty scratch location. Reject reuse, preexisting `.git`, inherited alternate object stores, unexpected remotes or a symlinked scratch path.
2. Validate bounded manifest structure and every delivered payload digest. Check original R C10 external digest before reading its members.
3. Read the bundle header and require supported SHA-1 bundle format, no prerequisites, no filter capability and the exact ref inventory. The v2 writer is the canonical build profile; reject unknown capabilities rather than guessing.
4. Initialize an empty bare repository and run `git bundle verify`. Capture output and exit code, but do not stop at success.
5. Import the exact refs from the local bundle via explicit refspecs. Import failure is `E_BUNDLE_IMPORT` even when header verification passed.
6. Run `git fsck --full --strict`; inspect the complete object database and compare the exact object inventory. No borrowed prerequisites, alternates or promisor objects are allowed.
7. Resolve every required ref and object type; verify milestone ordered parents, tree equality, ancestry and exact A tree. Wrong refs to valid objects fail even if fsck succeeds.
8. Restore a clean detached accepted checkout at A using canonical blob bytes. Require normal source files and their recorded executable modes; do not invoke hooks, candidate smudge filters or symlink targets. Verify the accepted source tree and all 369 pins in the restored repo.
9. Run the isolated TeX comparison against restored A.
10. Run the accepted `release/v0.2.0/verify_release.py` in final mode and `package_release.py --verify` in the restored accepted checkout. Never call the packager without `--verify`.
11. Run the old 29 release test methods in that isolated accepted checkout and record all failures/skips. They use temporary candidates; they must not edit the source archive.
12. Validate the separately archived R C10 original ZIP with the accepted content checker and the R-specific source/base/synthetic/PR context; bind it to captured successful R run evidence. Do not invoke fresh Lean or claim offline capture replay is proof execution.
13. Recheck delivered payload hashes and clean accepted source state after replay; write a report outside the source tree.

`archive-reproducibility` attests restoration of A and replay of its evidence. It is not a new build of C. `frozen-source-preservation` and `release-export-integrity` separately bind C's relevant content to A. All three are required; the old Lean/research workflows remain responsible for new candidate mathematics.

### 10.3 Failure injection must exercise the real chain

Test main-only bundle omission, named-ref success, missing synthetic object, valid but wrong ref target, incremental prerequisite, truncated pack with intact header, corrupted object, altered parent order, mismatched synthetic/main trees, extra refs, extra delivered files, mismatched R evidence and blocked network isolation. Do not count a checksum failure as testing later parent validation; repair outer checksums for the semantic adversaries and assert the intended later error.

## 11. CI integration

### 11.1 Events and permissions

Use `pull_request` on base `main`, `push` on `main`, and optional `workflow_dispatch` for diagnostics. No path filters. Do not use `pull_request_target` to execute candidate code. Do not silently enable merge queues; they have different event/source-binding requirements and the existing C10 path is PR-specific.

Set `permissions: contents: read`; `persist-credentials: false`; no secrets; no privileged network credentials; no self-hosted privileged runner for untrusted forks. Pin third-party actions to reviewed full commit IDs and record them. The template supplies the action commits observed in accepted release CI, not a silent upgrade to new major versions.

Each of the three jobs is independent, with its own checkout and no `needs` chain that can turn a failed prerequisite into a skipped required job. It must exit nonzero on a missing report, incomplete stage, unsupported environment or failed prerequisite. Do not use `continue-on-error` for any verifier. Diagnostic artifact uploads may run with `always()`, but may not determine the verification result.

### 11.2 Job responsibilities

| Required context | Required work |
|---|---|
| `frozen-source-preservation` | Validate event/checked SHA, load A, compare candidate 369 pins/closed roots, run preservation/reference/context/workflow tests |
| `release-export-integrity` | Validate event/checked SHA, independently isolate exporter and compare candidate TeX, run equation/import-origin/reference-argument tests |
| `archive-reproducibility` | Validate the candidate's supplement inventory; run archive unit adversaries; prepare pypdf before isolation; run real empty/network-disabled restore, legacy verifier/package check, old 29 release tests and original R C10 replay |

Do not fetch historical evidence from Actions in each job. The supplement carries it. F1/F2 require the accepted A objects, obtained through the checkout's full history or an explicit fixed-SHA preparation fetch. F3 proves its own historical objects come from the delivered bundle, not from the job's checkout.

On a genuine PR, the context checker must confirm checkout `HEAD=S`, actual parents `[B,H]`, repository identity and event PR number. For a push, confirm checkout `HEAD` equals the event's `after` SHA and the ref is main. Dispatch reports are marked diagnostic and cannot substitute for a required genuine-PR run.

### 11.3 Existing jobs and exact names

Preserve existing Lean, Research Lean, executable verification and both Application contract OS jobs. The live observed required contexts are:

```text
build
research
executable-verification
Application contract (ubuntu-latest)
Application contract (windows-latest)
frozen-source-preservation
release-export-integrity
archive-reproducibility
```

Their expected publisher is GitHub Actions App ID `15368`, observed from actual check runs. Read back new check names/App IDs after the first genuine PR run before activating rules. Do not require the legacy path-filtered `research-release` globally. Keep names unique across other workflows.

Any candidate change after review requires new exact-head evidence. A changed base requires a genuine new synthetic-merge check; a manually triggered run on a branch is not substituted for that event.

## 12. Test implementation requirements

The detailed test plan is in `03_Acceptance_Test_Plan.md` and its machine registry. Each case has an intended validator and error code. The plan is normative coverage, not a claimed number of tests already executed.

Unit tests use actual disposable Git repositories where object semantics matter. A private fixture constructor may generate its own baseline policy; production CLI cannot choose that fixture. Tests involving accepted reference bytes must cross-check the pinned accepted exporter and inventory, not independently rewrite a “similar” implementation.

For LF/CRLF tests, commit one canonical file, then checkout under two settings; prove same Git blob passes. Separately commit converted content and prove rejection. Set mode/symlink/gitlink entries through Git plumbing where Windows working-file permissions cannot express them reliably.

For negative tests, repair earlier hashes where required to reach the intended failure. Include a positive control immediately adjacent to each negative family. Assert exact error code and stage; a failed import, missing tool, or timeout does not satisfy an equation or preservation assertion.

Test the production importer against a candidate shadow module with an observable marker; the marker must never execute. Export tests must still run independently when F1 would reject their altered TeX. Test truncated-bundle rejection after successful header verification, as demonstrated in the audit fixture.

The new `run_tests` entry point MUST reject zero discovered tests, absent required test-method mappings, duplicate case mappings without explanation, test loading errors, any failure, and unexpected skips. Accept suite names only from `reference`, `preservation`, `context`, `workflow`, `tex`, and `archive`; resolve their directories/patterns through the checked-in mapping, not arbitrary command arguments. Validate each executable requirement ID has a mapped method/subtest and record execution at that granularity. Live-PR and authorized-rollout cases cannot be replaced by unit mocks and are tracked separately. An unmodified `unittest discover` command returning success with zero cases is not an adequate CI gate. `run_tests` writes `Permansson.Hardening.Tests.v1` records (suite, method/subtest results, requirement IDs, runtime and counts), not a fourth required GitHub check.

All new code must syntax-check, all new unit tests must pass, and the existing research/legacy/application suites must remain green in their supported pinned CI. Do not edit existing tests to reduce their expected counts or repair unrelated assertions.

## 13. Repository enforcement rollout

The supplied disabled proposed ruleset encodes one eligible approval, stale-review dismissal, last-push approval, resolved threads, strict current-base checks, merge commits only, no force push/deletion, and no bypass actors. It is not deployed.

Before activation: identify an independent reviewer who can actually approve this repository's PRs. Neither the author nor a no-major-issues comment discharges the required approval. Confirm the reviewer is distinct from the latest pusher under the intended last-push policy. If no eligible reviewer exists, report `E_REVIEW_INELIGIBLE` and leave deployment open; do not lower requirements implicitly.

After explicit authorization, apply the settings and read the individual ruleset and effective branch rules back with sufficient permissions to see bypass actors. Check all eight required contexts and App bindings, strict base policy, review fields, active state, matching main condition, merge method, and bypass list. A successful API write without read-back is not acceptance. Missing bypass data is unknown, not empty.

Preserve the existing merge-commit strategy and do not enable `required_linear_history`, squash, rebase, auto-merge or a merge queue as an incidental change. Settings, a remote release tag and external supplement publication are separate authorized operations, not PR code side effects.

Use a fresh annotated remote tag such as `permansson-v0.2.0-research` only after checking it is unused and obtaining authorization. Resolve its peeled commit back to A. Record signing status truthfully; do not invent a signature. Never move an existing tag to make it match. Publish the new supplement separately with its external digest and verify retrieval/hash from the chosen destination.

## 14. Acceptance and completion

### Code acceptance

Require exact-head local tests, three new genuine synthetic-merge jobs, existing full CI, fresh PR-only C10 evidence for this maintenance H/B/S, no unresolved findings, and explicit merge approval. The new maintenance C10 capture is additional integration evidence and must not overwrite the historical R artifact.

Require no release-path changes and all 369 pins unchanged. Require no changes to either Lean tree, either Lean root, dependency pins or application semantics in this maintenance PR. New tests are outside the accepted kit. Confirm that a PR with zero changed `release/**` paths visibly executed all three new checks.

**Separate mandatory K4 acceptance condition:** execute the shipped one-time scope CLI from a clean isolated checkout of the actual current S, before merge:

```text
python -B -m verification.integrity.maintenance_scope --repo . --candidate FULL_SHA --report /scratch/maintenance-scope.json
```

FULL_SHA must be the complete current genuine synthetic merge SHA, not a fixture, H, a previous S or a revision expression. Require subprocess exit 0 and a PASS `Permansson.Hardening.Check.v1` report with check `maintenance-Lean-scope`, the fixed accepted A/tree, the checked candidate S/tree, all four compared paths, and `details.completed_stages` containing `fixed_authority` and `complete_Lean_scope_comparison`. The four paths are `PermanssonLean/`, `PermanssonResearch/`, `PermanssonLean.lean` and `PermanssonResearch.lean`; additions, edits and deletions anywhere in their complete scope fail, including paths outside the 369 permanent pins. The report must identify `details.acceptance_only=true` and `details.permanent_preservation_policy=false`.

Join that report to independently captured current GitHub PR metadata for H/B/S. Verify that the report's checked SHA and tree are S and tree(S), that S has ordered parents `[B,H]`, and that the capture still describes the current head and base. A local invocation remains labeled local: its JSON does not manufacture a genuine GitHub event or publisher authentication. Retain the independent source receipt beside the scope report. A missing report, nonzero result, stale tuple, wrong tree, or incomplete stages blocks K4. Repeat this one-time check after any head or base change.

PRES-23 remains a unit-level regression requirement for the checker. Passing its fixture tests does not discharge this additional actual-candidate K4 condition. Do not add this scope restriction to the permanent three-job workflow or turn it into a new always-on context; future additive research remains allowed by the permanent policy. This condition does not add or renumber any of the 108 acceptance cases.

Record H, B, S and M separately, their tree relationships, actual run IDs/attempts, exact test outcomes, code/fixture hashes, supplement hash, review identity and open deployment steps. Do not infer broad mathematical completion from maintenance PASS.

### Operational completion

Use these independently tracked states:

```text
F1.code_verified
F1.enforcement_active
F2.code_verified
F2.enforcement_active
F3.original_evidence_captured
F3.bundle_materialized
F3.offline_restore_verified
F3.ruleset_active_and_read_back
F3.remote_tag_verified
F3.supplement_published_and_retrieved
```

A code PR may be accepted with operational items explicitly OPEN. Overall F3 is closed only when the required archival and authorized operational states are evidenced. If tag/publication destination or reviewer identity is undecided, report it as a deployment prerequisite, not an implementation guess.

### Research boundary carried forward unchanged

Strict MA2 remains OPEN; A3 remains conditional; D2 retains the proved initialized finite-path reach-and-stay scope; both X1 replete-region Exact-GR claims fail; numerical margin reflection and unrestricted discounted-strategy verification remain OPEN. This maintenance programme neither proves nor edits any of them.
