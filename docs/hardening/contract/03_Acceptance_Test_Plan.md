# Acceptance test plan

**Repository amendment:** PRES-23 explicitly covers additions, edits and deletions, including unprotected Lean paths. The byte-identical supplied plan is preserved in [supplied/03_Acceptance_Test_Plan.md](supplied/03_Acceptance_Test_Plan.md).

**108 specified acceptance cases.** These are requirements for the build, not tests claimed to have run. The new independent source/exporter subset is reported in `evidence/source_probes.json`; the original author's E1 source-ZIP and toy-Git probe records were NOT_SUPPLIED. See `00_README.md` for provenance.

Every negative case must have a nearby positive control and assert the intended code/stage. A missing tool, timeout or earlier checksum failure is not a substitute for exercising the specified condition. `BLOCKED_...` is an unmet environment/authorization requirement, not successful rejection of a malicious input.

Production policy cannot be overridden from the CLI; small reference policies are injected only through internal test constructors. Real history and real CI acceptance are distinct from disposable-fixture tests.

## REF

| ID | Case and stimulus | Expected | Level |
|---|---|---|---|
| REF-01 | **Accepted authority exists** — Resolve A as a commit and verify its fixed tree and manifest hash. | `PASS` | unit |
| REF-02 | **Missing accepted commit** — Production command in a source-only archive or repo without A. | `E_REFERENCE_MISSING` | unit |
| REF-03 | **Short or expressive candidate ref** — Supply abbreviated SHA, HEAD~1 or a newline/option-like value. | `E_REFERENCE_ID` | unit |
| REF-04 | **Wrong accepted tree** — Fixture authority commit resolves to an unexpected pinned tree. | `E_REFERENCE_ID` | unit |
| REF-05 | **Duplicate inventory key** — Direct policy-parser fixture has duplicate JSON keys. | `E_POLICY_INVENTORY` | unit |
| REF-06 | **Duplicate historical path** — Direct fixture has 340 rows with one duplicated path and one omitted. | `E_POLICY_INVENTORY` | unit |
| REF-07 | **Inventory count mismatch** — Direct fixture has 339 or 341 entries; do not use the candidate manifest as reference. | `E_POLICY_INVENTORY` | unit |
| REF-08 | **Reference blob metadata mismatch** — Fixture entry differs from actual reference mode, OID or SHA-256. | `E_POLICY_INVENTORY` | unit |
| REF-09 | **Shallow history** — Use an actual depth-limited clone for full-history replay. | `E_HISTORY_SHALLOW` | unit |
| REF-10 | **Promisor history** — Set promisor/partial-clone metadata before offline validation. | `E_HISTORY_EXTERNAL` | unit |
| REF-11 | **Borrowed object database** — Use objects/info/alternates or inherited GIT_ALTERNATE_OBJECT_DIRECTORIES. | `E_HISTORY_EXTERNAL` | unit |
| REF-12 | **Replacement object context** — Add replace refs or grafts; never let the overlay redefine A. | `E_HISTORY_EXTERNAL` | unit |
| REF-13 | **Path/parser safety** — Unrelated new paths contain spaces, tabs and newlines; fixed paths are still compared literally. | `PASS` | unit |
| REF-14 | **Production cannot refresh** — Pass --refresh, --update-baseline or an unsupported policy override. | `USAGE_ERROR` | unit |
| REF-15 | **Target outside accepted ancestry** — Resolve a valid candidate commit not descending from A. | `E_ANCESTRY` | unit |

## PRES

| ID | Case and stimulus | Expected | Level |
|---|---|---|---|
| PRES-01 | **Unchanged 369 pins** — Run production reference comparison on A. | `PASS` | unit |
| PRES-02 | **Comment-only frozen core** — Append a Lean comment to PermanssonLean/Regime/Constitution.lean. | `E_PROTECTED_CONTENT` | unit |
| PRES-03 | **Comment-only historical solver** — Append a comment to PermanssonResearch/ReverseSolver/C10ReceiptSemantics.lean. | `E_PROTECTED_CONTENT` | unit |
| PRES-04 | **Semantic frozen edit** — Change a protected theorem body in a disposable commit. | `E_PROTECTED_CONTENT` | unit |
| PRES-05 | **Deletion** — Delete an inventoried paper or source file. | `E_PROTECTED_MISSING` | unit |
| PRES-06 | **Rename** — Rename a protected file while preserving its bytes. | `E_PROTECTED_MISSING` | unit |
| PRES-07 | **Executable bit** — Change 100644 to 100755 through Git index plumbing. | `E_PROTECTED_MODE` | unit |
| PRES-08 | **Symlink replacement** — Replace a protected file by 120000 entry pointing to original bytes. | `E_PROTECTED_TYPE` | unit |
| PRES-09 | **Gitlink replacement** — Replace a protected root or file by a 160000 gitlink. | `E_PROTECTED_TYPE` | unit |
| PRES-10 | **Historical closed-tree addition** — Add paper/new.md or another unlisted closed-root descendant. | `E_CLOSED_ADDITION` | unit |
| PRES-11 | **Version-specific closed addition** — Commit release/v0.2.0/new.txt, tmp/x or __pycache__/x. | `E_CLOSED_ADDITION` | unit |
| PRES-12 | **Nested closed-root addition** — Add a new subdirectory and file under a closed root. | `E_CLOSED_ADDITION` | unit |
| PRES-13 | **Prefix lookalike allowed** — Add paper2/note.md outside the exact paper root. | `PASS` | unit |
| PRES-14 | **New research module allowed** — Add an ordinary new ReverseSolver module not present in the historical inventory. | `PASS` | unit |
| PRES-15 | **Documentation allowed** — Add an ordinary document outside pinned paths and closed roots. | `PASS` | unit |
| PRES-16 | **New release version allowed** — Add release/v0.2.1/example.txt, leaving v0.2.0 untouched. | `PASS` | unit |
| PRES-17 | **Manifest removal and repaired hashes** — Delete a protected row from candidate manifest and repair its candidate archive hashes. | `E_PROTECTED_CONTENT` | unit |
| PRES-18 | **Published archive replacement** — Change old ZIP bytes and repair its checksum file. | `E_PROTECTED_CONTENT` | unit |
| PRES-19 | **Scientific promotion rejected as bytes** — Change F1.MA2 from OPEN in the frozen manuscript and rebuild candidate outputs. | `E_PROTECTED_CONTENT` | unit |
| PRES-20 | **LF/CRLF checkout invariance** — Checkout one canonical commit under LF and CRLF settings, including a Windows test. | `PASS` | unit |
| PRES-21 | **Committed CRLF conversion** — Commit the converted protected content rather than merely checking it out. | `E_PROTECTED_CONTENT` | unit |
| PRES-22 | **Dirty worktree caveat** — Edit working bytes without committing; canonical-commit predicate stays PASS and report does not claim workspace cleanliness. | `PASS` | unit |
| PRES-23 | **Maintenance-only Lean scope** — One-time PR acceptance: reject any addition, edit or deletion under `PermanssonLean/` or `PermanssonResearch/`, or of `PermanssonLean.lean` or `PermanssonResearch.lean`, including unprotected paths outside the 369-file inventory. Compare both complete Lean trees and both roots with A; unchanged scope passes. This is separate from the always-on policy so future additive research remains allowed. | `E_MAINTENANCE_SCOPE` | unit |

## TEX

| ID | Case and stimulus | Expected | Level |
|---|---|---|---|
| TEX-01 | **Accepted complete export** — Isolated trusted two-module renderer regenerates 71,379 bytes and all ten equations. | `PASS` | unit |
| TEX-02 | **Wrong render revision** — Call reference using A instead of G in an internal renderer regression fixture. | `E_EXPORT_REFERENCE` | unit |
| TEX-03 | **Equation replaced by 0=1** — Mutate one equation body while retaining all captions/narrative; invoke F2 alone. | `E_TEX_MISMATCH` | unit |
| TEX-04 | **Sign changed** — Flip one minus sign in an equation; leave surrounding prose unchanged. | `E_TEX_MISMATCH` | unit |
| TEX-05 | **Fraction changed** — Alter one rational denominator without changing captions. | `E_TEX_MISMATCH` | unit |
| TEX-06 | **Equation removed** — Remove one complete companionEquation block. | `E_TEX_MISMATCH` | unit |
| TEX-07 | **Equation duplicated** — Duplicate an existing equation with its caption. | `E_TEX_MISMATCH` | unit |
| TEX-08 | **Equation order changed** — Swap two equation blocks; inclusion-only checks would still pass. | `E_TEX_MISMATCH` | unit |
| TEX-09 | **Caption or metadata changed** — Change caption, label-like text or source header only. | `E_TEX_MISMATCH` | unit |
| TEX-10 | **Trailing newline changed** — Drop or duplicate the final newline. | `E_TEX_MISMATCH` | unit |
| TEX-11 | **Repaired receipt attack** — Repair candidate inventory and compile/review input hashes after an equation mutation; F2 is independent of F1. | `E_TEX_MISMATCH` | unit |
| TEX-12 | **Candidate builder shadow** — Candidate builder writes a marker if imported; trusted render must ignore it and accepted candidate TeX still matches. | `PASS_WITH_MARKER_ABSENT` | unit |
| TEX-13 | **Candidate verifier shadow** — Candidate verify_release.py writes a marker; F2 alone must not import it. | `PASS_WITH_MARKER_ABSENT` | unit |
| TEX-14 | **PYTHONPATH/startup injection** — Place shadow modules/sitecustomize in cwd and PYTHONPATH; worker uses -I -S. | `PASS_WITH_MARKER_ABSENT` | unit |
| TEX-15 | **Missing accepted helper** — Internal trusted-input fixture omits verify_release.py. | `E_REFERENCE_MISSING` | unit |
| TEX-16 | **Wrong trusted helper hash** — Internal fixture replaces accepted helper bytes. | `E_EXPORT_REFERENCE` | unit |
| TEX-17 | **Render timeout** — Inject a controlled hanging test worker, without changing production authority switches. | `E_COMMAND_TIMEOUT` | unit |
| TEX-18 | **PDF path never called** — Patch reference PDF/build entry points in a fixture to throw if called; TeX-only operation succeeds. | `PASS` | unit |
| TEX-19 | **Output budget** — Fixture renderer returns more than the output size budget. | `E_LIMIT` | unit |
| TEX-20 | **Candidate TeX is symlink** — Candidate TeX entry is type 120000. | `E_TEX_TYPE` | unit |

## ARCH

| ID | Case and stimulus | Expected | Level |
|---|---|---|---|
| ARCH-01 | **Named synthetic full restore** — Toy base/head/S/M graph, all required named refs, fresh empty repo, import and fsck. | `PASS` | unit |
| ARCH-02 | **Main-only graph** — Build a valid full main-only bundle while synthetic object is unreferenced. | `E_BUNDLE_REFS` | unit |
| ARCH-03 | **Missing synthetic object** — Repair ref/manifest test fixture so required synthetic cannot be resolved after import. | `E_BUNDLE_REFS` | unit |
| ARCH-04 | **Wrong valid ref target** — Point a required ref at another valid commit; repair outer hashes. | `E_BUNDLE_REFS` | unit |
| ARCH-05 | **Incremental prerequisite** — Create base..main bundle and verify against a genuinely empty repo. | `E_BUNDLE_PREREQUISITE` | unit |
| ARCH-06 | **Truncated payload after intact header** — Truncate pack bytes; keep header valid and repair outer hash; header verify may succeed, import must fail. | `E_BUNDLE_IMPORT` | unit |
| ARCH-07 | **Checksum mismatch** — Flip bundle bytes without repairing its independently expected digest. | `E_BUNDLE_HASH` | unit |
| ARCH-08 | **Corrupt object integrity** — Inject a corrupted loose object into restored fixture before fsck. | `E_GIT_FSCK` | unit |
| ARCH-09 | **Extra ref** — Include an undeclared maintenance or unrelated branch ref. | `E_BUNDLE_REFS` | unit |
| ARCH-10 | **Extra object inventory** — Manifest inventory includes an object outside the required restored closure. | `E_OBJECT_INVENTORY` | unit |
| ARCH-11 | **Source/base parent reversal** — Fixture synthetic merge has reversed valid parents. | `E_PARENT_BINDING` | unit |
| ARCH-12 | **Different synthetic/main tree** — Both commits valid and same parents, but their trees differ. | `E_TREE_BINDING` | unit |
| ARCH-13 | **Archive self-inclusion** — Builder receives a maintenance/supplement commit as an extra root. | `E_BUNDLE_REFS` | unit |
| ARCH-14 | **Original R publisher hash** — Real R bytes are acquired with the published 9,377-byte identity and digest. | `PASS` | integration |
| ARCH-15 | **Wrong R run or artifact** — Valid ZIP/capture claims another run, head, artifact ID or repository. | `E_CAPTURE_ID` | unit |
| ARCH-16 | **R payload mismatch** — R ZIP bytes differ from externally observed published digest. | `E_EVIDENCE_HASH` | unit |
| ARCH-17 | **R content inconsistency** — Fixture changes proof/arithmetic content and repairs nested hashes; direct content validator must fail. | `E_C10_CONTENT` | unit |
| ARCH-18 | **Missing final code review** — Remove required captured final-review file from supplement. | `E_CAPTURE_ID` | unit |
| ARCH-19 | **Extra or unsafe delivered file** — Add traversal, duplicate key/path, unlisted payload or symlink in supplement. | `E_MANIFEST_FORMAT` | unit |
| ARCH-20 | **Unavailable isolation** — Network namespace cannot be created; never fall back to online success. | `BLOCKED_E_OFFLINE_UNAVAILABLE` | unit |
| ARCH-21 | **Isolation actually enforced** — New namespace has no external route; outward socket attempt is denied. | `PASS` | unit |
| ARCH-22 | **Borrowed offline prerequisites** — Restored repository inherits alternates/remotes/promisor state. | `E_HISTORY_EXTERNAL` | unit |
| ARCH-23 | **Legacy accepted verifier replay** — Actual supplement restores A; final verifier and package --verify run successfully. | `PASS` | integration |
| ARCH-24 | **Missing offline dependency** — pypdf is unavailable in the isolated runtime. | `BLOCKED_E_DEPENDENCY_MISSING` | unit |
| ARCH-25 | **Old bytes remain unchanged** — Rehash source kit and supplement after replay and legacy 29-test suite. | `PASS` | unit |
| ARCH-26 | **Rebuild semantics not universal bytes** — Two supported Git builds may vary pack bytes; delivered digest is fixed, reconstructed required ref/object closure must match. | `PASS` | unit |
| ARCH-27 | **Bounded archive inputs** — Declared bundle/object/metadata size exceeds policy cap. | `E_LIMIT` | unit |

## CI

| ID | Case and stimulus | Expected | Level |
|---|---|---|---|
| CI-01 | **Zero release diff real PR** — A genuine maintenance PR changes only new tooling/docs/archival paths; all three jobs execute. | `PASS` | live_pr |
| CI-02 | **Actual synthetic parents** — On PR, compare event H/B with git show S parents and actual checkout HEAD. | `PASS` | live_pr |
| CI-03 | **Wrong checkout context** — Use H or a previous synthetic instead of current S. | `E_CONTEXT` | unit |
| CI-04 | **Head changes after green** — Push a new commit; old reports cannot be reused for new head. | `E_CONTEXT` | live_pr |
| CI-05 | **Base changes after green** — Refresh genuine synthetic CI against updated B and capture new S; old pair fails. | `E_CONTEXT` | live_pr |
| CI-06 | **Workflow filters forbidden** — Static test introduces paths/paths-ignore or docs-only job skip around new checks. | `E_WORKFLOW_CONTRACT` | unit |
| CI-07 | **Skip cannot become PASS** — Simulate failed prerequisites, absent reports, zero test discovery, missing case mappings and unexpected skips; none may become success. | `E_REPORT` | unit |
| CI-08 | **Unique actual contexts** — Observe eight intended required job contexts from GitHub Actions; new names not workflow titles. | `PASS` | live_pr |
| CI-09 | **Manual run not acceptance** — Try to use a workflow_dispatch diagnostic report as genuine-PR acceptance; reject that use at the acceptance context validator. | `E_CONTEXT` | unit |
| CI-10 | **No candidate credentials** — Fork-safe job has contents:read, persist-credentials:false and no write token/secrets. | `PASS` | review |
| CI-11 | **Fresh maintenance C10 binding** — Capture newly executed PR-only C10 with current maintenance H/B/S, separate from historical R ZIP. | `PASS` | live_pr |

## OPS

| ID | Case and stimulus | Expected | Level |
|---|---|---|---|
| OPS-01 | **Disabled proposed rules** — Unapplied or disabled JSON cannot close enforcement. | `E_RULESET_INACTIVE` | authorized_rollout |
| OPS-02 | **Eligible reviewer prerequisite** — Only author approval or a no-major-issues comment is available. | `BLOCKED_E_REVIEW_INELIGIBLE` | authorized_rollout |
| OPS-03 | **Stale approval** — New reviewable push invalidates previously eligible approval under policy. | `E_REVIEW_INELIGIBLE` | authorized_rollout |
| OPS-04 | **Privileged settings read-back** — Read active rules and full bypass list; verify strict base, contexts, review and merge fields. | `PASS` | authorized_rollout |
| OPS-05 | **Bypass omitted from response** — Permissions cannot expose bypass actors; do not treat omitted property as []. | `BLOCKED_E_BYPASS_UNKNOWN` | authorized_rollout |
| OPS-06 | **Force push/deletion policy** — Inspect effective active rules and authorized controlled policy tests; production branch is never destructively tested without approval. | `PASS` | authorized_rollout |
| OPS-07 | **Remote tag verified** — Authorized new tag is created and peeled to A; existing wrong tag is not moved. | `PASS` | authorized_rollout |
| OPS-08 | **Tag collision** — Proposed tag already exists at a different object. | `E_TAG_CONFLICT` | authorized_rollout |
| OPS-09 | **Supplement publication verified** — Authorized external publication is retrieved and checked against independently recorded digest. | `PASS` | authorized_rollout |
| OPS-10 | **Publication missing** — Tooling and local bundle exist but no durable external publication receipt exists. | `E_PUBLICATION_MISSING` | authorized_rollout |
| OPS-11 | **Final stage conjunction** — F3 remains OPEN until all required capture/restore/settings/tag/publication states are evidenced. | `PASS` | authorized_rollout |
| OPS-12 | **Scientific exclusion** — Maintenance completion records zero new/changed theorem declarations and no promotion of open mathematical obligations. | `PASS` | authorized_rollout |

## Minimum reporting

Use the fail-closed new test runner: zero discovery, missing executable-case mappings, loading errors and unexpected skips cannot pass. Report actual method/subtest counts, distinct specified cases exercised, PASS/FAIL/SKIP/BLOCKED results and exact candidate context. Parameterized controls may make method counts differ from the 108 requirement count; do not mark an unevaluated case covered to hit a target.

Keep old suites unchanged. The maintenance tests are additional controls outside the frozen kit. Existing PR-only C10 evidence must be newly bound to the maintenance head/base/synthetic merge; the archival original R C10 bytes remain unchanged.
