# Independent agent source-review record

**Current integration disposition:** the final follow-up closes the reported source findings for identified working bytes; new commit, packaging, genuine CI and operational evidence remain separate requirements.

Repository: `HMarcusWH/PermanssonLean`  
Scope: maintenance source, artifact integrity and review of the hardening contract. This record is an agent review, **not a GitHub `APPROVED` review**, mathematical peer-review certificate or fresh Lean execution.

## Reviewed identities and disposition

| Pull request | Exact reviewed head | Disposition |
|---|---|---|
| #77 | `e314ccc2b3587065425a0357874ad5580cce841d` | Source review PASS; no actionable findings at this head |
| #77, subsequent local packaging delta | `bd88afd584e4bb829458f47d3e6a4fb5ebaa09b6` | Delta review PASS; no actionable findings; fresh integration evidence still required |
| #78 | `2ff920d6ab470cd49f6f392f23855676ac1f8db3` | Source review PASS; no actionable findings at this head |

The immutable accepted reference remains `d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618`, tree `72ad841cc5b3cffc5f82979a9739b7fd03d75e15` (A).

## PR #77: checks actually performed

The full source/artifact review was performed at `cff7d50bb9750fadd60e3d8fa148c806e86a4d62`. Its synthetic merge `a3c67852083c15d2587e403e67093f2928a19ab1` was independently resolved from Git: ordered parents were `[A, head]` and its tree equaled the head tree.

- All **369 protected files** passed the production preservation comparator: 6,680,695 bytes; inventory SHA-256 `8b4e5e235781c625c61f60b700f2d19f172e8bd9131a6b62edbda0907e77f160`.
- The one-time maintenance Lean-scope check passed. There were **zero Lean-source/root changes and zero accepted release-path changes**.
- The isolated exporter reproduced **71,379 bytes and ten equation records**, SHA-256 `3524da1f1ef92cfee179917efebeb3c2786b8ad484653d2f1c8f4d8036952416`, using the original research revision.
- The actual supplement manifest, executing tooling and captured evidence validated. All **32 tooling files** had identical canonical Git blobs at source T (`62757969628519e339bd71420d3a06ad1cd22d29`), the reviewed head and the delivered snapshot.
- Bundle header and registry matched **36 refs / 26 input commits**. The parsed inventory contained **8,202 objects / 27,391,135 uncompressed bytes**, included all 26 inputs and excluded T and the maintenance head. Header/inventory checks here are distinct from a full bundle import and offline replay.
- The original R capture validated: **25 captured files**, ZIP size **9,377 bytes**, SHA-256 `75d61c01020f63d7f9555f10f32de9d63a09c0107536463ae549cdb85ebe9fc8`.

Delivered manifest SHA-256: `9b068f586964a62454a034904ecfcd4525d19212b6c9f24a4ad0be971c363525`. Bundle: 6,633,053 bytes, SHA-256 `56c401a24130fd37231d667fdbad3f5578587bb6a1c6d3c406698bd5a966537f`.

The subsequent exact-head review at `e314ccc2b3587065425a0357874ad5580cce841d` confirmed that its sole delta was four lines in the Windows portability workflow: set repository-local `core.autocrlf=true` to match checkout normalization, then explicitly check failure. No checker, policy, tooling snapshot, supplement, Lean or release content changed; the source review therefore carried forward. Earlier green CI was not relabeled as evidence for this new head.

## Findings addressed during review

Review probes or source inspection identified the following gaps, subsequently addressed in the reviewed source:

- Required workflow commands could be replaced by `echo` or have failures swallowed with `|| true`.
- A partial requirement registry could omit acceptance cases without rejection.
- PR-acceptance contexts did not reject a foreign repository/accepted reference; test reports lacked candidate/run binding.
- Nested archive metadata could contradict delivered hashes, dependencies or reproduction claims.
- Final evidence validation did not require the complete workflow/job/log captures.
- Supplement-root symlinks, lexical `..` scratch overlap and builder output boundaries required stricter validation.
- Same-host HTTP downgrade redirects could retain authorization; direct production replay lacked the Python-profile check.
- Internal worker reports did not match their advertised check-report schema; implicit standalone context could select an unrelated Git ancestor.
- Canonical tree traversal required independent tree-payload verification as well as commit/blob verification.

Negative probes confirmed the corrected workflow, mapping, foreign-context and scratch-overlap rejections. The overlap regression rejected before creating scratch inside the supplement. The final source was also checked for the remaining fixes.

## PR #78: checks actually performed

Head `2ff920d6ab470cd49f6f392f23855676ac1f8db3`, tree `eb6c44cfb92a68f543dfd2829b14a9ff090192e2`, had sole parent A and added exactly **eight files under `docs/hardening/`**: five contract documents and three registries.

All eight modes and Git blobs matched the reviewed #77 head. Independently derived reference data confirmed that the 369-entry inventory equaled actual A, the archive registry equaled trusted accepted receipts plus fixed R identities, and authority pins equaled the production pins. There were **no implementation, Lean or release changes**.

## PR #77: subsequent packaging delta

Reviewed local head `bd88afd584e4bb829458f47d3e6a4fb5ebaa09b6` against `e314ccc2b3587065425a0357874ad5580cce841d`. The exact delta contained only three additions under `archival/v0.2.0/publication-candidate/` (ZIP, checksum and README), plus eight lines in `docs/V020_HARDENING.md`. It changed no checker, policy, trusted snapshot, mathematical source, closed-root member, accepted release or existing supplement payload.

The ZIP was independently read and verified: **7,399,088 bytes**, SHA-256 `fd39be3f3383de914456a249e072092d47af93e59ea56d216488147b58e72dc8`. The sidecar exactly matched that digest and filename. Its **65 members** were sorted, unique, safe regular files with Unix mode 0644, fixed `2026-10-17 00:00:00` timestamps and an empty archive comment. Every decompressed payload equaled the existing supplement file; the included manifest retained SHA-256 `9b068f586964a62454a034904ecfcd4525d19212b6c9f24a4ad0be971c363525`.

The added documentation accurately distinguishes a repository publication candidate from external publication. Reviewer and publication destination remain deferred; settings, remote archival tags and external publication are not claimed complete. Current maintenance acceptance remains outside the historical supplement and publication ZIP. **Delta review PASS; no actionable findings.** This does not transfer earlier CI results to this new head or its future refreshed base.

## Limits and remaining acceptance

This record does not certify live GitHub CI, a new head/base/synthetic tuple, fresh maintenance C10 execution, or a Linux namespace/full historical replay. Those require their own exact-source execution records. No theorem declaration was added or changed; scientific assumptions and open boundaries remain unchanged.

Any refresh after merging #78 needs a further exact-head delta review and genuine new synthetic-merge CI. No eventual merge SHA is certified here.

Eligible independent GitHub reviewer and durable publication destination remain undetermined. Administrative enforcement, remote tag creation and external publication/read-back remain pending and separately authorized. Agent source-review PASS does not close those obligations or supply the required counted approval.

## Follow-up: required workflow and context fixes, 17 October 2026

This follow-up supersedes the earlier broad source-review clearance for integration purposes. The earlier entries remain records of their stated inspections; later adversarial review found additional workflow and archival gaps. The current review target is **uncommitted working source based on `bd88afd584e4bb829458f47d3e6a4fb5ebaa09b6`**, identified by the file digests below. It is not a certificate for a future tooling commit, PR head or synthetic merge.

### Workflow/context findings now independently verified fixed

The required workflow and optional Windows portability workflow no longer expose `workflow_dispatch`. The generic context function retains diagnostic dispatch handling, while the required context CLI rejects events other than a genuine main-targeting PR merge or main push. The actual required workflow passes its reviewed-profile gate: **4,760 canonical-LF bytes**, SHA-256 `70cd7e8569beb995981be210369f57c34460289e6a5890c54153683a26939093`.

An independent read-only reprobe exercised **24 candidate mutations**, all rejected with `E_WORKFLOW_CONTRACT`. These included previously accepted extra executable steps in ordinary sequence, spaced-key, block, folded and flow forms; local, unversioned and container actions; PR types restricted to closed/labeled events; Python-version drift and alternate checkout ref; root/job permission grants, quoted/tagged keys, shell backgrounding and environment overrides; YAML directives/document markers; and a restored dispatch trigger. The profile now pins the complete reviewed canonical workflow after structural diagnostics. Changing that profile requires a reviewed policy-code update, with no production override. This restriction does not prohibit ordinary additive Lean research or future release directories.

An independent execution ran **11 test methods with zero failures or skips** in 15.964 seconds: all eight workflow tests, required-CLI dispatch rejection, genuine-PR positive binding and push/after-SHA positive/rejection controls. Fixture tests do not replace genuine GitHub execution at the refreshed H/B/S.

### Archival findings and current completion limit

The acquisition implementation now crosschecks normalized reviews against captured REST pages, normalized threads against the original connector response, and thread comments against exhaustive REST inline-comment pages. It requires per-job logs with an exact job endpoint and timestamped UTF-8 text; unparsed run-ZIP existence cannot replace those logs. Repaired acquisition-index and outer-manifest mutation tests were run for these corrections. Actual updated acquisition has 28 payload files and retains the original R ZIP digest unchanged.

Further independent repaired-hash probes subsequently exposed three additional archive conditions still **OPEN at the time of this record update**: omission of comment timestamp fields from both normalized and connector captures; impossible calendar timestamps in raw job logs; and erasure of both normalized and REST submission lists while inline comments still identify their review submissions. These require fixes and intended-stage regressions before overall source-review clearance. The source checker must crossbind those review IDs and require valid timestamp values. The workflow/context portion is verified; this record does not close the archival findings or certify a newly packaged supplement.

### Review boundary

The checker and expected workflow digest are candidate-owned code. A contributor able to change both can also weaken the check; the pin is a fail-closed reviewed-profile contract, **not independent authentication of its own implementation**. Sensitive changes still need eligible independent review and effective repository enforcement. An agent report is not a counted GitHub APPROVED review.

Reviewer and durable external publication destination remain undetermined. Settings, remote tagging and external publication remain deferred by the user's latest instruction. No operational requirement is marked complete from this review. No mathematical theorem, assumption or scientific status changes are reviewed or promoted here.

| Working source file | SHA-256 of inspected bytes |
|---|---|
| `.github/workflows/research-integrity.yml` | `70cd7e8569beb995981be210369f57c34460289e6a5890c54153683a26939093` |
| `.github/workflows/research-integrity-portability.yml` | `23c0b16125590d19c017a191b1b4a0b41ea8b15063fc13b246352901f64ad43e` |
| `verification/integrity/workflow_contract.py` | `d82b6ee6b8c97dcb7b0565e9fc635c7da8432bd3a0273c7373b19173bcaf8a6f` |
| `verification/integrity/ci_context.py` | `5ce429464b2bd437c1313e810dc11d58d123e30df8735fc95907620eb13179fe` |
| `verification/integrity/tests/test_workflow.py` | `bb8110866bcd473d576cf8e53b8854e33258ab48dc82574770d4241a39c3d1e5` |
| `verification/integrity/tests/test_context.py` | `10ba495a5dab584114155ca87717bb5ae6f92b142ccdf2f796b3840c9f05ba86` |

## Final archival follow-up: independently reproduced repaired-hash rejections

This section supersedes the OPEN archival disposition in the preceding follow-up. The source target remains **working source based on `562a22210e9e1cb23b19a6ebddacbc6bdc2bd6d0`**, with exact inspected bytes recorded below. All four independent attacks were constructed outside the source tree; source code was not edited by this reviewer.

The actual updated capture is a positive control: **28 payload files** pass, including the original R ZIP at 9,377 bytes and unchanged SHA-256 `75d61c01020f63d7f9555f10f32de9d63a09c0107536463ae549cdb85ebe9fc8`. The connector thread source truthfully records that pagination was not exposed. Thread/comment completeness is checked against exhausted REST inline-comment pages and the captured PR count; no GraphQL completeness flag is invented.

Each adversary repaired **both** acquisition-index hashes and the complete outer supplement manifest/detached checksum. `validate_manifest` returned PASS before `validate_evidence` reached the intended semantic rejection:

| Independently reproduced mutation | Observed result |
|---|---|
| Remove both comment timestamps from every comment in both normalized threads and the retained connector source | `E_CAPTURE_ID`: thread comment timestamp missing or different from REST capture |
| Erase both normalized review submissions and the retained REST review page while leaving captured inline-comment review IDs intact | `E_CAPTURE_ID`: wrong PR/review identity or duplicate ID |
| Replace a job log with UTF-8 text beginning `2026-99-99T99:99:99Z` | `E_CAPTURE_ID`: invalid calendar timestamp |
| Mark the retained connector result `isError: true` while keeping its thread data | `E_CAPTURE_ID`: result missing or not an explicit successful result |

**The reported workflow/context and archival source findings are now closed for these inspected working bytes.** This is scoped source-review clearance for preparing the tooling commit and rebuilding the supplement. The source author's full final regression report, new tooling/supplement commit identities, refreshed H/B/S and genuine GitHub CI remain separately required. Previous CI is not transferred to a new head. This review does not certify the next ZIP before its independent inventory/payload check or a new Linux offline restore before it executes.

| Inspected source file | SHA-256 |
|---|---|
| `verification/archive/acquire_evidence.py` | `c520c7f603a6393e4d37a97349f21987fc5adb56f7e12b9276d03880d24d10a2` |
| `verification/archive/tests/test_archive.py` | `d71117a52d005b8e0909e0f6fad295c87ce4f9c68b27e6ae4608db4679ac8632` |

Acquisition-index SHA-256 at this inspection: `41f0ff8617f5a8f52ac8bc1a742634fa29ba6c3c194ccd8f901f5e99b0d89e4a`.

The candidate-owned checker and its expected workflow pin remain review-sensitive and do not authenticate their own implementation. A timestamped log is a consistency input, not independently authenticated execution. No fresh Lean execution, mathematical peer review, theorem change, scientific promotion, active repository enforcement, remote tag or durable external publication is certified by this source review. Reviewer and publication destination remain undetermined; operational settings/tag/publication steps remain deferred by the user. The 108-case registry remains a requirement ledger, not a blanket completion claim.

## Exact committed packaging review: `049d2620317afd10f8a584254d768f36af1d4979`

The follow-up source fixes are committed at tooling T `562a22210e9e1cb23b19a6ebddacbc6bdc2bd6d0`; rebuilt packaging is committed at H `049d2620317afd10f8a584254d768f36af1d4979`. A read-only independent review at this exact clean H completed in 76.266 seconds. Its reproducible review script and execution report are external artifacts at `hardening-pr77/review_049_packaging.py` and `hardening-pr77/review-049-packaging.json`. **Exact-H source/packaging review PASS; no actionable findings.** This section supersedes the earlier limitation that the rebuilt ZIP had not yet been independently checked.

The new manifest SHA-256 is `d64c69508a89d677318c2d5a67a43e8ed2393911c5b22fdaee7cebf7d69b353c`. All **68 supplement files** equal their canonical regular-file Git blobs at H. All **32 tooling files** have identical Git blobs at T and H, and identical bytes in the executing source and delivered tooling snapshot. The fixed authority policy is unchanged between T and H. The actual **28-file capture** passes the strengthened validator; the original R ZIP retains its 9,377-byte size and pinned SHA-256 `75d61c01020f63d7f9555f10f32de9d63a09c0107536463ae549cdb85ebe9fc8`.

The historical bundle remains byte-identical to the previously reviewed bundle: **6,633,053 bytes**, SHA-256 `56c401a24130fd37231d667fdbad3f5578587bb6a1c6d3c406698bd5a966537f`. Its header matches the exact accepted-derived **36 refs / 26 distinct input commits**. The delivered object inventory was independently recomputed from those actual historical Git roots and matched **8,202 objects / 27,391,135 uncompressed bytes**. All input commits are present; T and H are excluded. Ordered merge parents, synthetic/main tree equality and accepted ancestry bindings passed. This packaging review did not repeat a new empty-database import or Linux offline execution; those remain separate execution records.

The production preservation check at H passed all **369 protected files / 6,680,695 bytes**, retaining inventory SHA-256 `8b4e5e235781c625c61f60b700f2d19f172e8bd9131a6b62edbda0907e77f160`. The one-time maintenance Lean-scope check passed. Direct accepted-A versus H tree comparison found **zero changes under either Lean tree, either Lean root, all release paths or application paths**. Isolated TeX regeneration again matched **71,379 bytes / ten equation records**, SHA-256 `3524da1f1ef92cfee179917efebeb3c2786b8ad484653d2f1c8f4d8036952416`, using research revision `5822cdff0fc360d9e368e10ff5f7576c3141a1b3`.

The publication candidate ZIP independently matched **7,436,361 bytes**, SHA-256 `4c95cc07f915612e4fd1270d75ed046449e7a2c33bbea02d5236e0058f16fe79`, and its exact detached checksum. Its **68 members** are sorted, unique, safe, unencrypted regular files with Unix mode 0644, fixed `2026-10-17 00:00:00` timestamps and an empty ZIP comment. Every decompressed payload equals the committed H inner supplement file. The README accurately retains pending external publication, remote tag, eligible reviewer and enforcement status.

The source-author regression execution is recorded separately in `hardening-pr77/archive-capture-regressions-final.json`: **two methods / 32 subtests, zero failures, errors or skips**, including the actual 28-file positive and repaired-inner-index/outer-manifest adversaries. Its recorded source digests match T and H. This is distinct from the independent four-attack reprobe described above.

No genuine refreshed maintenance H/B/S CI, eventual merge M, fresh maintenance C10 artifact or new Linux offline attestation is certified by this packaging review. Refreshing after prerequisite #78 still needs exact-head delta review and fresh genuine synthetic-merge CI. No GitHub APPROVED review, fresh Lean execution, mathematical promotion, settings activation, remote tag or external publication is claimed. The candidate-owned checker trust boundary and deferred operational obligations remain unchanged.

## Exact committed delta/package review: `cc114ee60ff8749b3bb64bb24a8d5e76d2120af9`

The reviewed clean head H is `cc114ee60ff8749b3bb64bb24a8d5e76d2120af9`, with sole parent tooling T `a83d57a707afc91861fc5fec853d01f576ba0334`; T has sole parent the previously cleared `049d2620317afd10f8a584254d768f36af1d4979`. The exact delta contains **seven modified files only**: the existing PRES23 test, its delivered tooling copy, the supplement manifest and checksum, and the publication ZIP, checksum and README. No new production checker, authority, workflow, registry or mathematical change is present. **Exact-H delta/package review PASS; no actionable findings.** The external reproducible script is `hardening-pr77/review_cc114_packaging.py`; execution report `hardening-pr77/review-cc114.json` records 19.984 seconds.

PRES23 now exercises **12 mutation subtests**: edit/delete both Lean root files and a module in each Lean tree, module additions in both trees, and each root addition against an explicit private root-absent baseline. The permanent fixture inventory remains unchanged. Crucially, deletion of the unprotected research root and research module each passes that permanent comparator before the one-time helper rejects with `E_MAINTENANCE_SCOPE`; frozen-file deletion coverage cannot substitute for this evidence. The unchanged existing method passed the author's targeted run in 27.434 seconds and an independent reviewer run in 27.946 seconds, with no failures/errors/skips. The committed, executing and delivered test source all retain independently inspected SHA-256 `7d177fb0876a78503c347bfea660421211cb18abf739bcc3ec3e47af1c081bac`. There is no new test method or requirement mapping. These targeted executions were reused based on identical source bytes, not rerun or represented as fresh GitHub CI in this packaging pass.

All **68 supplement files** equal their canonical regular Git blobs at H; all **32 tooling files** match T, H, executing source and the delivered snapshot. The manifest validates with SHA-256 `019f816a67d492e65dfb3c3873d2f8a353b08b7706a73489251190a42572710a`; the actual **28-file capture** passes the strengthened evidence validator and the original R artifact remains unchanged. Bundle, refs and object-inventory Git blobs are identical to the previously cleared H. Header/inventory measurements remain **36 refs / 26 input commits / 8,202 objects / 27,391,135 uncompressed bytes**, and bundle SHA-256 remains `56c401a24130fd37231d667fdbad3f5578587bb6a1c6d3c406698bd5a966537f`. The earlier independent full-closure/binding review is reused from identical inputs; no new historical import or offline run is claimed here.

The publication ZIP independently matches **7,437,026 bytes**, SHA-256 `da51255e8f47c3c3e16ef28fd41611eb532f370887722654dc88e01ac7dd97d1`, and the exact detached sidecar. All **68 members** are sorted, unique, safe, unencrypted regular Unix-mode-0644 files at the fixed `2026-10-17 00:00:00` timestamp; ZIP comment is empty. Every decompressed payload equals the committed H inner file. The README delta changes only package measurements and retains deferred operational boundaries.

The one-time maintenance scope was checked at this exact H, and accepted-A versus H Git trees still show **zero Lean-tree/root, release-path or application-path changes**. Permanent preservation and isolated TeX production code, trusted references and candidate inputs are identical to the previous cleared H. Accordingly its **369-file preservation** and **71,379-byte / ten-equation exact TeX** results are carried forward by identical-input reasoning; they were not freshly executed in this delta review. No change to accepted pins, schemas, mathematics or scientific status is introduced.

Fresh genuine maintenance CI at the eventual refreshed H/B/S, new maintenance C10, main merge M and Linux offline attestation remain separately recorded execution obligations. This agent review is not a GitHub APPROVED review or a statement that all 108 requirements have executed. Eligible reviewer and durable publication destination remain undetermined; enforcement, remote tagging and external publication remain deferred.

## Additional PR #78 findings: actual-candidate scope and supported archive invocation

Two later P2 threads are now fixed in committed tooling and amended documentation: `PRRT_kwDOUkBtPs6tjkqu` (bind the maintenance-only Lean check to the PR candidate) and `PRRT_kwDOUkBtPs6tjkqx` (align archive invocation with its normative CLI contract). The integration agent reports that both were resolved at 19:42:44 UTC on 2026-10-17 after pushing the fixes. This paragraph attributes live resolution status to that agent; it is not a separate thread-status API capture.

The independently inspected production tooling is T `cc0d29a38f3b27f4fdb760292790e677e4738d8d`, pushed by the integration agent as `evidence/v020-hardening-scope-tooling`. Its new `verification.integrity.maintenance_scope` public command validates fixed accepted A and tree plus candidate ancestry, then invokes the existing canonical full-union scope comparator for both complete Lean trees and root files. Git entries include content identity, mode and type as well as path membership, including actual directory/empty-tree entries. No baseline override, permanent-policy change, new workflow job, required context or mathematical modification is introduced. Its report explicitly labels acceptance-only scope and gives the checked canonical candidate/tree. A local run remains local; separate independently captured current GitHub H/B/S/tree/ordered-parent evidence is required for K4.

The independent reviewer executed the public-command control: **one method / two subtests PASS in 10.343 seconds**, with no failures/errors/skips. The unchanged candidate passed; a legitimate unprotected research-module addition passed the original permanent comparator but failed this one-time command with `E_MAINTENANCE_SCOPE`. Review found an initial mismatch between the new check name and its advertised Check.v1 schema. The schema enum was corrected and the control extended to check format/schema identity, required fields and check/status membership. Those final small schema/test additions were independently read without an unnecessary second fixture run. **The scoped code/schema finding is closed for the committed identities below.**

The integration agent's complete fail-closed preservation report, `hardening-preservation-scope-cli.json`, separately records **26 methods / 19 subtests PASS**, all 23 PRES requirements covered, zero failures/errors/skips and `execution_tracked_clean=true`. Its context identifies local T `cc0d29a...`, tree `61e77b4053252d212f460ad3554f528b027edf93`; runtime is Python 3.12.14 and Git 2.45.2.windows.1. SHA-256 is `e9a3da297a814b08d7e72d88296fc3939208c1b3db900adc065c52676c4d2a7b`. The integration agent reported 293.177 seconds elapsed; the JSON has no elapsed field. This complete suite was inspected as execution evidence, not independently rerun by this reviewer. **It does not discharge the still-pending actual final-S scope command and independent current-source receipt.**

| Committed tooling file at T | Git blob | SHA-256 |
|---|---|---|
| `verification/integrity/maintenance_scope.py` | `fa7f59ca34da6c2de7929a6d594f8579769f4f3c` | `fb55ab26b16ce02e154c0c349c9c319614f81713b16c5e9be403ab3c8d8b1411` |
| `verification/integrity/tests/test_preservation.py` | `2922409e07929a38f9558dec3c56c6666d93d2e6` | `ca9f1ff7be4ead7d43089cf97e1104b068bf8de7c92065b3e5f0ee32cc912a38` |
| `verification/integrity/schemas/check-report.schema.json` | `ebdd54844099d0d2b852237a0b0e34ced3cdfcd9` | `f071aaebf6092081e99be315ec632954f8d64b493d5dfee19a044b36ef3eb5a6` |
| `verification/integrity/test_coverage.json` | `617b710a1cefe4addeadff1219da27ec819d7fcc` | `a079dd160a4d01b640dd386b4e63fff28784d1bb9c966605892504f21f58e6b1` |

The amended documentation is committed at `ed8309843eedbd6cfe56b5e543c99285e28cead5`. The integration agent reports its current tuple as base A and synthetic `4403ec593fe3178495b6633c9221ccd0e49bc166`; its genuine fresh CI is separate evidence. The independent staged-source review confirmed that `offline_smoke --repo ... --candidate FULL_SHA` is the supported candidate-bound acceptance launcher, whereas bare `verify_bundle` is an internal enforced-namespace interface. The K4 command invokes the shipped one-time CLI on actual current S before merge, requires `details.completed_stages` and acceptance-only labels, joins to independently current H/B/S with ordered parents `[B,H]` and tree(S), and repeats after any source/base change. PRES-23 fixtures cannot substitute. No case ID or level was added or changed.

All five pristine supplied documents independently byte-match their Downloads originals. Active 01/directive remain unchanged; amended active 02/03/04 retain byte-identical originals under `supplied/` with `-text` attributes. Their original blobs are respectively `8d0379cc65a9eb056a06673a5b82147dca0468e5`, `38e9edc01043a9f912c2a652912dfc2ea1a9a570`, and `ea30c552ef47a02aa1873a259d96fb09c4781021`. The README accurately declares two unchanged active originals and three amended documents. The complete 108-case level inventory remains **87 unit / 2 integration / 6 live PR / 1 review / 12 authorized rollout**. The 4,760-byte approved workflow template and its SHA-256 `70cd7e8569beb995981be210369f57c34460289e6a5890c54153683a26939093` remain unchanged.

The external ledger now names T's exact registry and the amended/pristine contract identities, while retaining **96 PENDING_EVIDENCE / 12 DEFERRED_BY_USER**. A separate actual-candidate K4 scope condition remains PENDING outside the 108 cases. Locally prepared package H `3f2791d23b08d0dd157303d6c265c3dad036a349` was not yet PR #77's head at this update; this section does not certify that package, final genuine H/B/S CI, final-S scope execution, merge M, fresh Lean execution or any mathematical promotion. Reviewer and publication destination remain undetermined; settings, remote archival tags and external publication remain deferred. The checker remains candidate-owned and review-sensitive; an agent source review or resolved thread supplies no counted GitHub APPROVED review or independent publisher authentication.

### External actual-S execution helper reviewed before use

The external receipt-only helper `run_actual_maintenance_acceptance.py`, SHA-256 `75c09b260563077bd8263e617ce7a22741a091106c0e4015872d1e02793f700d`, was independently read and syntax-parsed after small review fixes. It requires canonical checkout HEAD=S, a clean checkout before and after the public command, canonical ordered S parents `[B,H]`, exact module bytes modulo checkout CRLF conversion, and a separately captured current tuple's CI context/tree. It checks independent literal accepted-A/tree/repository pins against production imports and both reports. It preserves command exit, scope-report hash, module blob/hash, CI ZIP hash and stdout/stderr hashes; it requires all four scope paths, completed comparison stages and acceptance-only labels. Report and receipt destinations must resolve outside the candidate checkout, preventing receipt writing from invalidating its own clean-after claim.

Helper source review is clear for the planned explicit external receipt paths. It was **not executed on final S during this review** and supplies no final acceptance by itself. The caller must establish that the downloaded context and publisher metadata still describe current H/B/S; copied JSON and checksums do not authenticate that publisher. Source/import trust still depends on the separately reviewed clean candidate and tooling identities. The helper reads explicit inputs only and is not permission to inventory or copy unrelated content under `artifacts/`.

## One-time acceptance implementation and local package: `3f2791d23b08d0dd157303d6c265c3dad036a349`

Local clean H `3f2791d23b08d0dd157303d6c265c3dad036a349` packages source T `cc0d29a38f3b27f4fdb760292790e677e4738d8d`. **Exact-H delta/package review PASS; no actionable findings**, completed in 22.125 seconds. The external reproducible adapter is `hardening-pr77/review_next_packaging.py`; report `hardening-pr77/review-3f279.json` has SHA-256 `53f4eb16086e566c68f8f1e8ae331eff33d9b10d5c17b3aa502ac5386259ac97`. This is a local packaging head, not yet a final integrated or CI-accepted PR identity.

Exactly **14 paths** differ from the prior cleared `cc114ee60ff8749b3bb64bb24a8d5e76d2120af9`: four source/report-contract files (`maintenance_scope.py`, the existing preservation test, coverage mapping and check-report schema), their four delivered tooling copies, `docs/V020_HARDENING.md`, and five manifest/publication measurement files. No permanent workflow, authority, pin, theorem, accepted Lean/release/application schema or mathematical status changes. The schema extension adds the explicitly separate `maintenance-Lean-scope` check name; it does not add this one-time condition to permanent jobs.

The standalone command validates candidate ancestry against fixed A and its tree, compares both complete Lean trees and both roots, and reports exact candidate/tree plus `acceptance_only=true` and `permanent_preservation_policy=false`. The package review executed its callback at H and obtained PASS for tree `0a8ebcb83bf40e2b01e5f50f878dc54f9edd393c`, with no differences. That local result explicitly requires an external join to genuine current PR H/B/S; it does not manufacture a GitHub event. The updated documentation requires a report from the actual synthetic candidate before integration. **That actual final-S CLI receipt remains a later acceptance obligation.**

Independent source/control/schema review confirmed these exact bytes, carried into T, H, executing source and the supplement:

| File | SHA-256 |
|---|---|
| `verification/integrity/maintenance_scope.py` | `fb55ab26b16ce02e154c0c349c9c319614f81713b16c5e9be403ab3c8d8b1411` |
| `verification/integrity/tests/test_preservation.py` | `ca9f1ff7be4ead7d43089cf97e1104b068bf8de7c92065b3e5f0ee32cc912a38` |
| `verification/integrity/schemas/check-report.schema.json` | `f071aaebf6092081e99be315ec632954f8d64b493d5dfee19a044b36ef3eb5a6` |

The independently executed new CLI method passed both positive/negative subtests. The source-author fail-closed full preservation-suite record `hardening-preservation-scope-cli.json` reports **26 methods / 19 subtests**, zero failures/errors/skips and tracked execution clean at code T, in 293.177 seconds. Its context accurately states local execution at T, not PR acceptance at this packaging H. Those tests are carried forward through identical reviewed code bytes; this packaging pass did not rerun them.

All **69 inner files** equal canonical regular-file H blobs. All **33 tooling files** match T, H, executing source and the delivered snapshot. The validated manifest has SHA-256 `d6a6cc21510534f05f1006600bd47c6091c47d5228c01e6536b401d256f54a9f`. The actual **28 historical capture files** validate and retain identical Git objects, as do bundle, refs and full object inventory. Bundle SHA-256 remains `56c401a24130fd37231d667fdbad3f5578587bb6a1c6d3c406698bd5a966537f`, with **36 refs / 26 inputs / 8,202 objects / 27,391,135 uncompressed bytes**. Historical full-closure/binding review and permanent preservation/TeX results are reused only from identical relevant algorithms, references and candidate inputs. No fresh full import, TeX regeneration or offline execution is claimed by this local packaging review.

The new publication ZIP is **7,438,442 bytes**, SHA-256 `a103a54501e89b014e32f0a954845e6e500bb833cac03e2ffc1320b037e75020`; exact sidecar and all **69** decompressed payloads match the committed H supplement. Members are sorted, unique, safe, unencrypted regular Unix-mode-0644 files with fixed `2026-10-17 00:00:00` timestamps; ZIP comment is empty. Declared member sizes were checked before decompression. Source remained clean throughout.

The separately captured nine green checks at `cc114ee...` remain valid **pre-base-change baseline** evidence only. They are not transferred to this new source/package or its future integrated base. Incoming prerequisite documentation still needs its final exact-head delta review; the eventual new synthetic needs the one-time CLI receipt and fresh nine-check/current C10/offline evidence. No GitHub APPROVED review, final integration, OPS completion, mathematical promotion, remote tag or external publication is certified here.

## Integrated documentation delta: `abccf9d7ce389fffe5637ea0ff0acd5718d9058f`

**Exact-head integration delta review PASS; no actionable findings.** Reviewed H `abccf9d7ce389fffe5637ea0ff0acd5718d9058f` has tree `965cc4973324439d46ccd8d610875c6940d7c6ab` and ordered parents `[3f2791d23b08d0dd157303d6c265c3dad036a349, 37c0cb8f2fbe7934639127e5f8b6d64a01e6950f]`. The second parent is merged prerequisite base B. Exactly **11** added/modified regular-mode-0644 files differ from the previously reviewed package head; all are under `docs/hardening/`. The complete resulting documentation subtree equals B's canonical Git subtree, including active 02/03/04 and their preserved supplied originals.

The amended specification/runbook correctly use candidate-bound `offline_smoke` as the ordinary enforced launcher; bare `verify_bundle` is internal/namespace-child and must block outside its enforced profile. K4 now separately requires the actual current S's standalone maintenance-scope report and an independent H/B/S/tree join; fixture tests cannot discharge it. Active PRES23 explicitly covers unprotected additions, edits and deletions, while permanent future research remains permitted. The unavailable original probes/templates remain explicitly distinguished from later independent records.

All archival/package Git blobs are identical to reviewed `3f2791d...`. All **33 tooling files** equal source T `cc0d29a38f3b27f4fdb760292790e677e4738d8d`, H and executing bytes. The **69-file** manifest and **28-file** historical capture validate unchanged. Whole-scope fixed-A candidate comparison passes at H, and accepted Lean/root, release, application, paper/provenance, protected verification and toolchain/manifest paths remain unchanged. Full ZIP and historical closure reviews are reused solely from identical canonical package inputs; no fresh proof or offline run is claimed by this delta check.

Reproducible external script: `hardening-pr77/review_abccf_delta.py`; report: `hardening-pr77/review-abccf-delta.json`. The clean rerun with a writable workspace temporary directory completed in **16.140 seconds**, including explicit temporary Git-config cleanup. An earlier successful comparison emitted a Windows sandbox temporary-directory cleanup warning; that wrapper issue was corrected before this recorded clean run. No repository source was modified by the reviewer.

Fresh genuine merge candidate S `76eeb466805f229ef9fb7cd216a0d5d45c09b225` is independently observed through GitHub with ordered parents `[B,H]` and the same checked tree. Its new workflow/artifact capture is in progress under `hardening-pr77-final-acceptance/`; the previous cc114 green capture remains a separate baseline. Actual-S one-time CLI receipt, final current CI/C10/Codex disposition and eventual M remain separate acceptance evidence. This delta review supplies no counted GitHub approval or operational rollout completion.

### Exact package/source-object review: H171c954 (2026-10-17)

Independent package verification passed at H `171c954c4733d2c8eaaac3ad90e60e4d1d4637c3`, with source T `507ff2461762a248b6a5f90dc966d11627c4b1b9`, in 89.593 seconds. This closes the package consistency review following the three later source findings; the source fixes have separate peer-review/test records and require fresh current-head CI.

The verifier rechecked all 369 canonical preservation entries, the one-time complete Lean scope, all 70 regular inner payloads, all 34 canonical T/H/executing code-and-guide source entries, all 28 captured evidence files, and the publication candidate ZIP. It required the explicit `canonical_T_C_and_executing_code` binding and identical delivered guide/instructions. The outer ZIP has 7,446,882 bytes, 70 sorted fixed-timestamp regular 0644 members, and SHA-256 `d67531969705ca39b41d25e91180dccec2c491aa3df776e876140b7777f43eca`. Manifest SHA-256 is `e53fe5f13ee270c425f7171c4006402fa73556970bbfe6a7018fb3c9fb1563de`.

The historical bundle remains byte-identical (`56c401a24130fd37231d667fdbad3f5578587bb6a1c6d3c406698bd5a966537f`), with the same 36 refs, 26 input commits and 8,202-object inventory. Reuse of the previous complete historical closure/import review is based on identical bundle/registry/object inputs; this review did not rerun a fresh historical import, Linux network isolation or Lean. No Lean/release/frozen-scope bytes changed.

Evidence: `hardening-pr77/review-171c954.json`. This is an agent package review, not a GitHub APPROVED review, mathematical peer-review certificate, current-H CI acceptance, settings activation, tag creation or external publication. The new H/B/S CI capture is separate under `hardening-pr77-repaired-acceptance/`; older head captures remain scoped to their recorded identities. Reviewer and durable publication destination remain deferred.

### Exact package/source-object review: H92e451 (2026-10-17)

The later H171c review identified three real enforcement/resource gaps and one ancestry claim citing a different commit. The ancestry claim did not reproduce on actual H171c/S7743; the preserved proof records both real ancestry exit codes, ordered parents and the successful bound archive worker. The three real gaps were fixed and independently reviewed in source T `71cc34fa0bc4b639c05d2ec5f39f0b88afd56388`: required legacy contexts bind genuine events, publication ZIP/sidecar are checked against canonical candidate objects, and delivered inventory traversal/hashing has fixed resource budgets. Agent code review is not a GitHub APPROVED review.

Exact package H `92e45179a5e3ecbe1b2bcadc4da54a0d1657f501` passed independent verification in 82.938 seconds: all 71 canonical inner/ZIP payloads, 35 T/H/executing code-and-guide entries, all 369 preservation entries, complete one-time Lean scope, the committed publication gate, and all 19 canonical workflow profiles covering five legacy contexts. Manifest SHA-256 is `8fc56980228519e96e927a212b3c49afbebd5007ef8f1fa3086b17241a3da18d`; ZIP size is 7,465,148 bytes and SHA-256 is `f6f119cadb1a3ebe09f9010510476bab2e75194ededde922eb99a8891652eca4`. No Lean/release/frozen-scope change was found.

This package contains a legitimate history-bundle repack: SHA-256 changed from `56c401a24130fd37231d667fdbad3f5578587bb6a1c6d3c406698bd5a966537f` to `f49203e5a7f2189565c24509bd56652318ab383dfcda36ee756b78332b1e5792` (6,639,932 bytes). The named-ref and object-inventory Git blobs remain identical. The initial identity-reuse check stopped on this byte change; no failed check was relabeled as PASS. A separate fresh local empty-database import then passed in 33.219 seconds, including strict full fsck, exact 8,202-object database/reachable closure, 36 refs, 26 input commits, fixed accepted registry and ordered parent/tree/ancestry bindings. The final package review requires that new report and records the repack explicitly. This local run did not enforce network isolation, replay accepted artifacts or execute Lean.

Evidence: `hardening-pr77/review-92e451.json`, `local-restore-92e451.json`, `restore_repacked_bundle.py`, and the source-review records. Fresh genuine H92/B/S CI, all 11 publisher artifact ZIPs, current review disposition and actual-S acceptance remain pending in the separate `hardening-pr77-finalized-acceptance/` capture. Historical H171c has nine green checks and captured C10 evidence but is not final integration acceptance. Main merge, effective settings, tag creation, external publication and reviewer eligibility retain their separate requirements.
