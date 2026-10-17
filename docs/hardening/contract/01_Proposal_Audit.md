# Proposal audit: preservation and v0.2.0 reproduction hardening

**Date:** 17 October 2026  
**Repository:** `HMarcusWH/PermanssonLean`  
**Proposal:** `sources/Original_Proposal.txt`  
**Audited accepted commit:** `d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618`  
**Accepted tree:** `72ad841cc5b3cffc5f82979a9739b7fd03d75e15`  
**Verdict:** approve the maintenance direction, subject to the explicit engineering contracts below. This is a build specification and source audit, not an implemented PR or an activated repository policy.

## 1. Scope and overall judgment

The proposal correctly addresses the prior audit's three maintenance findings: an always-on preservation gate (F1), an equation-complete deterministic TeX check (F2), and durable history/evidence plus enforced integration rules (F3). It explicitly keeps mathematical work out of scope. That boundary should remain intact. No X1 reflection, strategy theorem, strict MA2 witness, A3 extension, application-schema upgrade, dependency update, or scientific status promotion belongs in this change.

The proposed `340 + 29 = 369` count is correct. I reconstructed the uploaded repository's Git tree from all 748 file payloads and mode bits, matched the live accepted tree, checked every historical manifest entry, and independently counted the release paths. The machine-readable exact inventory is supplied in `registries/protected_inventory_369.json`.

The proposal is stronger than a hash checklist, but it is not yet sufficiently precise about where trusted bytes come from, what object is being tested, how the exporter is isolated, how an offline restore is demonstrated, or how reviews become enforceable. Those are implementation decisions that can determine whether the new green check means what its name suggests.

References use `[P]` for the proposal, `[R#]` for fixed repository sources, `[G#]` for official documentation, and `[E#]` for executed probes. The source register is in `00_README.md`.

## 2. Evidence actually obtained

### Source identity and inventory

The supplied source ZIP has SHA-256 `e1cae51533373cd87a1a8e82ea9d94fb72c048a45c1af66c6cf03843d723017b`. Its reconstructed tree is the accepted tree above. All 340 historical path/mode/Git-blob/SHA-256 entries match. Exactly 29 accepted files are under `release/`: 27 files inside `release/v0.2.0/`, including its manifest, plus the outer ZIP and checksum. The union has 369 distinct paths. No count was inferred from the earlier chat alone. [E1]

Live GitHub still reports accepted `main` at this commit, traditional protection disabled, and an empty repository ruleset collection. Existing check-run contexts and the GitHub Actions App identity were read directly. These are observations at audit time, not authorization to modify settings. [R6–R8]

### Exporter behavior

The accepted function is `build_release.tex_document(data, revision, manuscript_hash, draft)`. It can be called in an isolated `python -I -S -B` subprocess using only the accepted `build_release.py`, accepted `verify_release.py`, and standard-library modules. The PDF dependencies are imported inside the PDF function, not needed by the TeX function. [R2, E1]

Using the original research revision `5822cdff0fc360d9e368e10ff5f7576c3141a1b3`, the SHA-256 of the original manuscript bytes, and `draft=False`, regeneration exactly produces the 71,379-byte accepted TeX. Its digest is `3524da1f1ef92cfee179917efebeb3c2786b8ad484653d2f1c8f4d8036952416`. There are ten equation records. Substituting the release commit as the renderer's `revision` produces different output. [E1]

### Git-bundle mechanics

I built a disposable Git graph with separate source, base, synthetic merge, and accepted merge commits. A bundle rooted only at `main` omitted the unreferenced synthetic commit. Adding its named ref preserved it. A full bundle imported into a genuinely empty repository and passed full strict object checking. An incremental bundle was rejected there for missing prerequisites. [E1]

Importantly, `git bundle verify` returned success for a deliberately truncated bundle whose header remained intact; the subsequent import failed. Therefore the proposal's full sequence—verify, import, object checks—is essential. Header verification is not a payload-integrity certificate. These were toy graph experiments, not restoration of the actual Permansson history. [E1, G2, G3]

### Evidence availability

Live artifact metadata for final R C10 artifact `12106535829` matches the proposal: 9,377 bytes, digest `75d61c01020f63d7f9555f10f32de9d63a09c0107536463ae549cdb85ebe9fc8`, workflow `39045919534`, source head `cdbe7ed5124781be495404122fac1de3315cb6ec`. It is reported unexpired with expiry `2026-11-16T15:51:25Z`. The bytes are not present among the seven C10 ZIPs in the accepted kit. Acquire that original publisher object as a separate archival input. A new run is not a replacement for it. [R9]

The acceptance comment was read live. Its final review link points to a no-major-issues code-review comment. The proposal's phrase “final mathematical review” is too strong for that artifact alone. Archive it under a factual name such as `final-code-review-comment.json`; retain mathematical scope information separately. [R10]

## 3. Audit of the proposed F1 design

### 3.1 Preserve the four distinct identities

The frozen core snapshot, historical protection baseline, research snapshot, and accepted release commit have different roles:

| Role | Commit |
|---|---|
| Original core provenance | `c018f79ea4ce46f4f679ad5bca254509778fc53c` |
| Historical 340-file baseline | `6191a1acbf00867042a21c8e6c4a532af43017bc` |
| Research source in the companion | `5822cdff0fc360d9e368e10ff5f7576c3141a1b3` |
| Accepted release / policy source | `d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618` |

Do not replace all of these with a variable called `baseline`. The new protection policy reads the existing inventory from the accepted release commit, checks that inventory against the accepted tree, and preserves its original 340-file meaning. It then adds the accepted 29 release files. [P §1, R1]

### 3.2 Fixed reference must mean fixed Git objects

A candidate file named `manifest.json`, a clean-looking working directory, and a recalculated checksum are not authority. Read `A:release/v0.2.0/manifest.json` from the object database, check its independently frozen digest, parse it without duplicate keys, and derive the inventory from that source. Compare candidate commit objects, not working-file bytes. Missing objects are errors, not an invitation to update the reference. [P §1]

The specification additionally disables Git replacement objects and rejects shallow/promisor/borrowed-history contexts for the relevant full-history operations. Without this, object names can be interpreted through local overlays or lazily completed from a remote, weakening the claimed reference and offline boundaries. This is hardening of the mechanism, not a new mathematical assumption. [G4]

### 3.3 Closed trees and baseline-only sets are not interchangeable

Use eight closed roots: the seven roots already closed by the accepted checker plus `release/v0.2.0`. Do not close `release/` globally; future version directories must remain possible. Do not close all of `ReverseSolver/`; its existing protected entries stay frozen but later additions must remain possible. Treat root path replacement, symlinks and gitlinks as type/mode differences rather than following them. [R1]

The 369 pins do not freeze every research module. A separate, one-time maintenance-scope acceptance test must show this PR added or changed no Lean source. Do not install that one-time restriction as an always-on rule that blocks the next legitimate research PR.

### 3.4 Trusting the checker still needs review

The proposal already recognizes that candidate-controlled code can print a false success. Preserve that warning. A GitHub Actions App binding narrows who may issue the check; it does not prove the checked workflow itself is unmodified. Changes to `.github/workflows/`, the integrity tools, archive tools, proposed rules, or policy constants are sensitive review items. Independent eligible review is required for the deployment profile, and protection-policy migration is a separate reviewed change—not a CLI `--refresh` operation. [P trust boundary, G5–G7]

## 4. Audit of the proposed F2 design

### 4.1 Correct arguments are part of the certificate

The renderer reads release-source code at `A`, but its `revision` argument remains the research source `G`. The raw manuscript digest must be calculated before JSON parsing; reserialized JSON is not the original byte identity. `draft` is false. Exact equality includes newlines and metadata as well as equations. [R2, E1]

### 4.2 The accepted exporter has a dependency closure

Loading only `build_release.py` is insufficient: it imports functions from `verify_release.py`. Materialize both accepted files, check their hashes, and load them in a fresh isolated subprocess. Do not leave the current repository or candidate `PYTHONPATH` available to satisfy `import verify_release`. A candidate module or stale `sys.modules` entry must not become the reference implementation. [R2]

Use the TeX function, not `build()`, the script entry point, or `pdf_document()`. Those larger paths write outputs and manifests or pull in unnecessary rendering dependencies. The two-module standard-library-only route was directly tested.

### 4.3 Independent check, not preservation by another name

For F2 tests, call the export comparator even when the preservation comparator would already fail. Repair candidate manifest/receipt hashes and leave equation captions unchanged in negative cases. Assert `E_TEX_MISMATCH`, not any nonzero exit. That proves F2 catches a semantic export discrepancy rather than merely relying on the newly frozen TeX hash. [P §3]

This checks faithful export, not mathematical truth or PDF visual quality. The ten equations could faithfully reproduce a false source proposition; source correctness remains separately reviewed. No PDF regeneration is required for this check.

## 5. Audit of the proposed F3 design

### 5.1 Separate acquisition, construction, and offline verification

Acquisition is networked, authorized, and read-only with respect to the repository: collect exact Git objects and raw evidence. Construction produces a new supplement from those immutable inputs. Verification starts from a new empty Git repository with networking disabled and no alternate object store. CI should consume the committed supplement, not depend on expiring Actions artifact downloads for every future PR. [P §4]

The final R C10 artifact should be captured early, before unrelated code polish or repository-setting rollout. Its expiry is a practical acquisition deadline, not evidence of a current release defect. [R9]

### 5.2 Name every historical root explicitly

The supplied registry specifies 36 named refs: four provenance roots plus source/base/synthetic/main roles for all eight milestones. Several names intentionally point to the same object; there are 26 distinct commit IDs. This does not claim to inventory all historical commits—the bundle includes their full reachable history. Build an exact object inventory from that closure. [E1, G2]

Do not use `--all` in the working repository. It may include unrelated branches or later maintenance history. Create the bundle from a disposable bare staging repository populated with exactly the approved roots, without ranges, time cutoffs, object filters or prerequisites.

### 5.3 The old bundle must not claim to contain its own future acceptance

The historical bundle ends at accepted release `A` and the named historical synthetic commits. Raw API evidence and the new offline tooling can be ordinary files alongside it. The supplement may record the tooling's pre-packaging source commit and code hashes; the maintenance PR's final head/merge/acceptance belong in a subsequent external receipt. Do not rebuild the accepted v0.2.0 ZIP to include this later receipt. [P §4]

### 5.4 Reproduction has several levels

Use explicit result labels:

- **Source restore:** exact refs, objects, parent relations and trees.
- **Artifact replay:** accepted kit hashes, full frozen verifier, package verifier and archived C10 consistency checks.
- **Fresh Lean execution:** not supplied by a source/evidence bundle; requires installed pinned Lean/mathlib and its own run.
- **Publisher authentication:** not manufactured by offline checksums or a copied JSON comment.

The archival CI should restore the accepted checkout and run the old verifier there. The other two required jobs bind the candidate's protected files and TeX to that accepted content. Report these as separate checks; do not describe an accepted-checkout replay as compilation of the new candidate.

### 5.5 Header, payload, object closure, and source binding all matter

Require bundle checksum, valid supported header, zero prerequisites, exact ref inventory, successful import, `git fsck --full --strict`, exact object inventory, exact expected commit IDs, ordered merge parents, synthetic/main tree equality, and accepted-source ancestry. A wrong ref can point to a perfectly valid commit; fsck alone will not detect that semantic mismatch. [G2–G4, E1]

Do not demand universal byte-for-byte bundle regeneration across Git versions: Git object identity and closure are the reproduction target, while the delivered bundle's own byte digest is immutable. The existing portable ZIP retains its already accepted byte identity.

## 6. CI and enforcement corrections

### 6.1 Keep exactly the three new required names

Implement independent jobs named `frozen-source-preservation`, `release-export-integrity`, and `archive-reproducibility`, on every `pull_request` targeting main and every push to main. Do not put path filters, docs-only skip logic, `continue-on-error`, or permissive dependencies around them. Manual dispatch is diagnostic only. Preserve ordinary merge commits; merge-queue support is not introduced by this proposal. [P §5, G5]

The actual existing required contexts are job names, not workflow titles: `build`, `research`, `executable-verification`, and both OS-qualified Application contract names. The legacy `research-release` check remains path-filtered and should not be globally required. New job names must be observed from real PR checks before the ruleset is activated. [R8, G5]

### 6.2 Activation has a real reviewer prerequisite

A no-major-issues comment does not equal an `APPROVED` review. Pull request authors cannot approve their own requests. The supplied sources do not establish which independent account is eligible to approve these PRs. Make reviewer eligibility a deployment prerequisite. Do not silently reduce the count to zero or add an always-bypass actor to make the ruleset usable. [R10, G6]

The proposed JSON is deliberately disabled and has no bypass actors. Activation requires explicit authorization, an eligible reviewer, verified check contexts, and a privileged read-back of effective settings. A read response omitting bypass information because of insufficient permission is **unknown**, not proof of an empty bypass list. [G7]

### 6.3 Test discovery must fail closed

Do not rely on an unrestricted `unittest discover` invocation as the only evidence that the intended suite ran. The new runner must reject empty discovery, loading failures, missing required case-to-method mappings and unexpected skips, and emit actual executed method/subtest counts. The 108-case acceptance matrix also contains genuine-PR and operational cases; unit mocks do not complete those live obligations. This is an explicit build-contract requirement, not a claim that the new suites have been written.

### 6.4 Split completion states

Track F1 implemented versus enforced; F2 implemented versus enforced; F3 history captured, offline restore verified, settings active, remote tag verified, and external supplement published. The overall maintenance programme is not fully closed while the separately authorized operational steps remain open. Conversely, an accepted code PR may accurately report those remaining steps without pretending the code failed. [P §§5,8]

## 7. Build sequencing decision

Keep one coordinated maintenance programme and the proposed three checks, but stage work in this order:

1. Acquire final R evidence immediately; pin the reference inputs.
2. Build and adversarially test canonical-object preservation and isolated TeX comparison.
3. Build the supplement tooling and exact historical bundle; demonstrate empty, network-disabled restoration.
4. Wire all three always-on jobs, run old verification through the restored accepted tree, and obtain exact-head/synthetic-merge review and fresh PR-only C10 evidence.
5. Merge only under author approval. Apply rules/tag/publication separately, read them back, and issue the external completion receipt.

A split into multiple PRs is optional project management, not necessary mathematics. Never mark F3 complete because an early code PR contains a proposed settings file. Never delay capturing the expiring R artifact until all administration is finished.

## 8. What was not established in this audit

No real full-history supplement was created here; the source ZIP has no original Git object database. No actual R publisher ZIP was downloaded here. No new Lean build, real maintenance synthetic-merge CI, ruleset activation, remote tag, or external archive publication was performed. The included schemas, workflow and deployment JSON are specifications/templates. Executed evidence is limited to the source/inventory/exporter and disposable Git probes described above.

The proposal is ready to become an implementation after the contracts in `02_Implementation_Spec.md` are adopted. Its scientific exclusions remain unchanged.
