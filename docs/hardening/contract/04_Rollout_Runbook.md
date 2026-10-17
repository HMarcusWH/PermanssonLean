# Build and rollout runbook

**Programme:** `PERMANSSON-HARDENING-1`  
**Status:** instructions for the implementing agent/operator, not an execution receipt.  
**Reference:** `02_Implementation_Spec.md` is normative. The shell/Python examples below are command patterns to implement or execute after preflight; they are not claims that the real archive or deployment already exists.

**Repository amendment:** archival acceptance uses the supported candidate-bound offline launcher, and K4 requires an explicit actual-candidate Lean-scope report with independent H/B/S binding. The byte-identical supplied runbook is preserved in [supplied/04_Rollout_Runbook.md](supplied/04_Rollout_Runbook.md).

## 1. Decisions fixed by this contract

Build one coordinated maintenance change with three independent check contexts. Use the accepted release commit A as the immutable reference; retain the original research-source argument G for TeX. Preserve 369 fixed files and the eight closed roots. Build a new archival supplement without changing the accepted release kit. Restore actual historical Git objects from that supplement in an empty network-isolated environment. Keep mathematical work out of scope.

Use these fixed inputs:

```text
A = d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618
G = 5822cdff0fc360d9e368e10ff5f7576c3141a1b3
A tree = 72ad841cc5b3cffc5f82979a9739b7fd03d75e15
R synthetic = c70362b97ae7d0828a569fa15e194f9861b22b46
R publisher artifact = 12106535829
R publisher run = 39045919534
R publisher SHA-256 = 75d61c01020f63d7f9555f10f32de9d63a09c0107536463ae549cdb85ebe9fc8
```

Only three matters remain genuinely external choices: the eligible independent reviewer, the separately authorized durable publication destination, and approval to activate settings/create a remote tag. Record their owners and status. Their absence does not justify inventing an identity, reducing protection, or claiming F3 closed.

## 2. K0 — source preflight and original-evidence acquisition

Read the original proposal, audit, specification, inventories and test plan. Query live `main`, open PRs, current rulesets and final PR #76 evidence. A changed live base does not silently replace A. Any later source compatibility issue requires explicit analysis, while preservation still refers to A.

Work in a clean full clone with the actual object database. A downloaded source ZIP is adequate for source inspection but not historical ancestry validation. Do not synthesize commits with accepted SHAs or initialize an unrelated Git history over the ZIP.

Capture original R C10 bytes early. The last live metadata observation reports expiry **16 November 2026, 15:51:25 UTC**; reacquire metadata during implementation. Use authorized read access to the exact artifact endpoint or an authenticated artifact downloader. Preserve the downloaded ZIP verbatim. Stream-hash it and require the recorded 9,377-byte size and published digest before parsing. Capture current PR metadata, final code-review comment, acceptance comment, review submissions/threads, and final run/job metadata/logs. Pagination must finish.

Store originals and a factual acquisition index in a new directory outside the accepted kit. Record only metadata actually observed. Do not save access tokens, cookies, authorization headers, or expiring signed redirect URLs. Never substitute an older lane C10 ZIP or a regenerated numerical report for the original R artifact.

**K0 completion:** references and source tree verified; acquisition either has original bytes and capture records or is explicitly BLOCKED. Metadata alone is not captured-artifact completion.

## 3. K1 — shared policy, Git primitives and fixtures

Build `verification/integrity/policy.py`, `git_objects.py`, `inventory.py`, `reports.py`, `ci_context.py` and private test fixture helpers. Keep package initializers inert.

Establish canonical object access before higher-level features. Disable Git replacement objects and lazy fetching. Remove inherited Git-directory/configuration redirection. Reject unsupported object-store dependencies where the contract requires full closure. Parse `ls-tree -z`; preserve types, modes and raw path boundaries. Read payloads through bounded batch plumbing, not a filesystem walk of a CRLF checkout.

Derive the historical inventory from **A's** manifest, whose digest is independently pinned, and cross-check each entry. Derive the 29 accepted release files from A. Verify the supplied 369-entry registry agrees, but never treat a mutable candidate copy as authority.

Fixture repositories are real small Git repositories with privately supplied fixture policies. The production command line has no alternate reference/policy, refresh, skip or acceptance override. Unit fixtures must not require reconstructing the actual accepted history.

**K1 completion:** REF and basic PRES tests pass; exact error codes and canonical-object behavior demonstrated. No CI enforcement or F3 completion yet.

## 4. K2 — preservation and TeX comparators

Implement the F1 comparator and CLI. Add all type/content/mode/deletion/rename/addition controls and legitimate-development positive cases. Report sensitive changes to the new verification policy/workflows separately; the tool cannot authenticate its own reviewer.

Implement the isolated F2 reference importer. Materialize the accepted builder, accepted verifier helper and raw manuscript into a trusted temporary directory. Invoke `tex_document` with G, the hash of the raw manuscript bytes, and final mode. Require the reference output's 71,379-byte size and expected SHA-256; then compare it with the candidate Git TeX blob.

Do not load candidate helpers from `PYTHONPATH`, the current directory or inherited `sys.modules`. Exercise a shadow-module marker and prove it was not executed. Use byte output; do not normalize whitespace, Unicode or newlines.

Run equation mutation tests by calling F2 directly. Repaired candidate hashes and unchanged captions must not save a changed equation. The intended rejection is `E_TEX_MISMATCH`, not an earlier preservation failure.

One-time local command pattern, after implementation:

```bash
C="$(git rev-parse HEAD)"
python -B -m verification.integrity.preservation \
  --repo . --candidate "$C" --report /absolute/scratch/preservation.json
python -B -m verification.integrity.tex_export \
  --repo . --candidate "$C" --report /absolute/scratch/export.json
python -B -m verification.integrity.run_tests --suite reference --report /absolute/scratch/reference-tests.json
python -B -m verification.integrity.run_tests --suite preservation --report /absolute/scratch/preservation-tests.json
python -B -m verification.integrity.run_tests --suite tex --report /absolute/scratch/tex-tests.json
```

Record one actual Windows LF/CRLF compatibility run as well as Linux Git-plumbing mode/link tests. The existing application Windows job does not automatically execute new integrity tests. Keep any additional portability-only check distinct from the three required gate names; do not turn them into ambiguous matrix contexts.

**K2 completion:** F1/F2 code and independent adversaries pass. Accepted release outputs remain byte-identical. These are implemented checks, not yet enforced branch rules.

## 5. K3 — historical bundle and offline replay tooling

### 5.1 Preparation is the only networked Git phase

Read the exact input identities from `registries/archive_commit_registry.json`, backed by A's seven receipts and the external R acceptance. Verify source/head/base/merge fields. Acquire immutable objects from the authorized repository before offline testing; current branch tips and mutable pull refs are not the source of truth.

Use a new bare staging repository. Populate its object database from the acquired real history without borrowing object alternates, then create the 36 archive refs. In implementation, pass subprocess arguments as lists. Example construction shape:

```python
refs = approved_registry['refs']  # records use the exact 'ref' and 'commit' keys
# Require 36 unique approved names and complete 40-hex commit IDs before this loop.
for entry in refs:
    run_git(staging, 'update-ref', entry['ref'], entry['commit'])
run_git(staging, 'bundle', 'create', '--version=2', output_bundle,
        *[entry['ref'] for entry in refs])
```

The delivered registry uses these exact `ref`/`commit` keys. No `--all`, date cutoffs, exclusions, incremental ranges or filters. Staging operations do not change remote refs or the operator's active worktree.

Before bundle creation, validate every synthetic/main parent pair and matching tree. Enumerate the complete selected object closure and record its objects separately from the 26 distinct input commits. A bundle may contain thousands of ancestors and blobs; 26 is not the full object count.

### 5.2 Real restore, not an in-place verification

The verifier performs the following logical commands in a new empty repository. It validates inventory and size bounds before passing untrusted bytes into Git:

```text
git init --bare RESTORED.git
git -C RESTORED.git bundle verify /absolute/history.bundle
git -C RESTORED.git -c protocol.allow=never -c protocol.file.allow=always \
    fetch --no-tags /absolute/history.bundle REF1:REF1 ... REF36:REF36
git -C RESTORED.git fsck --full --strict
git -C RESTORED.git show-ref
```

Validate the bundle header's exact refs and zero prerequisite list before import. After import, independently compare all refs, every object's ID/type/size/content hash, merge parents, accepted ancestry and tree identities. `git bundle verify` alone does not detect every truncated payload; the audit fixture demonstrated that import is a necessary additional gate.

Create a local worktree of A from this restored database, without contacting a remote. The worktree may refer to that restored database; it must not refer to the CI checkout or an external object cache. Run the exact frozen release verifier, package verifier and old 29-method release suite there, with dependencies already installed. Independently check original R C10 content using the actual R source tuple, not an earlier lane tuple.

Rehash all delivered supplemental inputs and accepted artifacts afterward. A replay log must label its target **A**, while candidate F1/F2 reports identify the new candidate C. Neither label is a substitute for the other.

### 5.3 Network isolation adapter

The Linux adapter prepares dependencies first, records the parent's network-namespace identity, then launches a new network namespace. It must drop back to the nonroot runner UID/GID and clear supplementary groups/capabilities before invoking any Python code that parses the candidate supplement. Use known absolute executables and argument vectors, not shell interpolation of metadata.

The launch pattern to validate on the supported CI VM is:

```text
sudo -n /usr/bin/unshare --net -- \
  /usr/bin/setpriv --reuid=<runner-uid> --regid=<runner-gid> \
  --clear-groups --bounding-set=-all --inh-caps=-all --ambient-caps=-all \
  --no-new-privs \
  <absolute-python> -B <absolute-offline-worker> <validated-arguments>
```

This is an adapter design, **not a successful namespace run recorded by this audit**. Capture child/parent namespace identities, UID/GID, absence of outward routes and a denied outward socket attempt. Sanitize proxies, credentials and inherited descriptors. A timeout alone is not a sufficient denial result. If the platform cannot enforce the isolation profile, return BLOCKED/nonzero and stop; do not rerun the test online and report offline success.

The supported ordinary acceptance entry point installs that profile before invoking the internal verifier:

```text
python -B -m verification.archive.offline_smoke --repo . --candidate FULL_SHA --supplement DIRECTORY --scratch NEW_EMPTY_DIRECTORY --report /scratch/archive-reproducibility.json
```

For CI/K4, both `--repo` and `--candidate` are mandatory; FULL_SHA is the complete current genuine synthetic S. The parent report binds the candidate C before the child restores accepted A. Standalone artifact replay without candidate arguments cannot discharge K4. `verification.archive.verify_bundle` is a namespace-child/internal interface; bare use outside the enforced isolation profile must return BLOCKED/nonzero and cannot replace this launcher.

Network isolation is not a general sandbox against a malicious maintainer who controls the workflow. The new checker and workflow remain review-sensitive. The purpose is to prove the archival replay cannot acquire missing history or dependencies from the network.

### 5.4 Avoid the package/hash cycle

Finish and commit the tooling at a clean maintenance commit T before packaging. Snapshot its required Python/schema/guide closure as ordinary files alongside the historical bundle. Record exact code hashes and T. Generate and test the supplement in a new external output directory, then commit it in a later maintenance commit. The bundle remains rooted at A and the eight historical synthetics, not T or the current maintenance head.

If tooling changes, regenerate the tooling snapshot and supplement manifest before acceptance. Do not use stale copied tools merely because their own internal checksums agree. Final head/merge/approval evidence is an external post-integration receipt.

**K3 completion:** original historical supplement successfully restored offline; accurate boundary report, exact payload inventory, source closure and final R capture verified. External publication/settings can still be OPEN.

## 6. K4 — new workflow and genuine-merge acceptance

Use `templates/research-integrity.yml` only after its referenced production modules and tests exist. All three jobs must execute on every PR targeting main and every push to main, even when no release path changes. No paths filters, docs-only conditions, `continue-on-error` or dependency chain that turns a failed prerequisite into a skipped success.

Each job verifies event context. On a PR, the actual checkout must be the genuine S with ordered parents `[B,H]`. A manual workflow on H is useful diagnostic evidence but does not replace the PR event. Existing Lean, Research Lean, executable verification and both application OS jobs continue unchanged. Fresh PR-only C10 evidence for the maintenance H/B/S is separate from historical R evidence.

Before merging this maintenance PR, run the shipped one-time scope checker from a clean isolated checkout of the actual current genuine synthetic S:

```text
python -B -m verification.integrity.maintenance_scope --repo . --candidate FULL_SHA --report /scratch/maintenance-scope.json
```

Replace FULL_SHA with the complete current S. Require exit 0, report PASS, check `maintenance-Lean-scope`, fixed A/tree, current checked S/tree and `details.completed_stages` containing `fixed_authority` and `complete_Lean_scope_comparison`. Require all four complete scopes (`PermanssonLean/`, `PermanssonResearch/`, `PermanssonLean.lean`, `PermanssonResearch.lean`) unchanged, including unprotected additions, edits and deletions. Preserve the report's `details.acceptance_only=true` and `details.permanent_preservation_policy=false` labels.

Independently capture the current GitHub PR's H/B/S, verify S's ordered parents `[B,H]`, and bind that receipt to the report's checked SHA/tree. A locally produced report stays labeled local; it does not itself authenticate a GitHub event. Retain both records in the K4 packet. Missing, stale, mismatched or failing evidence blocks acceptance; rerun after any head or base change. PRES-23's unit fixtures test checker behavior and cannot replace this actual-candidate acceptance condition. Do not install the one-time restriction as a permanent workflow job or required context; it adds no new acceptance case ID or level.

Observe the actual new contexts and publisher App before proposing activation:

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

The observed publisher is GitHub Actions App `15368`; reread its identity. Do not require the old path-filtered `research-release` globally.

The review packet must include the zero-release-path diff, one-time no-Lean-change comparison, full 369-file comparison, exact TeX regeneration, 108-case coverage disposition with actual test methods/subtests counted separately, full old/new CI, current head/base/synthetic identities, and no unresolved substantive findings.

After any source update, refresh exact-head review and synthetic CI. After base movement, verify the new actual synthetic tree; do not merely reuse a prior green run with matching-looking files. Merge only with explicit author approval. After merge, read M and prove its ordered parents and tree equal the accepted S conditions, then record the post-merge runs.

**K4 completion:** code accepted and integrated, with operational deployment status still stated separately.

## 7. K5 — separately authorized settings, tag and publication

### 7.1 Bootstrap without locking out valid development

Before enforcing the proposed rules, resolve a real independent reviewer with sufficient review eligibility. An author cannot self-approve, and a bot's COMMENTED/no-major-issues entry is not a counted APPROVED review. The reviewer must meet the last-push policy as well. Do not silently set required reviews to zero or add an always-bypass actor.

Wait until all required contexts have actually been observed on the genuine PR and are available for the selected ruleset. Do not enable a required context that can never run. The proposed JSON is intentionally `enforcement: disabled`; applying it unchanged cannot close F3. It is a review artifact, not a performed settings change.

After explicit administrative authorization, apply the reviewed payload with active enforcement and then read it back. Include individual ruleset and effective main-branch rules, publisher IDs, strict current-base checks, resolved-conversation requirement, eligible-review fields, allowed merge methods and full bypass actors/modes. Read with sufficient permissions to expose bypass data; omitted is UNKNOWN, not an empty list.

Keep merge commits permitted and the only intended integration method. Do not add a linear-history requirement, squash/rebase-only policy, auto-merge or merge queue incidentally. Verify repository-level merge options agree with the rule. Record actual administrative bypass behavior; a ruleset name is not evidence of enforcement.

### 7.2 Remote tag

Only after separate authorization and collision checking, create a new annotated tag such as `permansson-v0.2.0-research` pointing to A. Read its remote tag object and peeled commit back. Record signing status exactly as observed. Do not move or overwrite an existing tag to satisfy this contract.

The original source bundle already preserves named commit identities without this later tag. Keep the later tag object/publication receipt external rather than rebuilding the old accepted source/evidence bundle merely to include its own later rollout history.

### 7.3 Durable external publication

Publish a separately named archival supplement to the approved destination, retaining an independently accessible checksum/receipt. Retrieve the published supplement into a clean destination and verify its digest and restore report. A local file, proposed destination URL or expiring Actions upload alone does not demonstrate durable publication.

No publication provider is selected by this specification because the user has not authorized one. Record that deployment choice explicitly. Do not disclose credentials or publish unrelated branch history through an indiscriminate `--all` bundle.

**K5 completion:** real active enforcement read back, tag verified, supplement publication retrieved/hashed, and external final receipt records exactly what changed. If any step is unavailable, list it OPEN or BLOCKED without closing F3.

## 8. Final handoff to the research programme

Return the exact maintenance H/B/S/M, all job/run attempts, new production file map, reported test methods and subtests, protected inventory digest, supplement digest, original R digest, actual review disposition, and activated-versus-pending operations.

The theorem-change count is **zero**. Carry every scientific limit forward unchanged. Only after maintenance acceptance should a separately scoped X1 numerical-reflection PR consume the preserved original canonical interfaces. This hardening contract supplies no X1 numerical theorem, unrestricted strategy theorem, strict MA2 witness or stronger A3/D2 conclusion.
