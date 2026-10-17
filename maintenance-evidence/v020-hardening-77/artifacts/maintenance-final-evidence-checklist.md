# Final maintenance receipt: explicit evidence whitelist

This is an assembly checklist, not an acceptance claim. Never recursively copy
or inventory the surrounding `artifacts/` directory: it also contains unrelated
private and historical projects. Include only individually approved receipt
files and explicitly named current CI capture directories.

## Unit-ledger assembler

`populate_maintenance_unit_ledger.py` uses only the standard library. It reads
explicit JSON files or `artifact.zip!member.json` sources without extraction.
It requires full expected H/B/S, PR number and a genuine downloaded PR context,
plus all six successful suite reports from the same hardening workflow run and
attempt. It verifies all 108 IDs/levels, all 87 mapped unit cases, executed
methods/subtests, clean execution, Python 3.13, and zero skips/errors/failures.

Example shape, with actual paths and full source identities supplied at capture:

```text
python -B populate_maintenance_unit_ledger.py --template maintenance-acceptance-ledger-template.json --context CURRENT_ARCHIVE.zip!context.json --head H_FULL_SHA --base B_FULL_SHA --synthetic S_FULL_SHA --pr 77 --report reference=CURRENT_PRESERVATION.zip!reference-tests.json --report preservation=CURRENT_PRESERVATION.zip!preservation-tests.json --report context=CURRENT_PRESERVATION.zip!context-tests.json --report workflow=CURRENT_PRESERVATION.zip!workflow-tests.json --report tex=CURRENT_EXPORT.zip!tex-tests.json --report archive=CURRENT_ARCHIVE.zip!archive-tests.json --output NEW_EXTERNAL_UNIT_LEDGER.json
```

The output must be a new file under this external artifacts directory. The
script populates **87 unit cases only**. It preserves nine nonunit technical
cases as `PENDING_EVIDENCE` and all twelve OPS cases as `DEFERRED_BY_USER`.
It does not authenticate copied publisher JSON, infer current GitHub state,
establish merge acceptance or supply a counted approval. The operator must
independently identify the reviewed current H/B/S and original artifact/API
captures. An old matching-looking report cannot be relabeled for a new head.

## Required final files or explicit capture members

1. **Source identity record:** exact repository, PR number, H, B, genuine S,
   ordered parents `[B,H]`, tested tree, and eventual M with its parents/tree.
   Keep each PR's source tuple separate. Capture PR metadata and the real event
   context; do not fill unavailable identities speculatively.
2. **Original current Actions captures:** run/job/check-run metadata, attempts,
   publisher App identity, conclusions and raw artifact ZIPs with observed API
   digest/size/provenance. Require the intended existing and three new check
   contexts; retain Windows portability evidence separately.
3. **Hardening unit reports:** `reference-tests.json`,
   `preservation-tests.json`, `context-tests.json`, `workflow-tests.json`,
   `tex-tests.json`, `archive-tests.json`, and their matching `context.json`.
4. **Production hardening reports:** `preservation.json`, `tex-export.json`
   and actual Linux `archive-replay.json`; preserve the original containers and
   bind these to current candidate context.
5. **Maintenance source-scope evidence:** complete Lean-tree/root comparison,
   zero accepted release-path changes, all 369 protected entries and inventory
   digest, plus actual full pinned proof/executable/application workflow results.
6. **Fresh maintenance C10 evidence:** actual PR-only artifact, publisher/run
   metadata, current maintenance H/B/S binding and independent content check.
   Preserve historical R separately; a new run cannot replace its original ZIP.
7. **Historical integration evidence:** ARCH-14 original R bytes and acquisition
   identity; ARCH-23 actual empty/network-disabled bundle restoration, strict
   object/ref/parent/tree checks, accepted-A verifier/package replay, 29 legacy
   tests, R consistency and post-replay hashes. Source restore and artifact
   replay do not themselves establish fresh Lean execution or publisher identity.
8. **Explicit nonunit acceptance records:** ARCH-14/23; CI-01/02/04/05/08/11
   actual live PR source/job/head/base-change evidence; CI-10 current workflow
   credential/permission review. Unit mocks do not populate these nine cases.
9. **Current review packet:** exact-head code review, thread captures/resolutions,
   `hardening-codex-review-resolutions.md`, `hardening-review-record.md`, and only
   the individually reviewed regression/report files referenced by that packet.
   Agent source review and a resolved comment are not a GitHub APPROVED review.
10. **Packaging receipt:** current tooling T and closure hashes, supplement
    manifest/bundle/object/ref inventories, publication-candidate ZIP/checksum,
    and independent exact member/payload/mode/timestamp verification.
11. **Ledger outputs:** unchanged-provenance template, this reviewed assembler
    and its digest, populated unit ledger, separately filled nonunit evidence,
    and final exact-source acceptance record with open/deferred stages intact.

Reviewer and external publication destination remain undetermined. Settings,
remote tags and external publication remain deferred by the user. No OPS case
is completed by a repository push or a local/publication-candidate archive.
Old `37544d2f...` docs CI and earlier PR #77 reports remain explicitly old-head
evidence; current-head CI is not PASS until its own captures are verified.
