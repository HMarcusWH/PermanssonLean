# v0.2.0 archival supplement and offline reproduction

The accepted release is `d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618`, tree
`72ad841cc5b3cffc5f82979a9739b7fd03d75e15`. Its existing 29 release files
and original ZIP remain unchanged. A supplement stores history and later
captures separately; it introduces no theorem or scientific acceptance.

## Constructing supplement-1

Acquire the original R C10 ZIP and final captures before packaging. Acquisition
is the only online evidence step. The fixed original ZIP has 9,377 bytes and
SHA-256 `75d61c01020f63d7f9555f10f32de9d63a09c0107536463ae549cdb85ebe9fc8`.
Its artifact ID is `12106535829`, run `39045919534`. A new workflow run cannot
replace those historical bytes. Never put credentials or signed redirect URLs
in the supplement.

Retain every page behind assembled review submissions and threads. Connector
thread responses expose no pagination state, so their full saved response and
exact PR request are cross-checked against exhaustive REST inline-comment pages
and the captured PR comment count. Do not invent a completion flag. Each final
job needs its own nonempty, source-bound log capture; an unopened run-level ZIP
cannot substitute for those logs.

Commit clean tooling at T first. Then, from the repository root:

```text
python -B -m verification.archive.create_bundle --repo . --evidence CAPTURE_DIR --output NEW_EXTERNAL_DIRECTORY
```

The builder derives 36 named refs / 26 distinct input commits from the accepted
seven source receipts and the fixed final R identities. The separate registry
ZIP mentioned in the supplied audit was not attached locally: the delivered
registry explicitly labels this derivation, without claiming byte identity to
the unavailable registry. Its namespace is `refs/archive/permansson/v0.2.0/`.

Only those exact refs enter a disposable staging repository. The full bundle
contains their reachable history, including all eight synthetic merges, without
prerequisites. The full object inventory records canonical payload hashes; it
does not confuse 26 input commit identities with the much larger closure.

The historical bundle excludes T and all subsequent maintenance commits.
Tooling from T is a content-hashed file snapshot alongside the bundle. After
verification, commit supplement files separately. Later tooling changes require
updating that snapshot; stale copies are rejected. Record eventual maintenance
H/B/S/M, review, rollout and publication in an external acceptance receipt.

The snapshot includes this canonical guide. Candidate-bound replay compares the
complete code and guide closure at T and current checkout C, then checks the
executing code and delivered copies. `OFFLINE_REPRODUCTION.md` must exactly
match the guide snapshot. These comparisons use committed Git content for the
guide, so checkout newline conversion does not alter its source identity.

## Supported offline profile

Install Python 3.13, Git and `pypdf==6.10.0` before the isolation boundary.
ReportLab, matplotlib, Lean and mathlib are not prerequisites for artifact replay.
Run as a nonroot Linux user with the reviewed `/usr/bin/sudo`, `unshare` and
`setpriv` adapter available:

```text
python -B -m verification.archive.offline_smoke --repo . --candidate FULL_SHA --supplement SUPPLEMENT_DIRECTORY --scratch NEW_EMPTY_DIRECTORY --report REPORT_OUTSIDE_SOURCE.json
```

The adapter creates a fresh network namespace and drops to the original UID/GID
with no supplementary groups or capabilities and no-new-privileges before
parsing candidate inputs. It records different parent/child namespaces, no
external route and a conclusively denied outward socket. Unavailable isolation
returns BLOCKED/nonzero. There is no online fallback. Windows may run portable
Git fixture tests, but cannot claim this Linux isolation acceptance.

For a standalone supplement, change into its `tooling/` directory and run:

```text
python -B -m verification.archive.offline_smoke --supplement .. --scratch ABSOLUTE_NEW_EMPTY_DIRECTORY --report ABSOLUTE_REPORT.json
```

This requires no prior Git checkout. After successful restoration its local
context is captured from the actual restored A and explicitly labeled
`accepted_artifact_replay`. Candidate-context CI acceptance still requires the
real maintenance Git checkout and genuine event. A standalone replay report
cannot replace current candidate CI.

Standalone replay compares the delivered code and guide copies by content; it
does not discover a surrounding Git repository or authenticate the publisher.
Both `--repo` and `--candidate` are required together for candidate-bound use.

## What the archival gate proves

The gate validates all delivered hashes and inventories; rejects unsafe paths,
symlinks, extra files and unbounded input; checks a prerequisite-free v2 header;
imports into an empty object database; runs full strict Git object checking;
and compares exact refs, full objects, ordered merge parents, matching synthetic
and main trees, ancestry and accepted tree.

It restores accepted A using canonical normal blobs, rechecks all 369 pins and
the complete deterministic TeX export, then runs the unchanged final release
verifier, package checker with `--verify`, all 29 old release tests and original
R C10 arithmetic/generated-source/transcript consistency validation. It rehashes
accepted artifacts and all delivered files afterward.

Distinguish the following results:

- Source restoration: historical objects, refs, parent relations and trees.
- Artifact replay: existing kit and captured evidence rechecked at A.
- Fresh Lean execution: not performed by this replay; requires the pinned proof
  environment and separate current candidate workflow evidence.
- Publisher authentication: not created by an offline checksum, copied JSON,
  or code-review comment. The R digest is compared with the separately fixed
  publisher identity. The archived final review remains a code-review artifact.

`git bundle verify` alone is insufficient: an intact header can outlive a
truncated pack. Successful import, object checking and source binding are also
mandatory. Different Git versions need not regenerate identical pack bytes;
the delivered bundle digest is fixed, while independent reconstruction must
match its exact object/ref closure.

## Completion boundaries

Prepared code, actual offline restoration, active repository enforcement,
verified remote tag and retrieved external publication are distinct stages.
Proposed disabled rules, local supplements and expiring Actions uploads do not
close operational F3. No setting, remote ref or publication is changed by these
tools. Those operations require their separately authorized rollout.
