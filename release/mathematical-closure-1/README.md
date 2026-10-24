# Mathematical-closure release candidate

**DRAFT — NOT ACCEPTED — NOT PUBLISHED.** For full 45/11 scope the
versioned state machine is `POSTMERGE_PRESEAL_READY` ->
`CANDIDATE_SEAL_BUILT` -> independently authenticated
`POSTSEAL_ARCHIVE_VERIFIED` ->
`FULL_MATHEMATICAL_CLOSURE_RELEASE_READY`. Full seal mode emits only
a candidate ZIP; no source-controlled JSON or local ZIP replay authorizes
publication. Canonical manuscript source lives under `research_papers/mathematical_closure/`. The versioned `manifest.json` is a frozen *claim candidate*, not a future GitHub merge or review receipt. No generated PDF or archive is committed. See build.py and verify_release.py for draft tooling; release approval requires independent source-bound proof, CI and manuscript/visual review.

## Exact merged-M reproduction

The postmerge pre-seal gate accepts `--reproduction-zip` plus
`--reproduction-ids` only as a pair. The ZIP must be the **original**
GitHub Actions `pr113-clean-paper-rebuild-draft` archive from a real successful
`clean-paper-rebuild` job at merged **M** on `main`. The ID JSON has
`run_id`, `run_attempt`, `job_id`, `check_run_id`, and `artifact_id`.
`final_closure_reproduction_auth.py` independently rechecks GitHub metadata,
the authoritative artifact digest, and identical actual PDFs, manifests,
archives, logs and page PNGs from two source roots. Without this genuine
receipt the full pre-seal gate remains closed. Even a valid clean-build receipt
is **not** mathematical review, scholarly approval or release authorization.

## Post-seal release authorization (not yet available)

`--postseal-zip` and `--postseal-ids` are paired inputs to the strict
full-release verifier. `final_closure_postseal_auth.py` insists on a real
successful exact-M `pr113-postseal-replay.yml` workflow_dispatch, a successful
`postseal-archive-replay` producing check and the GitHub-authoritative
`pr113-complete-postseal-candidate` artifact digest. It re-verifies the exact
retained candidate ZIP and sidecar, complete archive members, and original
unreviewed postseal receipt before recognizing `COMPLETE_ARCHIVE_REPLAY`.
**The new workflow is NOT installed in the protected workflow inventory and
must not be added without independent security authorization.** Until that
reviewed producer exists the final release is necessarily blocked; local
postseal reports are not substitutes.
