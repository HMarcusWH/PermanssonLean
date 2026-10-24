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
