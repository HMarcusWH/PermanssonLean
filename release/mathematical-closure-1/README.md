# Mathematical-closure release candidate

**DRAFT — NOT ACCEPTED — NOT PUBLISHED.** For full 45/11 scope the
versioned state machine is `POSTMERGE_PRESEAL_READY` ->
`CANDIDATE_SEAL_BUILT` -> independently authenticated
`POSTSEAL_ARCHIVE_VERIFIED` ->
`FULL_MATHEMATICAL_CLOSURE_RELEASE_READY`. Full seal mode emits only
a candidate ZIP; no source-controlled JSON or local ZIP replay authorizes
publication. Canonical manuscript source lives under `research_papers/mathematical_closure/`. The versioned `manifest.json` is a frozen *claim candidate*, not a future GitHub merge or review receipt. No generated PDF or archive is committed. See build.py and verify_release.py for draft tooling; release approval requires independent source-bound proof, CI and manuscript/visual review.
