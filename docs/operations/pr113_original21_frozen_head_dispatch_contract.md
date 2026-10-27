# PR #113: original 21-producer frozen-head dispatch compatibility

Status: **source-side engineering candidate, not activated or approved**.

The three unchanged protected original producer workflows (4 compiler, 9 original semantic and 8 legacy semantic shards) declare `workflow_dispatch` alongside path-filtered `push`. The reviewed 25→30 migration intentionally retains their original Git workflow bytes, so its exact 10-path activation cannot guarantee that all 21 producer jobs are naturally triggered at the final H.

The original source collector previously required `run.event == "push"`, which rejected a genuine explicit frozen-H dispatch even though the original workflow provided that interface. The corrected contract accepts only `push` or `workflow_dispatch`, and **both** must be authentic GitHub Actions results bound to the exact PR113 branch/head, expected original workflow, completed successful run and selected attempt/job/check/artifact IDs and ZIP digests. Other event types, stale H, wrong workflow and failed/partial evidence remain rejected.

For PR #113, run nonauthorizing trigger/collector/consumer rehearsals, not purported original21 acceptance. GitHub manual dispatch requires the workflow to exist on the default branch; at original base B the retained compiler workflow is absent from main, so feature-branch-only dispatch cannot work. After a separately authorized M113 registers the protected producers on main, the successor CERT may dispatch them at its frozen head, checking actual returned branch/ref, SHA, run/attempt, jobs, checks and all 4+9+8 artifacts. Path-filtered push may not trigger. Do not manufacture commits/IDs or conflate original21 with historical T/A2.

Independent R08 review and separate owner R09b workflow activation remain prerequisites. This implementation does not dispatch workflows or perform an activation.


## Successor source identity contract

At the genuine frozen Hcert run, the versioned producer consumers read `PERMANSSON_CERT_PR_NUMBER` as an **untrusted runtime lookup hint**. Set it to the actually assigned post-M113 successor PR number only after main registers the retained producer workflows. The consumer checks the exact GitHub producer event (`GITHUB_SHA`, `GITHUB_REF`, `GITHUB_REPOSITORY`), the live CERT PR head/base/branch, and the actual ordered M113 ancestry. Missing, stale, guessed or old #114 PR numbers fail. This variable is neither independent review nor authorization for mathematical acceptance.
