# PR #113: original 21-producer frozen-head dispatch compatibility

Status: **source-side engineering candidate, not activated or approved**.

The three unchanged protected original producer workflows (4 compiler, 9 original semantic and 8 legacy semantic shards) declare `workflow_dispatch` alongside path-filtered `push`. The reviewed 25→30 migration intentionally retains their original Git workflow bytes, so its exact 10-path activation cannot guarantee that all 21 producer jobs are naturally triggered at the final H.

The original source collector previously required `run.event == "push"`, which rejected a genuine explicit frozen-H dispatch even though the original workflow provided that interface. The corrected contract accepts only `push` or `workflow_dispatch`, and **both** must be authentic GitHub Actions results bound to the exact PR113 branch/head, expected original workflow, completed successful run and selected attempt/job/check/artifact IDs and ZIP digests. Other event types, stale H, wrong workflow and failed/partial evidence remain rejected.

After R10 exact-source activation, explicitly launch the three retained original workflows at the frozen H if their path filters did not trigger them; collect all 4+9+8 real producer artifacts before the 21→76 handoff. This action does not change source and does **not** authorize a mathematical claim. Use actual GitHub `run_id`, `run_attempt`, check-run and artifact records; never commit runtime IDs or invent reviewer choices.

Independent R08 review and separate owner R09b workflow activation remain prerequisites. This implementation does not dispatch workflows or perform an activation.
