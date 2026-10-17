# PR77 pre-base-change CI capture

This external record preserves the green baseline before any dependency/base
change. It does not mark final integration or the whole hardening programme
complete.

At `2026-10-17T19:34:02Z`, the captured GitHub API reported all **nine checks
completed successfully**, published by GitHub Actions App **15368**, for:

- H: `cc114ee60ff8749b3bb64bb24a8d5e76d2120af9`
- B: `d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618`
- Genuine synthetic S: `86ff0d8ce3482935d2ff09ee24c260d309f069d1`
- Checked tree: `bc2af29f32f6b89b5ea927ea04a6579422e4e6eb`

`final-pr77.json` captured the matching H/B/S before the root agent was told it
could proceed with its separately controlled base-change work. The synthetic
commit API confirms ordered parents `[B,H]`. Final metadata preserves all six
workflow runs, nine jobs/check runs, and all six artifacts. All downloaded ZIP
sizes and SHA-256 digests match their captured GitHub artifact metadata. No
temporary signed download URL, credential or cookie is retained here.

`verify_capture.py` verifies the downloaded reports and their exact source/run
contexts. Its output is `verification-summary.json`. Linux execution records:
17 reference methods, 25 preservation methods, 6 context methods, 8 workflow
methods, 20 TeX methods and 33 archive methods, all PASS without skips/errors/
failures. Windows separately records 17 reference, 25 preservation and 20 TeX
methods passing. Successful PRES23 rows include all 12 newly added maintenance
mutation subtests. Method/subtest totals are distinct from requirement coverage;
these results are not a statement that all 108 acceptance cases executed.

The actual offline report records UID/GID 1001, no supplementary groups or
capabilities, no-new-privileges, a different network namespace, no outward routes
and a denied outward socket (errno 101). It reports the real empty historical
restore, strict object/parent/tree checking, 369 pins, exact TeX output, all 29
accepted legacy tests and original R C10 replay. Fresh Lean execution comes from
the separate successful Research workflow, not from replay.

Current C10 ZIP `c10-release-evidence.zip` is source-bound to this H/B/S and its
13-member payload passed the independent structure/arithmetic helper against
the canonical frozen specification. `c10-content-verification.json` records that
local check and preserves its scientific limits; no local Lean rerun is claimed.
The final PR77 review-thread read found the same five resolved threads and no
new/unresolved thread.

This baseline still lacks the subsequently requested standalone candidate-bound
one-time maintenance-scope CLI receipt. That follow-up, the normative archive
CLI documentation correction, new source/tooling/package commits and their
fresh genuine synthetic CI remain separate work. Any changed H/B/S invalidates
reuse as current acceptance. Eligible GitHub reviewer, active enforcement,
remote archival tag and durable external publication remain deferred. Agent
review is not a counted GitHub APPROVED review.
