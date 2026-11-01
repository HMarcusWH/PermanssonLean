# Selected-capability release assessment — not release authorization

The `acceptance.py` policy consumes a typed `AcceptanceTarget` bound to Git
commit **and tree**, paper, research and application versions, exact wheel and
sdist digests, selected capabilities, platform set and execution mode.

Evidence must be present as an externally pinned SHA-256 exact record set, with
explicit source and method IDs. The policy enumerates required method IDs per
capability and kind. A recorded FAIL, ERROR, SKIPPED or NOT_EXECUTED cannot be
counted as PASS. An Ubuntu result cannot satisfy the Windows selection.
Lean-replay or empirical selections add proof or identified-source obligations.
An unrelated 45-case or 11-claim numerical check cannot substitute for
independent mathematical acceptance.

`python -m permansson_app.governance_cli release-assess TARGET EVIDENCE EXTERNAL_PINS POLICY --output NEW_DIR`

**Important limitation:** Even a completely covered test matrix is
`EVIDENCE_COMPLETE_REVIEW_REQUIRED`, **not** a release. The decisions the
policy requires (a review, an activation) are always listed as missing; they
are established outside the tested artifact. Two release scopes are packaged,
and neither is an activated release profile:

- `data/acceptance_policy.json` (v1, the default) is the *proposed minimum* for
  C10/C11 numerical selection.
- `data/acceptance_policy.successor_numeric.v1.json` (format v3) is the
  owner-selected scope for the 26 exact finite profiles. It covers numeric
  results only, on Linux CPython 3.12 and 3.13. For each capability it names:
  - the exact unittest method IDs of its tests, the whole-run budget tests
    and its end-to-end walkthrough row (`numeric_test`);
  - the installed-distribution qualification on each platform
    (`cross_platform`, `verification/application_successor/check_installed_package.py`);
  - source identity, and the wheel and sdist (`package`).

  Its `release_authority` is an owner-engineering policy: the owner approves
  and activates a release, and no independent security review is claimed, so
  only `EXTERNAL_OWNER_RELEASE_ACTIVATION` is listed as missing. The release
  gate (`verification/application_successor/release_gate.py`) checks that
  activation through the GitHub API; see
  [`RELEASE_ACCEPTANCE.md`](RELEASE_ACCEPTANCE.md). Any other platform or
  execution profile is reported missing. Lean instance replay would need its
  own, separately authenticated policy.

Neither policy can waive the historical archive gate.

No current operating mode claims PR/GR certification, empirical identification,
publication permission or owner signoff merely because its structural inputs
passed.
