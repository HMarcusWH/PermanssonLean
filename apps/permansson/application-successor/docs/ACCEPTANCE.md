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
`EVIDENCE_COMPLETE_REVIEW_REQUIRED`, **not** a release. Independent reviewer
identity, authority and owner activation must be established in a separate
nonself-issued trust process. The included `data/acceptance_policy.json` is a
*proposed minimum* for C10/C11 numerical selection, not an activated or
independently reviewed release profile. It cannot be used to waive the
historical `E_TOOLING_CLOSURE` archival gate.

No current operating mode claims PR/GR certification, empirical identification,
publication permission or owner signoff merely because its structural inputs
passed.
