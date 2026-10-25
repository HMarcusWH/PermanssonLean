# PR #113 — R1–R6 engineering implementation handoff (unapproved)

**Status:** candidate implementation and execution contract only. **Not** a security, mathematical, scholarly, merge or publication certificate. Always refresh exact `H113` before running a producer or requesting review.

**Original immutable Git anchors:** T `71cc34fa0bc4b639c05d2ec5f39f0b88afd56388`; historical A2 `f71a76032b169aac7bfe0694aa715339a94d4e05`; original B113 `17c315f7df7abf457eb94d393bd526d46da6f6f4`.

## R1 — T → T2 source preservation

- `pr113_dual_tooling_candidate.py` runs the unmodified T archive verifier in its own exact-T checkout, without inherited CI credentials, with true offline namespace isolation. Separately runs the current H original workflow test suite as a **sanitized local source run**, never as a fabricated main-branch/PR check.
- Requires original T restoration PASS, `network_isolation=ENFORCED`, zero capabilities, exact current H local source, CI-06/CI-07 coverage and no skipped/error/failing tests.
- `pr113_tooling_migration.py` still protects the original archived supplement bytes and the exact **two** documented canonical integrity-tooling changes.
- Staged producing workflow: `docs/operations/pr113_unapproved_workflows/pr113-historical-migration-candidates.yml`. Remains **inactive** until independently reviewed and separately owner-authorized.

## R2 — real historical and current A2 compiler sources

- `pr113_dual_a2_compiler.py` requires the real old verifier checkout and the successor source, full positive compiler/source/signature legs and all four meaningful mathematical negatives **on each**. Intermediate status cannot mask a positive command failure or a false-mutant compilation success.
- The staged workflow reuses only identical, independently Git-pinned **dependency source checkouts**, not compiled project proof objects, and retains `historical_dependency_bridge.json` alongside both original A2 reports/logs.
- `infrastructure_acceptance.verify_A2_dependency_bridge` authenticates that receipt against exact Git-H `lake-manifest.json`, including the original audited mathlib revision. No changed A2 historical verifier or rewritten expected hash.

## R3 — noncircular required-check transition (NOT ACTIVATED)

- `infrastructure_acceptance.check_historical_only` authenticates **both** actual successful historical GitHub producer ZIPs, their original T/T2 and A2 semantics, the true source H/B/S target, and a real independent, exact-H security approval. It **does not query any of the twelve required source checks**, so a required check cannot circularly demand its own success.
- Only the **separate** `infrastructure_acceptance.check_evidence` can aggregate **12/12 authentic latest-H required checks** after they are independently green.
- `pr113_required_dual_gate.py` is fail-closed on local calls or other event identities. It is intended for reviewed replacements in the real `Research Lean` `research` and `Research integrity` `archive-reproducibility` original PR113-merge event jobs. Even on valid provenance it claims neither all-CI completion nor mathematical approval.
- Exact replacement proposals are staged and source-pinned in `docs/operations/pr113_required_gate_replacement_unapproved/manifest.json`: the required A2 test module, archive job fragment and original protected code hashes. **Do not silently install** them.
- **Additional mandatory review surface before installation:** `pr113_a2_successor_identity.py` currently pins `verification/research/test_localized_prefix_compiler.py` by original blob SHA. A reviewed future replacement must also update the **versioned exact-blob identity profile** and every affected `verification/integrity/workflow_contract.py` approved workflow digest and 25+5 review manifest. Until that coherent atomic source review is complete, the original test and original archive job stay red by design.
- Future reviewed workflow input delivery must retrieve original GitHub artifact ZIPs and source-bound external reviewer/owner attestations at actual H, no source-owned self-approval. Changing source H invalidates prior producer artifacts and reviews; refreeze/reexecute/review final H.

## R4 — mathematical source closure remains genuine research

No receipt, staged status or original 21-producer execution can substitute for a missing mathematical theorem. The **45 original cases, 11 new claims, and 259 baseline declaration identities** are preserved. Q-05 actual domination and full original-canonical-margin rational identities, D-09 original classwise nonlinear expected-functional identity, F-01 measurable matched protocols and the other recorded 15 pending/30 partial original cases still require actual source-level verification or an explicit owner-documented deferral. Deferred certification obligations remain blockers to full CERT.

## R5 — reviewer-choice transport

`pr113_legacy20_choice_delivery.py` continues to require a successful exact-H producing legacy survey and independent owner-authorized commenter, all 20 case-wise observed candidate events and original artifact hashes. It now rejects a GitHub issue comment edited after creation and retains the selected comment-body SHA-256 to support downstream provenance. No automated event selection or mathematical relevance approval is inferred.

## R6 — reproducibility rehearsal

`pr113_draft_rehearsal_auth.py` reopens the real two-clean-source-root GitHub artifact ZIP without extracting it to disk, verifies both actual PDFs, draft nested ZIPs, 13 original manuscript source members, corresponding SHA256SUMS, original PDF page render bytes and absence of independent or postmerge approval. Both outer and inner archives are bounded against traversal, symlinks, duplicate entries and excessive expansion. The detached report is `REPRODUCIBLE_DRAFT_BYTES_AUDITED_NOT_A_RELEASE`. A scholarly reader still needs to examine **every actual page and claim**.

## Commands after authentic historical producing jobs

```bash
# After the original T and A2 producing jobs finish successfully:
python3 -B verification/research/pr113_dual_review_packet.py \
  --head "$H113" \
  --T-artifact-zip "$REAL_ORIGINAL_T_ZIP" \
  --A2-artifact-zip "$REAL_ORIGINAL_A2_ZIP" \
  --out "$REVIEW_FOLDER/dual_review_packet.json"

# The historical-only required gate can run ONLY after the source profile,
# independent reviewer authority, genuine GitHub approval and artifact
# sources have been externally authenticated.
python3 -B verification/research/infrastructure_acceptance.py \
  --historical-only \
  --evidence "$REAL_EXTERNAL_ENVELOPE" \
  --historical-T-zip "$REAL_ORIGINAL_T_ZIP" \
  --historical-A2-zip "$REAL_ORIGINAL_A2_ZIP" \
  --out "$REVIEW_FOLDER/dual_authentication.json"

# After two clean-source manuscript builds (draft is not accepted):
python3 -B verification/research/pr113_draft_rehearsal_auth.py \
  --head "$ACTUAL_DRAFT_H" \
  --artifact-zip "$REAL_CLEAN_DRAFT_ARTIFACT_ZIP" \
  --out "$REVIEW_FOLDER/draft_rehearsal.json"
```

## Stop conditions / next decisions

1. No existing historical verifier may be skipped, replaced as if equivalent, or made to accept a changed T/C closure by updating a self-owned digest.
2. No staged workflow or protected original A2 test may be activated before **independent security review of exact combined source** and **separate explicit owner authorization**. The current repository reviewer-authority rosters are unconfigured.
3. Required CI may be considered green only when all **12 exact-H check-run identities** genuinely conclude success with complete Research Lean C10/D0/default/import/firewall stages. Two old required checks fail until the reviewed transition is activated and rerun.
4. Main-branch protection/rules must be independently checked by an administrator before any authorized merge. No current source commit or comment grants authorization.
5. **PR #113 merge** requires separate owner approval and actual merge M113. **CERT** independently handles 45/45 and 11/11 mathematical decisions, full manuscript approval, final archive bytes and publication authorization.

This document intentionally does not embed any future PR number, invented M113, fake reviewer, fabricated current CI identity, activation permission, or scholarly acceptance.
