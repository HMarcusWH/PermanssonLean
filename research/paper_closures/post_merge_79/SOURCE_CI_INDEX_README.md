# NEXT-02 — post-PR79 source and evidence reconciliation (additive index)

This directory records a reproducible, **non-release** view of PR79. It does **not** replace or edit historical receipt files and does not certify the unrelated A2-P02 proof integration.

## Frozen objects (different roles)

| Symbol | SHA / meaning |
|---|---|
| B | `39279799834ae536bda715dedecdc11a32bf6c82` — PR79 base |
| H | `a1f1a77a301178e33412595265e823a873fb7301` — actual PR79 final source head |
| S | `fa0441227aa8b245b384b01b32f3bfb43a897f07` — PR79's genuine synthetic merge, with parents B then H |
| M | `674c1b557d99ab080afb65a797a99cb5840eab62` — actual PR79 merged main, with parents B then H |
| Tree | `b391f32f503f07bcfd7b29d8c24c1f9ad61eb19f` — shared H/S/M source tree |

`source_ci_index.json` inventories the 42 selected contract scopes/declarations and the source-bound research workflow records inspected in the independent October 18 Round 2 audit. The 22 archived job-log SHA256 hashes and six downloaded artifact ZIP hashes originate from that audited packet; the index alone **does not contain** those archives and cannot substitute for rechecking their actual bytes. Counters of 10,443 Research declarations and 918 test methods are **not** counts of newly proved theorems.

`receipt_normalization.json` preserves all 256 owner-receipt/source relationships. Of them, 234 are exact raw matches; 21 are reproducible newline-only representations (4 CRLF, 16 last-line CRLF, 1 last-two-lines CRLF); **one historical owner binding remains unreconciled**: `PermanssonResearch/EconomicWitness/ConstitutionCore.lean`. We retire that historical published hash as a present-day source authority, without overwriting the original receipt or pretending it can be reconstructed. Current source is independently identified at PR79's H/M tree.

`acceptance_decisions.json` retains all 45 acceptance IDs. It deliberately lists unresolved stronger-fixture obligations. `full_selected_programme_accepted` is **false**; absent final human/code review and the claimed 17-check/679-reference census are **not** promoted to approvals.

## Fail-closed checks

Run from a real Git checkout containing the PR79 merged-main ancestry:

```sh
python -B verification/research/post_merge_closure_index.py --repo .
python -B -m unittest verification.research.test_post_merge_closure_index -v
```

The verification reads the exact historical M Git blobs for all 256 owner record references, tests their raw or specified newline transformations, checks each named declaration's source digest against the frozen source, and validates M's ordered parent/tree binding. Missing `.git` or missing Git objects is **not** silently treated as a PASS. The separate explicit release gate is expected to **fail** while acceptance cases remain pending:

```sh
python -B verification/research/post_merge_closure_index.py --repo . --release-gate
```

The gate's nonzero exit is not a Research CI failure when an honest pending snapshot is under review; attempting to promote it to an accepted release without closing the remaining cases **must** fail. Synthetic S is indexed using the independent Round 2 evidence, not falsely claimed to have been newly fetched by the offline verifier.

## Claim limits

The index is evidence provenance, not new Lean mathematics, operational authorization, empirical causal identification, or a replacement for head-specific PR review. A separate PR must implement NEXT-03's semantic mutation fixtures and address any residual acceptance gaps. No merge, publication, workflow change, or repository settings edit is authorized by this index.
