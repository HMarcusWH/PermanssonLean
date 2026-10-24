# PR #113 implementation scope and certification successor handoff

**Status:** implementation contract / work in progress; **not** a mathematical, security, merge, or publication certificate.  
**Repository:** `HMarcusWH/PermanssonLean` · **PR:** [#113](https://github.com/HMarcusWH/PermanssonLean/pull/113)  
**Decision recorded:** 25 October 2026. This is a sequencing/scope decision, **not** an approval of final source or modified workflows.  
**Starting reviewed head:** `52f00c9ecb60219da31e7ee6780f6c5debfb5b87`; refresh GitHub identity for every later phase.  
**Original base:** `17c315f7df7abf457eb94d393bd526d46da6f6f4`.

## The boundary

> **#113 finishes proofs, implementation and verification infrastructure. A successor PR (CERT) runs genuine full mathematical acceptance and an independently reviewed publication process.**

A missing proof is **not** merely a missing acceptance vote. If it is promised in #113, implement and label it with its exact Lean hypotheses, or obtain an explicit owner decision identifying an unresolved research deferral. A deferred required theorem remains a blocker for complete certification.

Immutable historical authority includes the original 45 cases, 11 claims, 259 baseline declaration inventory (additions must be versioned, not substituted), accepted supplement/archive bytes, Lean/pins and original `PermanssonLean/` definitions. Historical T and A2 identities, checks and reports are never silently rewritten.

## Separate gates and roles

| Gate | Meaning | Cannot imply |
| --- | --- | --- |
| Implementation and infrastructure readiness | All claimed source implementations compile; integration, required CI, historical dual verifiers and independent security/engineering review pass | Independently certified mathematical results or right to publish |
| CERT mathematical acceptance | Actual source-bound proof/test receipts + authenticated independent 45/45 and 11/11 decisions | Permission to merge or publish |
| Release acceptance | Real approved CERT merge + two clean builds + scholarly/PDF review + exact archive bytes and independent postseal replay | Permission to publish without separate owner authorization |

The builder or coding agents implement. The independent engineering/security reviewer reviews the final combined trust surface. Genuine nonauthor mathematical and scholarly reviewers make corresponding source-bound decisions. Marcus retains separate authority for scope, workflow activation, each merge and publication. Source-owned `approved:true` flags and synthetic tests never create an external decision.

## #113: ordered implementation checklist (all unchecked until evidenced)

- [ ] **113-01 — Scope and handoff:** PR title/body and this document agree; preserve the 45/11 obligations, old provenance and draft paper. This step documents scope only.
- [ ] **113-02 — Deterministic integration repairs:** pass `original_producers=authentic_original` and `original_producers=from_original` to the two public `validate_executed_controls` callers; correct the staged compiler `expected_job` to `compiler-shard`; prevent inner transport status overwriting preseal's outer status; test through real local validators and real committed manifest.
- [ ] **113-03 — Distinct infrastructure acceptance:** new typed engineering acceptance must require source identity, historical/security results and genuine review; every mathematical/seal/release gate rejects this receipt as certification.
- [ ] **113-04 — Versioned successor target:** separate original corpus, infrastructure baseline and CERT target. Verify actual PR/base/branch/source/run IDs without self-referential future hashes in frozen source. Old receipts stay historical.
- [ ] **113-05 — Mathematical source crosswalk:** all 45 original cases and 11 claims map to exact compiled theorem, hypotheses, positive/negative controls and separately recorded implementation/acceptance status. Inspect Q-05 real domination versus any still-unproved exact rational equality; preserve 259 baseline proof requirements.
- [ ] **113-06 — T→T2 and A2 security migration:** run untouched historical verifiers in their original isolated historical checkouts and successor verifiers separately, including both A2 positive controls and four genuine semantic mutations. Retain reports and immutable baselines.
- [ ] **113-07 — Runtime reviewer-input delivery:** producers → authenticated collection → observation survey → independently reviewed 20 legacy-event choices → replay. Choices must be detached, source-bound and authenticated; missing reviewer input must block.
- [ ] **113-08 — Complete workflow configuration:** prepare coherent pinned actions, permissions, job names, workflow inventory, dependencies, source-target semantics, and distinct dev versus explicit certification execution. Do not activate protected changes yet.
- [ ] **113-09 — Integrated release dry run:** source-faithful draft → complete synthetic evidence → strict fail-closed checks → candidate ZIP + SHA256 sidecar → independent synthetic replay. No fake release credentials or approvals.
- [ ] **113-10 — Reproducible truthful draft:** align manuscript to theorem crosswalk, build twice from clean source roots, compare required artifacts and inspect every page; no scholarly signoff claim.
- [ ] **113-11 — Actual security approval and activation:** present final combined T/T2+A2+CI/release profile to authorized independent security/engineering reviewer; obtain separate owner activation authorization and verify protected rules with admin access. Activate only exact approved bytes.
- [ ] **113-12 — Final-source freeze and full checks:** focused Python/regressions, full pinned Lean/axioms, historical/engineering 12 required contexts, entire Research workflow including C10, D0, default build, import coverage and firewall. No skipped/queued/cancelled run counts as success.
- [ ] **113-13 — Authorized merge and handoff:** request separate owner merge approval. Merge real #113, record `M113`, verify applicable merged-source CI, retain source/tree/receipts/limitations. **Not a mathematical release.**

Implementation dependency guidance: 113-02 follows scope; 113-03→04 follows repairs; 113-05 can proceed independently; 113-06/07 after target and provenance design; 113-08 after migrations/transport; 113-09 after executable inputs/workflows; 113-11 only after combined implementation and independent security review; 113-12/13 only after activation/freeze/owner decisions.

### Critical 113-02 source locations

- `verification/research/pr113_mandatory_v31.py` → `authenticate_all_76`
- `verification/research/final_closure_extra_producers_v31.py` → `assemble_review_pending`
- `verification/research/pr113_v31_execution_integrity.py` → real callee `validate_executed_controls`
- `docs/operations/pr113_unapproved_workflows/trigger_candidates/manifest.json` → staged `compiler-shard`
- `verification/research/pr113_original_producer_trigger_candidate.py` → check real manifest and original pinned blobs
- `verification/research/pr113_preseal_input_carrier.py` and staged `pr113-preseal-fullscope.yml` → outer status and transport diagnostic agreement

## CERT: ordered successor checklist (do not open or pre-approve early)

- [ ] **CERT-01:** After genuine `M113`, open a *new draft* PR based on main containing it; register GitHub's assigned PR number, not #114 (already closed/merged).
- [ ] **CERT-02:** Authorize genuine mathematical and scholarly reviewers, all 45+11 exact scopes, providers, assumptions and positive/negative selections.
- [ ] **CERT-03:** Freeze actual `Hcert`; prove target/base/source identity; store runtime identities only in detached records.
- [ ] **CERT-04:** Execute/authenticate **21 original producers** (4 compiler + 9 direct semantics + 8 legacy observations); collect **259 baseline** declaration receipts plus approved additions for `Hcert`.
- [ ] **CERT-05:** Obtain 20 authentic independent event selections from the real legacy survey; bind to producing observations and source.
- [ ] **CERT-06:** Run and authenticate **45 original positives, 45 original semantic negatives (25 direct + 20 legacy), 11 new claim positive/negative pairs and 76 additional control owners** with genuine run/job/check/artifact provenance.
- [ ] **CERT-07:** Obtain case-by-case independent mathematical acceptance for **45/45 and 11/11**; pass strict source-bound mathematics gate.
- [ ] **CERT-08:** Obtain separate owner approval to merge CERT; record actual `Mcert`, verify reviewed source ancestry/tree and required merged CI.
- [ ] **CERT-09:** Rebuild complete final paper twice from independent clean `Mcert` source roots; independently inspect and approve every PDF page, equation, reference and limitation.
- [ ] **CERT-10:** Produce actual full-scope preseal, candidate archive, checksum sidecar and independently replay the **exact candidate ZIP bytes**. Synthetic replay is insufficient.
- [ ] **CERT-11:** Obtain independent **owner publication authorization for that exact archive**, then publish precisely the checked bytes and preserved signed/attributed source records.

## Status bookkeeping

- `B113` is the pinned original base. `H113` changes until final infrastructure freeze. `M113` does not exist until authorized merge.
- `CERT` is a placeholder name. The next GitHub number, `Bcert`, `Hcert` and `Mcert` cannot be invented in #113.
- Requirements, source implementation, local test pass, CI evidence, independent acceptance, merge permission, and publication are separate columns in any generated ledger.
- **This document adds no independent review, security signoff, mathematical acceptance, merge authorization or publication authorization.**
