# PR #113 — two-stage historical verification cutover

**Status:** implementation runbook only; not security approval, workflow activation, release certification or a merge decision. Current base and accepted historical artifacts are never rewritten.

## Immutable authority and scope

- Original historical T: `71cc34fa0bc4b639c05d2ec5f39f0b88afd56388`.
- Original A2 introducer: `f71a76032b169aac7bfe0694aa715339a94d4e05`.
- Source-pinned preactivation workflow inventory: 25 exact files at `5189f0c4a0db7535d57a9ff2a7aef6a3e76191b6`.
- The candidate is exactly **23 retained + 2 replaced + 5 added workflows**, plus three source guards. The ten-path cutover is atomic and needs separate approval.
- `main` PR #113 source baseline is `17c315f7df7abf457eb94d393bd526d46da6f6f4`. Always authenticate real later H/S/M from GitHub; do not write predicted SHAs or runtime IDs to committed source.

## Stage 0 — Engineering, without authority

1. Keep the installed 25 workflows untouched. Reproduce historical T in a genuine detached T checkout with Python 3.13, pypdf 6.10.0 and proven nonroot/offline network namespace. Separately verify the current 25-workflow suite. Neither replay is current source approval.
2. Compile original A2 from its exact historical checkout under pinned Lean 4.34.0 and source-pinned dependencies. Independently run successor A2 on a genuine disposable 30-workflow checkout. Require real positives, transitive-axiom evidence and all four intended semantic negatives per leg; parser/import/timeout failure is not evidence.
3. Run `pr113_disposable_transition_rehearsal.py` for the exact ten-path candidate and synthetic [B,C] tree/parent checks. Require current CI-06/07 and eight active30 regression suites. It remains local/nonauthorizing.
4. Prepare one immutable source-review dossier: exact Git objects and file modes, all relevant called verifiers, 25/30 inventory, actions/permissions/events, source-mutation controls, historical T/A2 execution records, dependency hashes, producer scheduling, response to failure and every retained workflow's risk.

## Stage 1 — Source security review and installation decision

1. An authorized *independent* security/engineering reviewer assesses the entire proposed source configuration and the Stage-0 evidence. A builder's synthetic proof, code comment, JSON boolean, or current CI status is not independent review.
2. The owner separately authorizes **installing the exact reviewed source on the unmerged PR branch for evidence production**. This is not final artifact attestation, a merge or mathematical acceptance. Record external decisions and exact source identity, not future artifact IDs, in the relevant detached review evidence.
3. If either permission is absent, do not install or silently skip original required checks. Do not demand the producer's future GitHub artifacts before the workflow has been authorized to run.

## Stage 2 — Actual producer artifacts and final source-bound attestation

1. Install exactly the 23 retained / 2 replacement / 5 additional workflows and three guard files as one reviewed source change on PR #113. Verify all 30 actual Git blobs and updated manifest/test OIDs. Preserve every historical T archive and original A2 verifier source.
2. The new historical producer is registered for **PR-branch push**; this is different from manual workflow dispatch on the default branch. At the actual install H, confirm the GitHub push event launched both real `historical-T-and-H-unreviewed` and `historical-A2-and-H-unreviewed` producing jobs. Both must succeed at the exact same run attempt before collection. Rerun or reschedule the producer at the same H if required, using a real supported GitHub trigger—never a fabricated commit/run or a borrowed CI check.
3. Obtain the genuine T/A2 artifact ZIPs and their SHA-256 digests. Authenticate repository, branch, H, workflow source, run/attempt, job, check-run, artifact identity, ZIP members, original T isolated restoration and genuine A2 positive/four-negative source results. Transport and attest these outside Git source.
4. The configured independent reviewer then submits an actual current GitHub PR review binding exact **final H, 30-workflow fingerprint, original base B and both T/A2 ZIP digests**. Reviewer independence and dismissal/latest-review state are authenticated through the owner-approved reviewer policy. Any subsequent source edit makes the attestation stale.
5. Admin provides the genuine original producer run ID and approved review ID through GitHub variables/authorized inputs. Rerun the same final source H's original `research` and `archive-reproducibility` contexts. The phase-aware runtime exports `PERMANSSON_HISTORICAL_REQUIRED_RECEIPT` for every phase; initial #113 alone may export the original T/A2 sidecars.
6. Require the entire Research suite plus C10, D0, default target, import coverage and firewall to actually execute. Require all 12 exact H/S required check contexts and the archive's original adversarial coverage. A source success flag without executed job evidence is insufficient.

## Descendants and final main

- After separately owner-authorized ordered merge, record real M113 and verify parents `[B113,H113]` and identical H/S/M tree. Reauthenticate the first actual main-push historical gate, not the premerge PR event.
- For later CERT and main descendants, use `pr113_historical_inheritance_v3` against the immutable genuine M113 source and real current descendant event. The staged A2 test consumes the **phase-neutral receipt** and calls the same fail-closed `check_stored` verifier; it never asks CERT to fabricate PR113 event or borrow initial ZIP sidecars.
- The original 4+9+8 mathematical producer workflows are a distinct CERT pipeline, requiring actual default-branch registration and authenticated frozen Hcert dispatch after M113. A path-filtered push or docs-only YAML is not proof of a GitHub producer run.
- GitHub's *effective* main rules and required-status-check set must be inspected separately: a source-side 12-context checklist does not automatically configure branch protection.
- Infrastructure acceptance never means independent 45/45 or 11/11 mathematical certification, scholarly approval, sealing or publication.

## Mandatory rejection cases

Wrong H/B/S/M, reversed merge parents, missing historical isolation, altered T archive, stale/foreign/doubled run or artifact, source/blob drift, unauthorized or stale review, duplicate/nonfinite JSON, missing provenance, any skipped required Research step, failing original A2, false-mutant parser failure, a 25-as-30 upgrade, a 31st workflow, and inherited ZIP evidence instead of revalidation all fail closed.

No unauthorized approval, workflow installation, GitHub ruleset change, merge, certification or publication is implemented by this runbook.
