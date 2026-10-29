# PR113 — historical T → T2 security review dossier (candidate; not approval)

**Current baseline for this dossier:** Historical T
`71cc34fa0bc4b639c05d2ec5f39f0b88afd56388`;
PR base B `17c315f7df7abf457eb94d393bd526d46da6f6f4`.
The run must bind **the actual latest source head H at execution**; any
source-changing commit resets its source identity and all downstream
review/execution artifacts.

## Scope

The original `archive-reproducibility` CI job currently runs an unmodified
`verification.archive.offline_smoke` against candidate C. It fails closed
with `E_TOOLING_CLOSURE` because **two** current canonical integrity-tooling
files differ from the frozen T package:

| Source path | T Git blob | H pre-dossier Git blob |
|---|---|---|
| `verification/integrity/workflow_contract.py` | `7c1b26559dc30c2f37e8165983ce71094b205cde` | `f8fa8196a7a0e33d2f218faa0ba570c09aac9a3a` |
| `verification/integrity/tests/test_workflow.py` | `66ba674710cae286605baf3eee570ee1d7fcf282` | `1fa90e0dce90518b8052e42199867f11c77e1010` |

Verify these actual objects again at **final H**; the pinned example H objects
are a record, not permission to reinterpret a later change. All other
`verification/integrity/`, `verification/archive/`, and
`archival/v0.2.0/README.md` Git members are to remain unchanged as proved
by `pr113_tooling_migration.audit`. Original packaged T source and the
v0.2.0 archive/expected hash must never be modified.

The H workflow set contains 25 protected GitHub workflow files; new
`pr113-*` producing workflows, concurrency, job identities, action versions,
privilege scope and events must be reviewed **as a complete source set**.
Staged future producer workflows outside `.github/workflows` are
**not active**, and a prospective 26+ workflow set is a NEW review target.

## Dual execution before approval

The source-controlled **candidate** entrypoint is
`verification/research/pr113_dual_tooling_candidate.py`, and the
historical candidate workflow source remains
`docs/operations/pr113_unapproved_workflows/pr113-historical-migration-candidates.yml`.
The proposed workflow is not installed. Its GitHub execution is allowed only
as a specifically named exact-branch **push candidate** after the
workflow has been independently authorized for activation. Never interpret
its result as the required archived check.

1. Obtain actual complete-history checkouts: historical T and candidate H
   with clean Git status. Keep different source roots, output outside either.
2. Install exactly Python 3.13 and `pypdf==6.10.0`; verify availability of
   `sudo`, `unshare`, `setpriv`, nonroot runner, and real network isolation.
   No offline-to-online fallback.
3. Run original historical T's **unaltered** `offline_smoke` standalone,
   with GitHub event and secret environment entirely excluded. Verify the
   historical artifact is restored and the original check reports PASS,
   `acceptance_scope=accepted_artifact_replay_only`,
   `network_isolation=ENFORCED` and `capabilities=all_zero`.
   This is NOT execution of the original gate against today's C.
4. In the separate actual H checkout run original source-controlled workflow
   regression suite and record all methods/failures/errors/skips and the
   current 25-workflow source binding.
5. Independently audit every packaged T file versus its immutable T
   Git object, the two changed T/H blob pairs, exact 25-file workflow
   membership and current H tree with `pr113_tooling_migration.audit`.
6. Retain both original unedited JSON reports, digest them, and generate
   `T2_security_review_candidate.json`. Status MUST remain
   `COMPLETE_DUAL_EXECUTION_CANDIDATE_SECURITY_REVIEW_PENDING` and
   independent approvals MUST be false.

**No approval from a green candidate.** A historical PASS alongside a
current-H workflow suite PASS only demonstrates two distinct execution legs,
not authorization to redefine the required T/C archival closure.

## Required human decisions

A genuine **independent security reviewer** must examine all source objects,
especially two changed integrity files, all current and proposed workflows,
event/permission restrictions, old and successor verifier behavior,
no-change guarantees for T, negative-adversary coverage and every
source trust transition. The repository owner must explicitly authorize the
precise versioned T2 profile **after** that review. Do not author approval
JSON, independent GitHub reviews, check-run identities, or merge commits in
this implementation work.

Only after explicit owner plus nonauthor security authorization:

- implement the versioned, active mandatory `archive-reproducibility` gate
  so it **executes both historical T and reviewed T2**, each with legitimate
  separate source binding; never short-circuit the historical leg;
- update the protected workflow contract **as one reviewed atomic source
  revision**, restart final H provenance, and rerun all 12 required GitHub
  contexts at exact final H;
- retain both original execution reports/ZIPs and approval provenance.
  Any new workflow, action, test selection or source change makes the
  prior security review stale.

## Stop/failure conditions

- Original T still fails, lacks true namespace isolation, or gets labeled
  current C; historical archive/expected digest modified.
- Current H's 25 protected workflows do not pass its own original suite.
- T/H source drift beyond the explicitly reviewed two files.
- A candidate tries to run as `research` or `archive-reproducibility`.
- No authentic owner + independent security signoff or a stale final H.
- Missing review of proposed future workflow producer additions.
- Original mandatory `archive-reproducibility` continues to fail.

All T2 receipts remain **candidates**; no mathematical acceptance,
independent reviewer certification or publication is implied.
