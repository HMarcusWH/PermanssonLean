# Application successor — governance and evidence architecture

This module set extends the numeric application without changing `PermanssonLean/`,
`application/`, accepted release artifacts, pinned Lean/mathlib or any active workflow.

## Directed trust boundary

```text
verified exact caller source and controlled model input
       ↓
versioning + semantics + monotonic resource budget
       ↓
numeric engine → independent checker → detached result receipts
       ↓
provenance DAG + claim registry + externally pinned evidence set
       ↓
selected-scope acceptance ASSESSMENT (never owner approval)
       ↓
independent security review + owner decision (out of band)
```

The Lean bridges and the application emitters (`proof/*_emit.py`, dispatched
by `permansson-app lean-emit`) produce candidate instances, not a proof merely
by generating source. `replay.py` does not invoke arbitrary Lean
source; it compares separately authenticated compile, axiom and negative-mutation
evidence for one exact source/mode/platform/theorem identity. Each of the three
records must attest the exact replay transcript (its `artifact_sha256` is the
SHA-256 of the transcript's canonical bytes), so the emitted source, theorem
type, toolchain, exits and axiom set come from the authenticated evidence, not
from the caller. Only an isolated, independently reviewed compiler runner may
produce those receipts.

External case-study packages enter through the bounded `domain/bundle.py` reader.
Only explicitly declared data assets are inspected; ZIP-contained scripts are
**never executed**, and support matrices or event counts cannot become identified
causal `alpha/P/U` by casting or relabeling them.

Federation is detached exact-set, read-only evidence exchange; its compatibility
check never grants remote execution or mathematical acceptance. A matching digest
without an independently authenticated source is only an integrity check.

## Deliberately limited scopes

- All registered capabilities (26 exact profiles and the 2 native C10/C11
  providers, see `CAPABILITY_SCOPES.md`) remain separately registered; this
  subsystem does not add a fake theorem-backed runtime mode.
- The 56 legacy mathematical case/claim IDs are imported as **review items**
  directly from `research/paper_closures/post_merge_112/` source maps; none is
  automatically certified by a successful Python or Lean build.
- Application acceptance is **eligible for external review at most**. The
  `AcceptanceAssessment.authorized_release` field cannot be set by a caller's
  JSON flag, a self-issued review, or the PR merge state.
- Historical archival reproduction remains red pending genuine T/T2 security
  review. The new code does not edit `verification/archive/`.
