# C10 source-bound release evidence

[Documentation index](README.md) ·
[C10 research ledger](LANE_C10_EXACT_CONSTITUTIVE_EXECUTION.md) ·
[Frozen audited v1.1 requirements](PR61_C10_Exact_Constitutive_Execution_Spec_v1.1_AUDITED.md)

## What it proves and what it does not

**Historical compatibility:** `Permansson.C10.rational-margin.v1` retains
its original meaning: `effects` is a vector over the normalized comparison
set. It remains verifiable for archival records; the new release does not
rewrite or falsely relabel old receipts.

**Current release:** `Permansson.C10.rational-margin.v2` reports a complete
`effects` vector over **all** `n` states plus a checked
`comparison_effects` projection. The original margin still minimizes
**only** that projection on the predeclared `B₁`. The new strict
`Permansson.C10.release-evidence.v2` manifest binds the v2 numerical
receipt, source, frozen specification, original six-state Lean proof, and a
separate rational-initial-law evaluation plus Lean witness.
A v1 receipt is rejected by the v2 release-evidence verifier.

The six-state-only emitter `c10_emit_golden_bridge.py` first verifies the
whole normalized frozen six-state input and index/ID ordering. In its
separately compiled generated Lean file it proves pointwise identity of
the baseline and **all six** menu matrices, descriptor, and full comparison
set against `sixRaw`. It then proves the six receipt margins equal the
**original** `sixOriginalMargin` values on the frozen B₁ and checks the
selected member, global optimum and ties. This does **not** alter the generic
reifier or identify arbitrary external strategic-world models.

The original six-state baseline Exact GR proof is separately referenced
as `C10.six_original_baseline_exactGR` and its axioms are printed. Its
existence cannot be inferred from a JSON flag. For arbitrary generic
rational inputs, positive numerical margins remain **PR unverified** until
actual input-bound original Exact GR and comparison/descriptor transport
terms are supplied.

## Reproduce in GitHub Actions (trusted PR mode)

```sh
python3 verification/research/c10_release_evidence.py \
  "$RUNNER_TEMP/c10-release-evidence" \
  --event-file "$GITHUB_EVENT_PATH" \
  --repository "$GITHUB_REPOSITORY"

python3 verification/research/c10_verify_release_evidence.py \
  "$RUNNER_TEMP/c10-release-evidence" \
  --event-file "$GITHUB_EVENT_PATH" \
  --repository "$GITHUB_REPOSITORY"
```

These steps run **only** on a `pull_request` event after the Research
Lean library is compiled. The GitHub event is the expected source of the
independently supplied source head and base. `git rev-parse HEAD`
must equal `GITHUB_SHA`. The verifier reads `git cat-file -p HEAD`,
which works even with checkout depth one, and checks the synthetic merge's
first and second parent identities against the GitHub event. A supplied
manifest cannot override these expectations.

Before generation, after the Lean proof, before independent verification,
and after replay, source integrity checks compare tracked and untracked
non-ignored files to the commit (`git status --porcelain=v1 -z`), verify the
immutable v1.1 specification Git blob and reject staged/unstaged/deleted
or untracked shadow sources. Legitimate ignored `.lake` build artifacts
remain separate from the Git source identity; actual compilation, toolchain
pinning and Lean kernel checks remain their own gates. The audit does not
misrepresent a clean Git tree as a proof about arbitrary cached binaries.

The artifact `c10-release-evidence` has 30-day retention; the v2 folder
contains all of the following and rejects unexpected additional files:

- `input.json` — original raw golden request, not falsely equated to
  its canonical normalized representation
- `normalized_input.json` — exactly normalized comparison/menu and matrix
  inputs
- `receipt.json` — independently checked **complete full-state v2**
  exact-Fraction numerical receipt
- `C10ReifiedGolden.lean` — complete reconstructed input, numeric claims,
  original-six-state data binding and real-margin theorems
- `lean_check.stdout.txt`, `lean_check.stderr.txt` — actual Lean compiler
  output (plus a separate fresh rerun during validation)
- `mixed_initial.json` — exactly normalized rational distribution over all
  six states, with half the mass at each original comparison start
- `mixed_report.json` — independent non-PR mixed-event report with exact
  baseline/member values, signed changes and absolute changes
- `C10MixedGolden.lean` — Lean-checked literal six-state initial-law mixture
  using `C10RationalInitialMixture.lean`
- `mixed_check.stdout.txt`, `mixed_check.stderr.txt` — actual mixed-law
  Lean compiler output and a separate fresh kernel replay
- `evidence_manifest.json` — source/base/merge identifiers, artifact
  SHA-256 values, frozen specification SHA-256, fixed interpretation scope
- `verification_summary.txt` — a human-readable fixed boundary statement,
  **included in the canonical SHA-256 manifest and checked byte-for-byte**
  during independent verification; unexpected bundle files are rejected

Input, receipt and generated Lean source are byte-reproducible for an
identical logical input and pinned implementation. Logs and CI provenance
depend on run context; their byte hashes are recorded, not promised
universally identical.

## Trust boundary

Checking a digest verifies **byte identity relative to an expected value**.
A self-consistent collection of user-provided hashes does not authenticate
GitHub source, confer a Lean proof, or establish an original GR/PR claim.
GitHub Actions event and checkout context are assumed independently
trusted **only in the CI environment**. Running these scripts with a
locally forged event file does not produce an external attestation.

The independent Python checker independently evaluates graph classes,
Dirichlet boundary/harmonic equations, and exact margins; it shares
input parsing/normalization code with the numerical producer. It is
independent arithmetic rechecking, **not** independent verified parsing
or formally verified Python.

The v2 full-effect-vector test cases specifically tamper with an effect
**outside B₁**, leaving the actual original margin unaffected. Both the
independent Python checker and generated Lean `FullReceipt.pointwiseEffect`
must reject a forged value. Historical v1 only covers the old projected
effect schema, never masquerading as a complete v2 report.

The C10 metamorphic regressions also perform nontrivial complete
**physical-state relabelings**, checking bottom-class/absorption weights,
the frozen Boolean event vector, all original comparison-state effects
and lowest-index worst-start tie breaking in the *new* coordinates.
**Menu permutations** preserve per-ID probabilities/margins and the
complete set of maximizers; the first normalized tie is intentionally
allowed to change with the declared menu order. Distinct IDs sharing
an identical kernel remain distinct candidates.

The new, separate `c10_eval_initial_law.py` accepts a finite exactly
normalized rational initial law and checks a v2 receipt. Its independent
`c10_verify_initial_law.py` recomputes all mixed probabilities without
calling the producer's aggregation function. Both use exact `Fraction`
arithmetic. It is a **probability query**, not a change to the fixed-menu
optimizer. Mathematically, `C10RationalInitialMixture.lean` constructs
the actual D0 probability measure and composes C2's canonical
initial-mixture theorem with C10's point-start path-law correspondence.
The two optional numeric effects
`|Σ μ (p_i-p_0)|` and `Σ μ |p_i-p_0|` differ in general; neither is
the original `min_(x∈B₁) |p_i(x)-p_0(x)|`. The adversarial four-state
cancellation fixture has original numeric pointwise margin 1 but mixed
signed/absolute probability change zero, demonstrating why mixing
must never replace the original B₁ objective.

The generated Lean source and its proof terms are rechecked by the real
Lean kernel (`decide +kernel`; no `native_decide`), while both initial
and rerun `#print axioms` reports must use only
`propext`, `Classical.choice`, and `Quot.sound`.
The repository Research Lean root's transitive axiom audit is separate.

Unsupported external model identification, unverifiable event metadata,
missing/altered proof files, invalid rational data, source mismatch, and
Lean execution failure are **not** mathematical infeasibility evidence.


## Mathematical coverage

The complete theorem and hypothesis crosswalk is in the
[C10 research ledger](LANE_C10_EXACT_CONSTITUTIVE_EXECUTION.md#v11-mathematical-claim-coverage-source-hypothesis-review).
The new `C10ReleaseRegimeEquivalences.lean` supplies the strictly
hGR-gated positive-receipt-margin iff original relative PR statement,
and the original C9 support eligibility iff under hGR **plus** literal
`almostSureWeak` mode. Its one-way support-ineligible ⇒ not PR
statement needs literal mode, but not hGR, and does not equate that
conclusion with a zero margin without hGR. These are new post-review
source assertions pending a fresh final-head Lean build and review.

The extra corollary file `C10ReleaseCorollaries.lean` derives
Cramer good-class mass = C7 `pointGoodMass`, and positive
rational Cramer absorption = existence of a reachable member of
the computed bottom class, from C8 native-representative reachability.
These are *additional* formal-proof obligations that require passing
Research Lean compilation and the three-axiom audit at their exact
source head; metadata cannot certify them.

The original six-state baseline Exact GR evidence is a separate imported
theorem, not a field in the numeric release receipt. Its hypotheses are
not generalized to arbitrary external JSON inputs.

## Before merging

Require all four exact-head GitHub workflows on the actual PR synthetic
merge, the full revised test count, the 3-axiom root audit, a successful
CI-uploaded source-bound artifact and generated proof replay, final
mathematical theorem-hypothesis review and documented code review.
Any commit, including documentation, restarts exact-head CI checks.
No final SHA is embedded inside its own tracked source file. The author's
explicit merge approval remains separate; post-merge CI is separate proof.
