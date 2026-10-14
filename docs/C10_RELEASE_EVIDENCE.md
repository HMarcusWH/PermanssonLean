# C10 source-bound release evidence

[Documentation index](README.md) ·
[C10 research ledger](LANE_C10_EXACT_CONSTITUTIVE_EXECUTION.md) ·
[Frozen audited v1.1 requirements](PR61_C10_Exact_Constitutive_Execution_Spec_v1.1_AUDITED.md)

## What it proves and what it does not

The existing `Permansson.C10.rational-margin.v1` output is an exact
rational **numerical** report. The separate
`Permansson.C10.release-evidence.v1` manifest binds it, without modifying
its strict schema, to source, specification, input and generated Lean proof.

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

The artifact `c10-release-evidence` has 30-day retention; its folder
includes:

- `input.json` — original raw golden request, not falsely equated to
  its canonical normalized representation
- `normalized_input.json` — exactly normalized comparison/menu and matrix
  inputs
- `receipt.json` — independent exact-Fraction certificate, unchanged v1
- `C10ReifiedGolden.lean` — complete reconstructed input, numeric claims,
  original-six-state data binding and real-margin theorems
- `lean_check.stdout.txt`, `lean_check.stderr.txt` — actual Lean compiler
  output (plus a *separate fresh rerun* during validation)
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

The C10 metamorphic regressions also perform nontrivial complete
**physical-state relabelings**, checking bottom-class/absorption weights,
the frozen Boolean event vector, all original comparison-state effects
and lowest-index worst-start tie breaking in the *new* coordinates.
**Menu permutations** preserve per-ID probabilities/margins and the
complete set of maximizers; the first normalized tie is intentionally
allowed to change with the declared menu order. Distinct IDs sharing
an identical kernel remain distinct candidates.

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
