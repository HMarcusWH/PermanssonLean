# Permansson Closure Successor — supported C10 v0.1.0

This is a **new** versioned application, entirely outside the frozen `application/` tree.

The sole supported input in this release is the exact frozen six-state D0/C10 rational model of the already-proved original `C10SixStateBridge` with the six legal named interventions and **complete original comparison set `[1,2]`**. The CLI reads *external JSON* but does not claim a theorem about arbitrary JSON, arbitary stochastic matrices, or empirical models. Arbitrary well-formed finite rational models **fail closed as unsupported** until a typed Lean adapter is separately established. It is not an optimizer for unrestricted learning, continuous policies or nonlinear history-dependent objectives.

## Run

Requires Python 3.13, git, and for proof replay the repository's **pinned Lean 4.34.0** environment and unchanged mathlib checkout. Invoke from any current working directory; the input and fresh output folder are explicit:

```bash
python apps/permansson/closure-successor/cli.py \
  apps/permansson/closure-successor/examples/frozen_six_state.json \
  --mode replay --output /tmp/c10-replay-fresh
```

`--mode numeric` independently validates the exact input, computes the exact rational C10 receipt and verifies it again, **without** running Lean. This is never a proof claim. `--mode replay` requires a clean Git repository, verifies the original trusted C10 source blobs and immutable specification, regenerates the numerical receipt and Lean proof source from the external input, invokes `lake env lean`, checks the compiler result and transitive axiom reports, and records source identity, generated proof digest and statuses. A missing compiler is an error, not a skipped pass. Outputs must be in a new or empty folder **outside the source tree**.

The output `result.json` has separate statuses: `numeric_status`, `lean_status`, `scientific_claims_verified` and `empirical_identification`. Even when the original constructed six-state theorem replays, the last two **remain false/NOT_IDENTIFIED**. That is not a claim that the abstract theorem is unproved; it means the CLI does not authenticate a real regime or its data-generating mechanism.

The input is limited to 128 KiB. Duplicate JSON keys, JSON floats and nonfinite numbers fail, as do wrong menu orders, altered stochastic transition rows, missing original comparison starts and out-of-profile objectives. `model.schema.json` documents input structure, but does **not** replace the runtime input-bound semantic check. `theorem_manifest.schema.json` documents output status distinctions.

## Chain of evidence

`frozen_six_state.json` → strict JSON parser → existing `check_input` → exact comparison to `six_input()` → existing `execute` → independent `verify_receipt` → `emit_golden_bridge` → compiler replay of `C10ReifiedGolden.lean` → printed theorem transitive axiom allowlist. Source checks require exact Git head/clean checkout and frozen source blobs; a self-reported JSON certificate is never accepted as Lean verification.

The CLI emits `numeric_receipt.json`, `C10ReifiedGolden.lean` and `lean.stdout.txt`/`lean.stderr.txt` (replay mode), plus `result.json`. The GitHub Research test `test_c10_app_successor_compiler.py` executes actual Lean. Negative tests ensure fake successful compiler exits without the correct axiom reports and unsupported model changes **fail**.

## Not included

No C11 general periodic/multichain interface yet, no arbitrary user-provided structural model theorem, no full external raw JSON decoder correctness theorem, no empirical identification, and no authority to certify operational action. Add C11 only after this first slice's source-head and synthetic-merge CI passes. Do not rewrite the original `application/` directory or the accepted release.
