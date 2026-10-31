# Reviewer guide

This page is for someone reviewing the successor application or one of its
Lean bridges without having written it. It says where to look, what each
piece is supposed to establish, and how to re-run the evidence yourself.

## 1. Reproduce before reading

From a checkout with the pinned toolchain
([`docs/RESEARCH_BUILD.md`](../../../../docs/RESEARCH_BUILD.md) at the
repository root):

```bash
lake build PermanssonResearch                                    # every bridge module
python -B -m unittest discover -s apps/permansson/application-successor/tests
python apps/permansson/application-successor/scripts/end_to_end.py --lean
cd verification/research && python -B -m unittest test_application_private_stage_live_lean
```

`scripts/end_to_end.py` runs every packaged example as a user would. It runs
each command, requires the independent check and an unpromoted report, emits
and byte-rechecks a Lean candidate and checks that a tampered copy is
rejected. With `--lean` it compiles each candidate and audits axioms. Use
`--app <venv>/bin/permansson-app` to run it against an installed wheel. The
live tests (`verification/research/test_application_*_live_lean.py`) add
single-line semantic mutations that must fail inside the targeted theorem.

## 2. Anatomy of one profile

Take `finite-private-stage` as the example; every profile has the same five
parts.

| Part | File | What to check |
| --- | --- | --- |
| Producer | `src/permansson_app/engines/private_stage.py` | strict parsing (exact field set, canonical rationals, bounds); the computation matches the docstring |
| Independent checker | `src/permansson_app/receipts/private_stage.py` | does **not** import the producer; recomputes every field (often in a different loop order); certificates checked directly; extra or changed fields rejected |
| Lean bridge | `PermanssonResearch/ApplicationBridge/PrivateStageReceipt.lean` | a decidable check over literal rationals, its soundness, and a theorem that transfers an existing Research result. Check the transferred statement matches the Research original, and that no hypothesis is assumed that the check does not decide |
| Emitter | `src/permansson_app/proof/private_stage_emit.py` | runs the checker first; every number in the Lean file comes from the request or receipt; theorem statements name the Research objects |
| Live replay | `verification/research/test_application_private_stage_live_lean.py` | positive instances compile with audited axioms; each mutation is semantically meaningful and fails at the stated theorem |

The profile's `docs/NUMERIC_*.md` and `docs/*_LEAN_BRIDGE.md` describe the
intended mathematics and its limits. Read them against the code, not
instead of it.

## 3. Questions worth asking of every bridge

- **What does the instance theorem quantify over?** For example: all real
  mixed controllers, all behavioral policies, all admissible randomized
  policies, or only the listed menu.
- **Where does each premise come from?** It should be decided by
  `decide +kernel` on the literal data, proved on the reflected α/P/U tables
  (`HeldFixed`, patch-row theorems), or a theorem of Research. Nothing should
  be assumed.
- **Is a claimed optimum or impossibility certified?** Look for a
  certificate (dual, Farkas ray, saddle mixtures, monitor table) rather than
  trust in a solver.
- **What is explicitly not claimed?** Each module docstring and bridge
  document lists it. Check that the application output does not overstate
  it: `lean_status` stays `NOT_EXECUTED`, `scientific_claims_verified` stays
  `false`, and empirical identification is `NOT_IDENTIFIED`.

## 4. Boundaries a change must respect

- Do not modify `PermanssonLean/`, `application/`, accepted release
  artifacts, `lean-toolchain`, `lakefile.toml` or `lake-manifest.json`, or the
  native C10/C11 providers. `PermanssonResearch.lean` only gains imports.
- No `sorry`, `admit`, `native_decide` or custom axioms. The axiom audit
  accepts only `propext`, `Classical.choice` and `Quot.sound`.
- Do not weaken a test to make it pass. Changes to emitter output must keep
  earlier candidates byte-identical unless the change is intended and
  documented. The source recheck compares bytes.
- Every new or changed file is recorded in `IMPLEMENTATION_MANIFEST.json`.
  Planned paths that were implemented under another name are marked
  `RECONCILED_SUPERSEDED_BY_IMPLEMENTED_EQUIVALENT`, not duplicated.

## 5. Where the status lives

- [`ACCEPTANCE_STATUS.md`](ACCEPTANCE_STATUS.md) — gate by gate, with the
  bridge table and live-test counts.
- [`ROADMAP.md`](ROADMAP.md) — what was planned, what is done, and what is out
  of scope.
- `IMPLEMENTATION_MANIFEST.json` — every inventory path with its state and
  digest.
- Pull request #115 — per-commit summaries and exact-head CI results.
  Earlier green results do not transfer to later commits.
