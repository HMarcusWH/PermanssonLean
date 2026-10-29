# Finite-world α/P/U literal Lean source — application implementation candidate

Status: **source emitter + source binding checked, no current-source pinned-Lean compilation or axiom audit yet**. This is an implementation step toward `ApplicationBridge/FiniteWorldInput.lean` and not a mathematical release certificate.

## Scope and mathematical boundaries

`permansson_app.proof.finite_emit` accepts the application successor's strict `Permansson.App.FiniteStrategicWorld.v1` JSON. It uses the **existing** exact rational, state-name, feasibility, row-normalization and semantic-identity parser. The reifier is intentionally restricted to **1–2 strategic, world and action indices each**, even though the numerical application accepts larger finite models. It emits a concrete `FiniteWorldInput ns nx na` with fully reflected rational α/P/U entries and proof obligations for all primitive stochastic rows. The emitted theorem instances assert each induced joint transition atom and complete row normalization, using the source's exact `α(s,x,a) · P(x'|s,x,a) · U(s'|s,x,a,x')` ordering.

For an action excluded by the state-specific feasible set, the numeric input omits `P/U` source rows. The Lean structure requires total function fields; the emitter uses a **declared normalized Dirac extension** on those unused indices. Such values are *not* claimed to be empirically supplied, admissible actions, or identified causal dynamics. Its proof source explicitly marks this distinction, and the JSON candidate enumerates each extension.

All generated equality theorems require Lean to reduce the actual serialized rational expressions; none are postulated as axioms or introduced using `sorry`/`admit`/`native_decide`. Source generation alone does not establish those proofs compile.

## Execute the source emission and integrity recheck

Run from a clean exact-source checkout containing the successor package, with its package installed or `PYTHONPATH` set to the application successor's `src` directory. Use a **fresh detached** destination outside the repository:

```bash
MODEL=apps/permansson/application-successor/src/permansson_app/data/examples/finite_world.v1.model.json
OUT="$(mktemp -d)"/reified
python3 -B -m permansson_app.proof.finite_emit "$MODEL" --output "$OUT"
python3 -B -m permansson_app.proof.finite_source_check "$MODEL" "$OUT"
```

`ReifiedFiniteWorld.lean` is the source candidate. `source_candidate.json` binds the exact input bytes, normalized typed semantic identity, generated source SHA-256, declared theorem names and any synthesized infeasible-action extensions. Rechecking regenerates the exact source, compares all bytes, and refuses changed input, altered source, modified claimed status, extra receipt fields, noncanonical receipt JSON, or symlinked file paths. The checker deliberately returns `SOURCE_BYTES_MATCH_NOT_LEAN_PROOF`.

## Next qualified proof stage — **not part of source emission**

At the exact future candidate Git head, run the pinned `lake build PermanssonResearch` and compile the generated source with that repository's pinned Lean/mathlib and `lake env lean "$OUT/ReifiedFiniteWorld.lean"`. Preserve the exact source head, Git tree, Lean/toolchain identity, complete logs, compiler exit, printed axiom dependencies and negative mutations (wrong α, wrong P, wrong U, wrong exact atom, incomplete row, forbidden action). A green compiler result does not certify the raw JSON parser in Lean, global control optimality, empirical α/P/U identification, or the original 45-case/11-claim independent CERT program. A separate trusted consumer must bind exact result bytes to the **same** input, theorem names and source commit before calling any receipt `LEAN_VERIFIED`.

A successful *default* Lean workflow is not a substitute for the dedicated Research Lean/instance proof replay. The 2026-10-29 `BeliefReceipt.lean` `noncomputable` correction remains separately dependent on its exact-head Research Lean job.
