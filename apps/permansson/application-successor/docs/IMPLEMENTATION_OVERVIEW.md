# Implementation overview

The successor application is an exact-rational companion to the Lean
research library. It turns a finite, declared model into a checked numeric
result and, where a bridge exists, into a Lean source candidate. That
candidate is bound to the original request bytes and can be compiled with
the pinned toolchain. It never turns a result into a scientific
certification on its own.

## One request, four separable stages

```
request.json ──► engine (propose_*) ──► receipt ──► independent checker (check_*) ──► report
                                           │
                                           └──► emitter (*_emit) ──► Lean candidate ──► lean-recheck (bytes)
                                                                           │
                                                                           └──► lake env lean (pinned toolchain)
```

1. **Engine** (`engines/`). Parses the request strictly (exact field sets,
   canonical rationals, bounded dimensions) and computes the exact result.
2. **Independent checker** (`receipts/`). Re-reads the original request and
   recomputes every reported value, usually in a different loop order or by
   a different formula. It never imports its producer. A receipt that
   differs in any field, adds a field or claims a stronger status is
   rejected.
3. **Report** (`report.py`). Binds capability, model identity, receipt and
   checker into one document. Every scientific certificate dimension stays
   `null` and `kernel_checked_proof` stays `NOT_EXECUTED`.
4. **Lean candidate** (`proof/`). Runs the checker again and writes a Lean
   file in which the request's numbers are literal rationals, plus metadata
   that binds the request bytes, receipt bytes and Lean bytes by SHA-256.
   `proof/lean_candidates.py` dispatches every family.
   `proof/control_source_check.py` re-derives a candidate from the original
   bytes and compares it byte-for-byte. Compiling the candidate is a
   separate, local act; see [`NATIVE_PROOF_REPLAY.md`](NATIVE_PROOF_REPLAY.md).

## Package layout

| Path | Role |
| --- | --- |
| `src/permansson_app/__main__.py` | the `permansson-app` command line, one subcommand per profile plus `lean-emit` / `lean-recheck` |
| `src/permansson_app/engines/` | exact producers (`propose_*`) and strict parsers |
| `src/permansson_app/receipts/` | independent exact checkers (`check_*`) |
| `src/permansson_app/proof/` | Lean emitters, byte rechecks and the family dispatcher |
| `src/permansson_app/data/` | `capabilities.json`, Draft 2020-12 request schemas and packaged examples |
| `tests/` | unit, CLI and emitter tests (no Lean needed) |
| `scripts/inventory.py` | recomputes and checks `IMPLEMENTATION_MANIFEST.json` against the tracked tree; writes the detached post-commit head receipt |
| `scripts/end_to_end.py` | every packaged example through command, independent check, `lean-emit`, `lean-recheck`, tamper rejection and (`--lean`) pinned compile with axiom audit |
| `../../../verification/research/test_application_*_live_lean.py` | pinned-Lean live replays with axiom audits and semantic mutations |
| `../../../PermanssonResearch/ApplicationBridge/` | the Lean bridge modules the candidates import |

## Lean bridges

Each bridge module states a decidable check over literal rationals
(`check… = true`, closed by `decide +kernel` in the instance). It proves
soundness and then transfers an existing Research theorem to the checked
data. Examples are Bellman optimality, `monitor_optimal_and_attained`,
`transportFiniteConstitutiveCertificate` and `solvePrivateStage`'s
`returned_isGreatest`. Where a source α/P/U model is involved, the instance
also reflects it as a `FiniteWorldInput` and proves the relevant structure
on the literal tables: feasibility and P held fixed, and exactly the
declared patch rows.

The bridge set and each family's scope are listed in
[`CAPABILITY_SCOPES.md`](CAPABILITY_SCOPES.md). The evidence status of every
bridge is in [`ACCEPTANCE_STATUS.md`](ACCEPTANCE_STATUS.md).

## What is deliberately not here

No independent research CERT and no empirical identification. The only
workflow change is the owner-dispatched release workflow (pull request #118),
and the only release is 0.2.0, made by that workflow
([`RELEASE_ACCEPTANCE.md`](RELEASE_ACCEPTANCE.md)). The protected theory core, the
legacy `application/` root, the pinned toolchain and the C10/C11 providers
are not modified. See [`ROADMAP.md`](ROADMAP.md).
