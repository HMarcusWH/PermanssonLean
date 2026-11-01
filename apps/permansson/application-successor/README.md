# Permansson application successor

An exact-rational application for finite strategic-world models
(`α` action selection, `P` world transition, `U` strategic update). For a
declared finite model it computes a result. An **independent checker**
recomputes that result. Optionally, it then produces a **source-bound Lean
candidate**, in which the request's numbers appear as literal rationals in
theorems that transfer results of the `PermanssonResearch` library.

> **Status: version 0.2.0, release candidate for the 26-profile numeric scope
> on Linux CPython 3.12 and 3.13. Not yet released and not independently
> certified.** A release is made only through the release workflow and its
> gate, activated by the owner under an owner-engineering policy that claims
> no independent security review ([`docs/RELEASE_ACCEPTANCE.md`](docs/RELEASE_ACCEPTANCE.md)).
> Every output reports `lean_status=NOT_EXECUTED`,
> `scientific_claims_verified=false` and `empirical_identification=NOT_IDENTIFIED`.
> A checked numeric result or a compiled Lean candidate is a statement about
> the declared finite model, not about a real-world regime.

The package is additive under `apps/permansson/application-successor/`. The
frozen `PermanssonLean/` core, the historical `application/` standard,
accepted release artifacts, the pinned Lean toolchain, the native C10/C11
providers and `.github/workflows/` are unchanged.

## Quick start

Linux with Python 3.12 or 3.13. Other platforms are unsupported for this
release: the whole-run budget relies on Linux process limits. Install with
offline Draft 2020-12 schema checking:

```bash
python -m pip install './apps/permansson/application-successor[full-schema]'
permansson-app capabilities                       # registered profiles and their exact scopes
permansson-app about                              # where the package is imported from, version, Python
permansson-app resources --full --output /tmp/permansson-resources
```

Run one profile, then emit and recheck its Lean candidate:

```bash
EX=/tmp/permansson-resources/examples
permansson-app finite-private-stage $EX/private_stage.v1.json --output /tmp/ps
cat /tmp/ps/independent_check.json                # status PASS, both saddle sides checked
permansson-app lean-emit --family private-stage $EX/private_stage.v1.json \
  /tmp/ps/private_stage_receipt.json --output /tmp/ps-lean
permansson-app lean-recheck --family private-stage $EX/private_stage.v1.json \
  /tmp/ps/private_stage_receipt.json --candidate /tmp/ps-lean
lake env lean /tmp/ps-lean/ReifiedPrivateStage.lean   # from the repository root, pinned toolchain
```

Every command writes a **new** output directory containing the receipt,
`independent_check.json` and `scientific_report.json`. A failing input leaves
no output directory and exits with status 2 and a JSON error on stderr.

## What it computes

26 exact profiles, each with its own command, independent checker and Lean
candidate family. The full table is in
[`docs/CAPABILITY_SCOPES.md`](docs/CAPABILITY_SCOPES.md).

| Area | Commands | Documentation |
| --- | --- | --- |
| Finite kernels, LP certificates, survival, occupation, exit, menus, Bellman, safety, perturbation | `finite-kernel`, `lp-propose`, `lp-check`, `finite-survival`, `finite-occupation`, `finite-exit`, `frozen-menu`, `finite-bellman`, `finite-safety`, `finite-perturbation` | [`NUMERIC_FOUNDATIONS.md`](docs/NUMERIC_FOUNDATIONS.md) |
| Residence monitors, nonlinear classwise objectives | `finite-residence`, `nonlinear-stationary` | [`NUMERIC_RESIDENCE_NONLINEAR.md`](docs/NUMERIC_RESIDENCE_NONLINEAR.md) |
| Patch grammars, typed quotients, adaptive block control | `finite-grammar`, `finite-quotient`, `finite-adaptive-grammar` | [`NUMERIC_GRAMMAR_QUOTIENT.md`](docs/NUMERIC_GRAMMAR_QUOTIENT.md), [`NUMERIC_ADAPTIVE.md`](docs/NUMERIC_ADAPTIVE.md) |
| Robust control: rectangular nature, private-stage saddle | `finite-robust-nature`, `finite-private-stage` | [`NUMERIC_ROBUST_NATURE.md`](docs/NUMERIC_ROBUST_NATURE.md), [`NUMERIC_PRIVATE_STAGE.md`](docs/NUMERIC_PRIVATE_STAGE.md) |
| One-step risk occupancy and cap infeasibility | `one-step-risk`, `one-step-risk-infeasibility` | [`NUMERIC_RISK_OCCUPANCY.md`](docs/NUMERIC_RISK_OCCUPANCY.md) |
| Partial observation | `one-step-belief`, `finite-belief-tree` | [`NUMERIC_BELIEF_CONTROL.md`](docs/NUMERIC_BELIEF_CONTROL.md), [`NUMERIC_MULTISTAGE_BELIEF.md`](docs/NUMERIC_MULTISTAGE_BELIEF.md) |
| CQ-1 finite constitutive certificates and their transport | `finite-cq1`, `finite-cq1-transport` | [`NUMERIC_CQ1.md`](docs/NUMERIC_CQ1.md) |
| W1 contraction, rational algebra witnesses, two-player protocols | `finite-metric`, `finite-algebra`, `finite-multiagent` | [`NUMERIC_METRIC.md`](docs/NUMERIC_METRIC.md), [`NUMERIC_ALGEBRA.md`](docs/NUMERIC_ALGEBRA.md), [`NUMERIC_MULTIAGENT.md`](docs/NUMERIC_MULTIAGENT.md) |
| Native C10 / C11 replay | `run --source-root <checkout>` | below |

Every profile is bounded: dimensions, horizons and rational sizes are capped,
and Lean reflection often has a smaller cap than the numeric profile. Each
command also runs under one whole-run budget for wall clock, CPU, memory and
output. An exhausted run leaves no output. See
[`docs/EXAMPLES_AND_LIMITS.md`](docs/EXAMPLES_AND_LIMITS.md).

## How results are checked

The pipeline is engine, independent checker, report, Lean candidate,
byte recheck, then pinned compile. Each stage is separate evidence:

- [`docs/IMPLEMENTATION_OVERVIEW.md`](docs/IMPLEMENTATION_OVERVIEW.md) — the pipeline and package layout.
- [`docs/EVIDENCE_AND_RECEIPTS.md`](docs/EVIDENCE_AND_RECEIPTS.md) — receipt fields and the separate levels of evidence. Optima and impossibilities carry certificates such as duals, Farkas rays and saddle mixtures, checked directly.
- [`docs/NATIVE_PROOF_REPLAY.md`](docs/NATIVE_PROOF_REPLAY.md) — compiling a candidate, the axiom audit, and what a pass does not show.

## Verify it yourself

```bash
# unit, CLI and emitter tests (no Lean needed)
python -B -m unittest discover -s apps/permansson/application-successor/tests

# every packaged example end to end: command, independent check, lean-emit,
# lean-recheck, tamper rejection; --lean also compiles and audits each candidate
python apps/permansson/application-successor/scripts/end_to_end.py --lean

# the same against an installed wheel (PYTHONPATH is removed and the app's import
# location is checked, so the run cannot fall back to the source tree)
python apps/permansson/application-successor/scripts/end_to_end.py --app /path/to/venv/bin/permansson-app

# the inventory matches the tracked tree (current counts, dispositions of planned paths)
python apps/permansson/application-successor/scripts/inventory.py --check

# byte-reproducible wheel and sdist from a clean commit, built with the hash-locked tools
# (an interpreter with `pip install --require-hashes -r requirements-build.lock`)
python apps/permansson/application-successor/scripts/build_distributions.py --output /tmp/permansson-dist

# pinned-Lean live replays with semantic mutations (needs `lake build PermanssonResearch`)
cd verification/research && python -B -m unittest discover -p 'test_application_*'
```

Reviewers should start with [`docs/REVIEWER_GUIDE.md`](docs/REVIEWER_GUIDE.md).
The current status of every gate is in
[`docs/ACCEPTANCE_STATUS.md`](docs/ACCEPTANCE_STATUS.md), and the plan and
out-of-scope items are in [`docs/ROADMAP.md`](docs/ROADMAP.md).
`IMPLEMENTATION_MANIFEST.json` records every inventory path with its state
and digest.

## Native C10 / C11 replay

The C10 and C11 routes run the existing native providers. They need an exact
repository source tree, which is checked against the providers' stored SHA-256
pins:

```bash
permansson-app run /tmp/permansson-resources/examples/c10.request.json \
  --source-root /path/to/PermanssonLean --output /tmp/permansson-c10
```

The same command accepts the C11 periodic and multiclass example requests.
Each output directory must be new and **outside the source root**. A source
ZIP can supply byte-identical providers for local inspection, but does not
authenticate a Git commit or enable Lean replay.

## Evidence import, legacy validation and detached bundles

```bash
permansson-app legacy-validate /path/to/application.json \
  --source-root /path/to/PermanssonLean --output /tmp/legacy-check
permansson-app domain-validate /path/to/known_at_evidence.json --output /tmp/domain-check
permansson-app bundle-inventory /path/to/result_files --scope numeric-only \
  --source-commit <commit> --source-tree <tree> --output /tmp/detached-manifest
permansson-app bundle-verify /path/to/result_files /tmp/detached-manifest/detached_manifest.json \
  --output /tmp/bundle-check
```

- **Legacy validation.** The legacy reader runs the historical offline
  validator without editing the seven original schemas or source.
- **Domain evidence.** `domain-validate` keeps the evidence role, the
  original event and `known_at` dates, the source publication time,
  missingness and uncertainty. It refuses to promote measurement support or
  a simulation into an identified causal transition law. It checks the
  **envelope only**
  ([`docs/DOMAIN_IMPORTS.md`](docs/DOMAIN_IMPORTS.md),
  [`docs/FEDERATION_CONTRACT.md`](docs/FEDERATION_CONTRACT.md)).
- **Detached bundles.** A bundle manifest lists exact relative paths, content
  SHA-256 and source *claims*. Verification checks the bytes and rejects path
  traversal, symlinks and unlisted files. A self-created manifest is not
  independently trusted, so pass `--expected-manifest-sha256` from an
  independent channel when one exists.

## Scientific and release boundaries

The nine dimensions of the original certificate stay separate from numeric
verification and are reported as `null` (not assessed), never as `VALID`,
`PR` or `CERTIFIED`. No `sorry`, custom axioms or placeholder modules simulate
completion. The following are outside this application and are not claimed:

- independent mathematical certification of the original 45 cases and the
  later 11 claims;
- empirical identification;
- application release acceptance;
- the 30-workflow GitHub Actions trust-profile migration (T2). The
  `archive-reproducibility` check itself was repaired separately, in pull
  request #116, under an owner-engineering policy that is not an independent
  security review (`docs/operations/ARCHIVE_SUCCESSOR_CONTRACT_V1.md` at the
  repository root).

The original Application Standard 0.1.0 and its digest profile are **not**
reinterpreted as the newer typed-rational identity profile
([`docs/SEMANTIC_DIGEST_PROFILE.md`](docs/SEMANTIC_DIGEST_PROFILE.md)).

All documentation is indexed in [`docs/README.md`](docs/README.md).
