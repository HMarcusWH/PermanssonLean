# Permansson application successor — implementation candidate

**Development status (2026-10-29):** independently checkable **numeric foundation**, not a complete 217-/251-file application, release or mathematical certificate. The former recovered C10/C11 seed has been extended with strict finite `α/P/U` kernels, exact rational LP candidate/certificate verification, finite killed-kernel survival comparisons, exact occupation families and first-exit routing, offline schemas, historical legacy import, detached bundle integrity and chronology-aware domain evidence intake. No Lean correspondence module or independent review is claimed for these new components.

The package is additive under `apps/permansson/application-successor/`. The existing `application/`, `PermanssonLean/`, accepted release artifacts, native C10/C11 providers, Lean toolchain and `.github/workflows/` remain untouched. The original Application Standard 0.1.0 and its historical digest profile are **not** reinterpreted as the newer typed-rational identity profile.

## Installation

Python >=3.12. To install with complete offline JSON Schema checking, use the optional dependency:

```bash
python -m pip install './apps/permansson/application-successor[full-schema]'
permansson-app capabilities
permansson-app resources --full --output /tmp/permansson-resources
```

The C10 and C11 numeric routes require an exact audited repository source tree, with their native providers' stored SHA-256 pins. Run from an installed package with an explicit source root:

```bash
permansson-app run /tmp/permansson-resources/examples/c10.request.json \
  --source-root /path/to/PermanssonLean-main \
  --output /tmp/permansson-c10
```

The same `run` command supports the C11 periodic and multiclass example requests. Each output directory must be newly created **outside the source root**. A source ZIP can supply byte-identical numeric providers for local inspection and execution, but does not authenticate a Git commit or enable Lean replay.

## Additional exact numeric profiles

```bash
permansson-app finite-kernel /tmp/permansson-resources/examples/finite_world.v1.model.json \
  --output /tmp/finite-kernel
permansson-app lp-propose /tmp/permansson-resources/examples/lp.v1.model.json \
  --output /tmp/lp-proposal
permansson-app finite-survival /tmp/permansson-resources/examples/finite_survival.v1.json \
  --output /tmp/finite-survival
permansson-app finite-occupation /tmp/permansson-resources/examples/finite_world.v1.model.json \
  --output /tmp/finite-occupation
permansson-app finite-exit /tmp/permansson-resources/examples/finite_world.v1.model.json \
  /tmp/permansson-resources/examples/finite_region.v1.json \
  --output /tmp/finite-exit
```

`finite-kernel` validates finite strategic/world/action spaces and admissible actions, exact rational stochastic `α/P/U` rows, and the induced joint transition kernel in the order **α → P → U**. The independent checker recomputes the full finite kernel; there is no theorem claiming identification of the factors from external data.

`lp-propose` enumerates bounded exact vertices and proposes a primal/dual certificate. The *separate* `lp-check` can verify supplied exact primal/dual certificates or a Farkas infeasibility witness without invoking a producer. An unlocated vertex returns `NO_CERTIFICATE_FOUND`, not a theorem of infeasibility. The checked value does not identify the controller that another solver happens to return. Finite LP correspondence to canonical Lean theorems remains unsupported. `finite-survival` compares a held-fixed strategic intervention against a baseline with an exact killed-kernel recurrence and a complete declared comparison set; it checks every horizon row and the minimum absolute finite difference. It cannot establish Exact GR/PR, infinite-horizon persistence, QSD uniqueness or empirical transition probabilities.

`finite-occupation` computes all bottom recurrent classes, exact stationary laws and start-specific absorption weights. Its `expected_limit_laws` are explicitly the **means of random limiting class laws**, not the law realized on every sample path. The independent checker reconstructs the canonical `α → P → U` kernel and uses separately calculated communication/reachability sets and exact stationarity/harmonic equations.

`finite-exit` accepts an immutable explicit region and finite horizon, checks every survival value and first-exit-by-destination vector, and preserves never-exit mass without renormalization. Eventual exit is an exact finite-state Markov property; it does **not** establish an equilibrium, constitutive intervention or an Exact GR. Both routes are numerical-only and fail closed on false receipts. Proof correspondence to canonical Lean statements is still unimplemented.

## Evidence, legacy import and detached bundles

```bash
permansson-app legacy-validate /path/to/application.json \
  --source-root /path/to/PermanssonLean-main --output /tmp/legacy-check
permansson-app domain-validate /path/to/known_at_evidence.json \
  --output /tmp/domain-check
permansson-app bundle-inventory /path/to/result_files --scope numeric-only \
  --source-commit 3492b26707788293ca88c66637b6ba021c7e478d \
  --source-tree 9ef00ac4b2d4f928aa6551ef3f0dfeb2d4434452 \
  --output /tmp/detached-manifest
permansson-app bundle-verify /path/to/result_files /tmp/detached-manifest/detached_manifest.json \
  --output /tmp/bundle-check
```

The legacy reader invokes the historical offline validator without editing the seven original schemas or source. `domain-validate` preserves evidence role, original event and `known_at` dates, source publication time, missingness and uncertainty; it refuses to promote measurement support, a support matrix or an assumption-conditional simulation into an identified causal transition law. The importer checks the **envelope only**; it does not ingest or authenticate an entire external research companion.

The detached bundle manifest lists exact relative paths, content SHA-256 and source *claims*. Offline verification checks their bytes and rejects path traversal, symlinks and unlisted files. **A self-created manifest is not independently trusted:** supply `--expected-manifest-sha256` from an independent channel when an external trusted digest exists. Even with a trusted hash, source provenance, mathematical applicability, theorem proof and empirical identification need separate verification.

## Scientific and release boundaries

The nine dimensions of the original certificate remain separate from numeric verification. The new report uses `None` for **not assessed**, not `VALID`, `PR` or `CERTIFIED`. Every numeric route explicitly reports that Lean was **not executed**, independent mathematical certification is **not assessed**, and empirical identification is **not identified**.

This development branch does **not** implement the 19-engine / 17-Lean-bridge full target. Absent capabilities stay unavailable; no dummy source files or `sorry`/axioms are used to simulate completion. The separately controlled mathematical 45-case/11-claim CERT, active GitHub Actions trust-profile migration, and independent application release acceptance are outside ordinary application numeric tests.

## Development tests

```bash
python -B -m unittest discover -s apps/permansson/application-successor/tests -p 'test_*.py' -v
python -B -m unittest discover -s verification/research -p 'test_application_successor_numeric.py' -v
```

An installed wheel and source distribution must be tested in clean roots outside the checkout. The current newly tested runtime is Linux/Python 3.13.5; a previous recovered prototype had separate Linux/Python 3.12 evidence. Current-source Windows, fresh Python 3.12, and pinned Lean replay have not been qualified here. See `IMPLEMENTATION_MANIFEST.json` and `docs/ACCEPTANCE_STATUS.md` for source-by-source status and blockers.

### Frozen finite-menu optimization

`permansson-app frozen-menu <request.json> --output <new-output>` computes exact rational finite-horizon survival or exit objective for each *explicitly listed* feasible alpha/U intervention, independently checks all choices, reports every tied optimum, and never claims that the menu exhausts all feasible policies. The mathematical/Lean and causal status remains unassessed. A packaged `examples/finite_menu.v1.json` provides a reproducible input.
