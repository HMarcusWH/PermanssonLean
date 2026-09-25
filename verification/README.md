# Permansson verification guide

[Repository home](../README.md) · [Setup](../docs/GETTING_STARTED.md#setup) · [Verification boundary](../docs/APPLICATION_BOUNDARY.md)

Choose the check that answers your question. All commands below start in the
**repository root**, except the explicitly labelled external-package command.
A PASS in one layer does not replace a check in another.

## Choose a verification layer

| Layer | Main entry point | What PASS establishes |
|---|---|---|
| Application contract | `verification/application_gate.py` plus application tests | Declared structure and reporting consistency, not scientific truth |
| Executable destructive/regression suite | `verification/destructive/suite/run_all.py` | The tested numerical/structural cases pass, not a general proof |
| Repository integrity | `verification/repository_gate.py` | Specified source, artifact, metadata, and documentation synchronization |
| Deductive Lean | `lake build` and the Lean CI audits | The encoded declarations check on the pinned toolchain |
| Release package | Run 34 in its original external package | The specified historical artifact/build contract passes |

The repository includes the final PDF but does not duplicate the frozen ZIP release artifacts.
The paper and its Lean snapshot, the repository adaptations, and later application
checks have separate provenance. See the [provenance guide](../provenance/README.md).

<a id="application-contract-layer-separate-from-frozen-verification"></a>

## Application contract checks

Use the Python 3.13 environment from [setup](../docs/GETTING_STARTED.md#setup):

```bash
python -m pip install -r application/requirements.txt
python -m unittest discover -s application/tests -v
python application/examples/build_examples.py
python verification/application_gate.py
```

Expect `OK`, `Example regeneration PASS`, and an application-gate PASS.
The [Application contract workflow](../.github/workflows/application.yml) runs these
on Linux and Windows. An expected-invalid fixture is tested against its exact
error codes; it is not skipped. Unresolved applications and records declaring
INVALID remain representable. This is structural validation, not proof,
identification, support, source authentication, coverage, or authentic registration.

## Reproduce the current destructive suite

The [executable-verification workflow](../.github/workflows/verification.yml) uses
**CPython 3.13** with **NumPy 2.5.3** pinned in the suite's requirements file:

```bash
python -m pip install -r verification/destructive/suite/requirements.txt
python verification/destructive/suite/run_all.py
```

Expect all fourteen numbered runs, 17 through 30, to report PASS and the runner to
exit 0. The recorded strengthened post-proofread lineage contains **3240/3240
passing checks**; that historical count and a new run's output are distinct evidence.
The runner writes fresh logs under `verification/destructive/suite/logs/` and its
run summary under `verification/destructive/suite/results/v17_run_summary.json`.

Read the [suite guide](destructive/suite/README_RERUN.md) for the Run 30
`V017_SOURCE_CONTRACT.txt` fallback. A normal repository run does not re-audit the
complete historical v0.1.7 TeX unless that exact control is supplied. Runs 17–29
retain their numerical cases; older `rerun_legacy_*.py` helpers require external
historical workpacks and are not called by `run_all.py`.

[Windows instructions](destructive/WINDOWS_RERUN_INSTRUCTIONS.md) distinguish these
repository commands from the separately packaged Windows-safe ZIP.

## Repository integrity gate

```bash
python verification/repository_gate.py
```

Expect every check to report PASS and exit 0. This verifies the committed paper
PDF/TeX hashes, release identifiers, Run 17–34 source presence, Appendix D/E scope,
Lean snapshot/import references, documentation synchronization, and Python syntax.
It is not a Lean build or the package-level Run 34. No Lean or LaTeX installation
is needed to run this Python gate.

`verification/application_gate.py` independently checks application files, schemas,
version boundaries, expected fixture outcomes, and the application Git attributes.
Run both gates when reviewing changes that affect both documentation areas.

## Lean verification

Follow the [pinned Lean setup](../docs/GETTING_STARTED.md#build-the-lean-proofs),
then run:

```bash
lake exe cache get
lake build
```

The [Lean workflow](../.github/workflows/lean.yml) additionally runs its root axiom
audit and rejects `sorry`, `admit`, and source-level custom axioms. The
[formalization map](../docs/FORMALIZATION_MAP.md) defines the completion claim;
[Lean provenance](lean/README.md) separates the paper's immutable snapshot from
fresh CI results. No Python PASS certifies a Lean declaration.

## Reproduce the editorial-final package gate

**Not a normal-clone command.** Run 34 is a **package-level** gate requiring the
external release package, its original filenames, frozen/portable ZIPs, the v0.1.7
control TeX, and `pdflatex`, `pdfinfo`, and `pdftotext` on PATH.

From the extracted package root containing its `paper/`, `provenance/`, and
`verification/` directories:

```bash
python verification/v0.1.8_release_gate/run34_editorial_final_release_gate.py
```

The historical expected result is **58/58 PASS**. The normal clone uses a different
PDF filename and does not include the full required package assets. Follow the
[release-gate guide](v0.1.8_release_gate/README.md) rather than renaming repository
files or regenerating evidence to force a pass. Normal CI does not execute Run 34.

## Historical release gates

[Runs 31–33](v0.1.8_release_gate/prior_gates_31_33/README.md) target the pre-editorial
31-page artifacts. Their relocated sources are inspection/syntax-preservation
copies, not in-place rerun entry points. Current CI syntax-checks them.

## Historical source boundary

[Historical test reports](destructive/suite/POST_PROOFREAD_FULL_TEST_REPORT.md)
and compact older summaries describe their own recorded executions. The frozen
archive remains the authority for unavailable historical source workpacks and
full per-check results. The [future theory roadmap](../docs/FUTURE_THEORY_ROADMAP.md)
is not extra theorem coverage or a new empirical certificate.
