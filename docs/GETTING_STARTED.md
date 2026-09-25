# Getting started

[Repository home](../README.md) · [Documentation index](README.md) · [Glossary](GLOSSARY.md)

Start with the application example below to try the reporting format. Lean is
needed only for [building the proofs](#build-the-lean-proofs). Reading the
[paper](../paper/README.md) needs neither Python nor Lean.

## Setup

Use Git and **Python 3.13**, the version used by repository CI. Installation of
Python dependencies and Lean caches needs network access; application validation
itself does not download schemas or evidence.

Clone once, then enter the repository:

```bash
git clone https://github.com/HMarcusWH/PermanssonLean.git
cd PermanssonLean
```

Already have a checkout? Open a terminal in its root: the directory containing
`README.md`, `application/`, `verification/`, and `lakefile.toml`.
All commands below use that working directory unless stated otherwise.

Create an isolated Python environment using the instructions for your shell.

### Linux or macOS

With Python 3.13 installed and available as `python3.13`:

```bash
python3.13 -m venv .venv
. .venv/bin/activate
python --version
```

### Windows PowerShell

With Python 3.13 installed and available through the Python launcher:

```powershell
py -3.13 -m venv .venv
.\.venv\Scripts\Activate.ps1
python --version
```

If local policy blocks activation, do not change system policy for this project.
Use `.\.venv\Scripts\python.exe` in place of `python` in subsequent commands.
On Linux/macOS the corresponding direct interpreter is `.venv/bin/python`.
Confirm that the selected interpreter reports Python 3.13 before continuing.

## Run the first example

```bash
python -m pip install -r application/requirements.txt
python application/validator/validate_application.py application/examples/grounded_pr_minimal/application.json --json
```

Expected: exit code **0** and these fields in the JSON result (the notice is omitted
from this excerpt):

```json
{
  "contract_valid": true,
  "errors": [],
  "scientific_claims_verified": false
}
```

Read the example's [specification](../application/examples/grounded_pr_minimal/specification.md)
and [argument](../application/examples/grounded_pr_minimal/argument.md), then its
[application.json](../application/examples/grounded_pr_minimal/application.json).
The toy model alternates between two states; the declared intervention changes its
long-run occupation mean. The analytic argument is in the artifact, not proved by
the JSON validator. Every fixture's dates and empirical-mode flags are synthetic.

**`contract_valid` describes the record's structural consistency.** It is not the
same as `certificate.validity`, and neither a contract PASS nor a digest proposal
establishes empirical truth. A well-formed record can report an invalid application
or unresolved identification. See the [scope table](APPLICATION_BOUNDARY.md).

## See an expected rejection

Run this separately: it is supposed to return exit code **1**.

```bash
python application/validator/validate_application.py application/examples/invalid_posthoc_specification/application.json --json
```

Expect `contract_valid=false` and error code `POSTHOC_CONFIRMATORY`: the fixture
mislabels exploration as valid confirmation. Compare it with
[valid_posthoc_exploratory](../application/examples/valid_posthoc_exploratory/application.json)
and [invalid_application_record](../application/examples/invalid_application_record/application.json),
both of which pass the structural check without making that invalid promotion.
The [example index](../application/examples/README.md) lists every expected outcome.
Do not interpret every fixture's nonzero exit as a broken installation.

## Make a separate practice copy

Do not edit the committed examples or their evidence to experiment. This command
copies a complete bundle to a new directory and refuses to overwrite an existing one:

```bash
python -c "from shutil import copytree; copytree('application/examples/grounded_pr_minimal', 'application/bundles/tutorial-copy')"
python application/validator/validate_application.py application/bundles/tutorial-copy/application.json --json
```

The copy is still a synthetic demonstration, not a ready-made empirical study.
For an actual application, work through the [standard](../application/APPLICATION_STANDARD.md):
replace the toy specification and argument with your own declared mechanisms,
regime/property definitions, intervention, model-set and inference rules, evidence,
and justified status annotations. Do not inherit the fixture's dates or claims.
Artifact paths are relative to the directory containing `application.json`.

When intentionally changing an artifact, review its bytes and record the new SHA-256
in that bundle's `artifacts` registry. A portable way to inspect a file's hash is:

```bash
python -c "from pathlib import Path; import hashlib; print(hashlib.sha256(Path('application/bundles/tutorial-copy/specification.md').read_bytes()).hexdigest())"
```

Do not recompute hashes simply to conceal an unexpected change. Keep raw evidence
in its bundle directory; the repository's Git attributes preserve those bytes.
Do not commit confidential evidence to this public repository.

## Propose an identifier, then validate

After deliberate semantic changes and artifact-hash updates, the pipeline and
certificate may still share the same old ID. Request a new proposal:

```bash
python application/validator/validate_application.py application/bundles/tutorial-copy/application.json --digest --json
```

The command tolerates only `PIPELINE_DIGEST`; the two declared IDs must already
match, and all other checks must pass. Exit 0 means **a proposal was generated**,
not necessarily that the input conforms. Inspect `digest_generated`,
`proposed_pipeline_id`, `contract_valid`, and `errors` independently.

Review and explicitly record the proposed ID in both
`semantic_pipeline.pipeline_id` and `certificate.pipeline_id`. Then run the ordinary
validator again:

```bash
python application/validator/validate_application.py application/bundles/tutorial-copy/application.json --json
```

Only this ordinary validation exit 0 is the structural acceptance gate.
A changed semantic pipeline requires a new freeze/selection account; a locally
computed hash does not authenticate preregistration. Never backdate a freeze to
silence a chronology error. The [CLI reference](../application/validator/README.md)
and [canonical exit table](../application/APPLICATION_STANDARD.md#mode-specific-exit-codes)
cover bootstrap, error, and help behavior.

## Test the application installation

```bash
python -m unittest discover -s application/tests -v
python application/examples/build_examples.py
python verification/application_gate.py
```

The tests must finish with `OK`; the regeneration check reports
`Example regeneration PASS`; the gate reports `application_contract_gate: PASS`.
The tests check expected failures as well as successes. The regeneration script
compares decoded text; the tests additionally verify exact fixture bytes.
No `--write` flag is needed for routine testing.
For the independent numerical and repository checks, use the
[verification guide](../verification/README.md).

## Build the Lean proofs

Install Lean through **elan** using the [official installation guide](https://lean-lang.org/install/manual/).
Keep this repository's `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.
From its root:

```bash
lake env lean --version
lake exe cache get
lake build
```

The version must be Lean **4.34.0**. The dependency is mathlib **v4.34.0**.
The cache command follows Lean's documented existing-project workflow and avoids
unnecessary dependency rebuilding. Initial downloads can take longer than an
incremental build. `lake build` should exit 0; the exact number of build tasks varies
with cache state. Do not run `lake update` or change pins merely to try the examples.

The [Lean workflow](../.github/workflows/lean.yml) also runs the root axiom audit
and placeholder/custom-axiom rejection. Local build success alone is not a claim
that every CI audit ran. Follow the [formalization map](FORMALIZATION_MAP.md) to
inspect specific declarations. The Python application examples are not new Lean proofs.

## Troubleshooting

| Symptom | What to check next |
|---|---|
| Python, pip, or a module is missing | Select the Python 3.13 environment above; install with that interpreter's `-m pip`, not a different pip executable. |
| A repository-relative path is missing | Return to the repository root. Artifact paths inside a bundle are relative to its manifest, not the shell directory. |
| `SCHEMA` | Check required fields, exact status vocabulary, and explicit nulls against the [schemas](../application/schemas/README.md). |
| `ARTIFACT_HASH` / `ARTIFACT_PATH` | Verify the original bytes, declared path, file size, and absence of symlinks. Do not normalize evidence or silently update its recorded hash. |
| `PIPELINE_DIGEST` / `CERTIFICATE_PIPELINE` | Review the semantic change and both IDs; use the deliberate proposal/validation workflow above, not automatic repair. |
| `FREEZE_CHRONOLOGY` / `POSTHOC_CONFIRMATORY` | Correct the actual reporting/selection account; do not change dates or status flags merely to force a PASS. |
| Run 34 reports missing files | It requires an external release package and its original layout, not just a Git clone. See the [release-gate guide](../verification/v0.1.8_release_gate/README.md). |
| `lake` is unavailable or versions differ | Check elan installation and open the project root. Preserve the pinned files; consult the official setup guide rather than installing an unrelated tool with the same command name. |

When reporting a problem, include the exact command, working directory, interpreter
version, commit, exit code, and error output. Redact private evidence. Follow the
[contribution guide](../CONTRIBUTING.md) for changes to the repository itself.
