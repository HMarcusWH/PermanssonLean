# Permansson Application Standard

[Repository home](../README.md) · [Setup and walkthrough](../docs/GETTING_STARTED.md) · [Glossary](../docs/GLOSSARY.md)

**Draft 0.1.0, compatible with theory v0.1.8. Application contract, not a theorem extension.**

Use this package to describe a Permansson application in a consistent, inspectable
format and check its declared structure. It serializes the three layers in paper
Sections 10.5–10.7: mathematical regime, frozen semantic counterfactual, and
empirical certificate. It does not estimate a model, infer causality, or verify
that an attached argument is correct.

## Run from the repository root

You need Python 3.13, not Lean or LaTeX. Follow the [environment setup](../docs/GETTING_STARTED.md#setup)
first. From the **repository root**, with the selected Python environment:

```bash
python -m pip install -r application/requirements.txt
python application/validator/validate_application.py application/examples/grounded_pr_minimal/application.json --json
```

Expect exit 0, `contract_valid=true`, and `scientific_claims_verified=false`.
The example is synthetic. Read its [specification](examples/grounded_pr_minimal/specification.md)
and [argument](examples/grounded_pr_minimal/argument.md), then compare the
[other fixtures and expected outcomes](examples/README.md).

The validator also runs as `python -m application.validator.validate_application`.
Dependencies need installation first; validation itself uses a closed local schema
registry and reads only bounded, bundle-local artifact files. It does not execute
application code or download evidence.

## Understand the result

`CONTRACT PASS` means the record satisfies this version's structural rules.
It is not proof, empirical certification, source authentication, justified
statistical coverage, or authentic preregistration. The nine certificate dimensions
remain separate; a well-formed record may report `validity=INVALID` or unresolved
identification. See the [verification boundary](../docs/APPLICATION_BOUNDARY.md).

`--digest` proposes an identifier and does not modify files. Its exit 0 is not a
validation gate: matching stale IDs can still leave `contract_valid=false`.
Follow the [proposal-then-validation walkthrough](../docs/GETTING_STARTED.md#propose-an-identifier-then-validate)
and [mode-specific exit table](APPLICATION_STANDARD.md#mode-specific-exit-codes).

<a id="contents"></a>

## Find the right reference

| Task | Guide |
|---|---|
| Make a separate practice bundle | [Getting started](../docs/GETTING_STARTED.md#make-a-separate-practice-copy) |
| Understand required declarations | [Canonical Application Standard](APPLICATION_STANDARD.md) |
| Inspect fields and schema composition | [Schema guide](schemas/README.md) |
| Use CLI options or the Python interface | [Validator reference](validator/README.md) |
| Diagnose errors | [Troubleshooting](../docs/GETTING_STARTED.md#troubleshooting) |
| Run tests or contribute changes | [Contribution guide](../CONTRIBUTING.md#application-contract-changes) |

[VERSION.json](VERSION.json) versions this draft independently of the theory.
The paper citation, immutable Lean snapshot, theorem ledger, release hashes, and
Appendix E boundary are unchanged. The [future theory roadmap](../docs/FUTURE_THEORY_ROADMAP.md)
is research, not additional certificate labels implemented by this package.
