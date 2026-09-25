# Permansson Application Standard

**Draft 0.1.0, compatible with theory v0.1.8. Application contract, not a theorem extension.**

The standard serializes the three-layer application architecture in Sections
10.5-10.7 of the [frozen paper](../paper/README.md): mathematical regime,
frozen semantic counterfactual, and empirical certificate. The nine certificate
dimensions remain separate. `CONTRACT PASS` means only that the record satisfies
this version's structural rules. It is not a proof, empirical certification,
authenticated registration, or endorsement of the supplied evidence.

## Run from the repository root

```bash
python -m pip install -r application/requirements.txt
python application/validator/validate_application.py application/examples/grounded_pr_minimal/application.json --json
python -m unittest discover -s application/tests -v
python application/examples/build_examples.py
python verification/application_gate.py
```

The validator also runs as `python -m application.validator.validate_application`.
Validation uses bundled JSON Schema 2020-12 resources and never downloads schemas,
evidence, or executable code. Every referenced artifact must be a local, bounded,
regular file inside its bundle, with matching SHA-256 bytes.

## Contents

- [APPLICATION_STANDARD.md](APPLICATION_STANDARD.md): source crosswalk, rules and limits.
- [schemas/](schemas/): five domain schemas plus common definitions and bundle schema.
- [validator/](validator/): read-only CLI and Python interface.
- [examples/](examples/): self-contained synthetic fixtures, including unresolved and invalid records.
- [tests/](tests/): positive, negative, mutation, offline and portability checks.
- [Future theory roadmap](../docs/FUTURE_THEORY_ROADMAP.md): three separate research lanes, none promoted to v0.1.8.

`VERSION.json` versions this draft independently. The paper's citation, immutable
Lean snapshot, theorem ledger, release hashes and Appendix E boundary are unchanged.
