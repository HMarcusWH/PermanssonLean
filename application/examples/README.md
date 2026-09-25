# Synthetic application fixtures

[Application home](../README.md) · [Setup and walkthrough](../../docs/GETTING_STARTED.md)

These are format demonstrations, not empirical findings or new Lean declarations.
Their timestamps and empirical-mode fields are synthetic. Each bundle contains
`application.json`, `specification.md`, and `argument.md`; copy the whole bundle
when experimenting, not just the JSON file.

## Suggested reading order

Start with [grounded_pr_minimal/specification.md](grounded_pr_minimal/specification.md),
its [argument](grounded_pr_minimal/argument.md), and
[manifest](grounded_pr_minimal/application.json). Then compare a finite-horizon
case and an unresolved case before inspecting the intentionally rejected record.

| Fixture | Expected contract outcome | Purpose |
|---|---|---|
| [exact_gr_minimal](exact_gr_minimal/application.json) | PASS | Period-two Exact GR; constitution not evaluated |
| [grounded_pr_minimal](grounded_pr_minimal/application.json) | PASS | Grounded strategic intervention; analytic gap 1/2 |
| [quasi_regime_minimal](quasi_regime_minimal/application.json) | PASS | Leaky process; exact rational finite survival, no Exact PR |
| [unresolved_identification](unresolved_identification/application.json) | PASS | Unknown support/modularity and statistical coverage remain unresolved |
| [invalid_posthoc_specification](invalid_posthoc_specification/application.json) | FAIL: POSTHOC_CONFIRMATORY | Invalid promotion of exploration to valid confirmation |
| [valid_posthoc_exploratory](valid_posthoc_exploratory/application.json) | PASS | Exploration remains explicitly exploration |
| [invalid_application_record](invalid_application_record/application.json) | PASS | Well-formed record truthfully labels the application INVALID |

PASS means structural consistency only. In particular, the last fixture shows why
`certificate.validity` is not the validator's exit status.

## Run and verify

After [setup](../../docs/GETTING_STARTED.md#setup), run from the **repository root**:

```bash
python application/validator/validate_application.py application/examples/grounded_pr_minimal/application.json --json
python -m unittest discover -s application/tests -v
python application/examples/build_examples.py
python verification/application_gate.py
```

[expectations.json](expectations.json) is the fixture test manifest. The deliberately
invalid fixture must return exit 1 when validated directly. The test suite and
gate succeed only when every fixture matches its exact expected error-code set;
they do not skip the rejected example or expect every bundle to pass.

## Preserve fixture and evidence bytes

The regeneration command compares generated **decoded text** without writing files.
The unit tests separately check exact fixture bytes. `--write` explicitly regenerates
fixtures during deliberate development; it is not a repair step for unexpected drift.

The Git attributes default nested bundle payloads to `-text`, preserving their raw
bytes rather than converting all evidence to LF. Only scoped authored source paths
are normalized. Neither the generator nor validator performs empirical inference.
Use a [separate practice copy](../../docs/GETTING_STARTED.md#make-a-separate-practice-copy)
for your edits; do not repurpose committed synthetic evidence as a real study.
