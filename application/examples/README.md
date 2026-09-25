# Synthetic application fixtures

These are format demonstrations, not empirical findings or new Lean declarations.
Their timestamps and empirical-mode fields are synthetic. The analytic finite
model is specified in each relevant `specification.md`, with a separate argument.

| Fixture | Expected contract outcome | Purpose |
|---|---|---|
| exact_gr_minimal | PASS | Period-two Exact GR; constitution not evaluated |
| grounded_pr_minimal | PASS | Grounded strategic intervention; analytic gap 1/2 |
| quasi_regime_minimal | PASS | Leaky process; exact rational finite survival, no Exact PR |
| unresolved_identification | PASS | Unknown support/modularity and statistical coverage remain unresolved |
| invalid_posthoc_specification | FAIL: POSTHOC_CONFIRMATORY | Invalid promotion of exploration to valid confirmation |
| valid_posthoc_exploratory | PASS | Exploration remains explicitly exploration |
| invalid_application_record | PASS | Well-formed record truthfully labels the application INVALID |

`expectations.json` is the test manifest. Expected failure is asserted by its exact
error-code set, not treated as a silently skipped example. CI checks that every
committed `*/application.json` is listed and tested.

`python application/examples/build_examples.py` compares regeneration byte-for-byte
without changing files. `--write` explicitly regenerates fixtures during deliberate
development. The application-specific `.gitattributes` rule preserves LF bytes on
Windows. Neither the generator nor the validator performs empirical inference.
