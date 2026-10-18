# Permansson — Paper proofs and mathematical build specification

**Reference:** main `39279799834ae536bda715dedecdc11a32bf6c82`.
**Document:** `PERMANSSON-PAPER-CLOSURES-1`, 18 October 2026.

This is a mathematical specification and coding-agent handoff, not a new formal release. It develops exact selected theorem statements and proof derivations for all 42 entries in the input closure atlas. Broad research entries retain explicit scope restrictions and residual obligations. No fresh Lean compilation or repository write was performed.

## Reading order

Read `MATHEMATICAL_BUILD_SPEC.pdf` or its identical-content Markdown source, then `AGENT_BUILD_DIRECTIVE.md`. The per-item machine-readable contract is `registries/closure_contracts.json`. Original atlas inputs and source hashes are under `sources/`. `SOURCE_REGISTER.md` distinguishes source-derived facts from the new paper derivations.

The main derivations include exact X1 kernel/margin reflection, an exact discounted performance-difference identity, a strict-autonomy MA2 obstruction, measurable shared-mass bounds, finite/Polish transport and invariant-law constructions, a generic finite-monitor solver theorem, risk/robust/partial-observation variants, a total rational C11 stationary constructor, compact-Feller occupation limits, grammar transport, a new positive economic witness, and five conditional specialized algebraic adapters.

## Executed evidence versus future acceptance

The independent standard-library checker passed **27 test methods** with zero failures/errors/skips. It generated eight X1 matrices (144 stochastic rows), 576 terminal-table values, 54 effect entries and six exact minima, with explicit corruption checks. These are finite arithmetic checks, not universal proofs or Lean certificates. All new registry `formal_status` fields are `NOT_LEAN_VERIFIED`.

`registries/acceptance_tests.json` contains **45 implementation acceptance requirements**, not 45 additional completed tests. The coding agent must implement and run the relevant proof/adversarial tests on the actual source and genuine synthetic merge.

## Reproduce the included numerical checks

From this package root, with Python's standard library:

```text
python -B verification/exact_checks.py --output /path/to/new/scratch
python -B verification/validate_spec.py --root .
```

The first command writes proposed exact tables and its observed test report. The second checks registry coverage, dependency acyclicity, source-register syntax and file integrity; it does not validate every mathematical proof. The PDF was generated from the Markdown using Pandoc/XeLaTeX. `render/` contains the build inputs and log, not a Lean environment.

## Highest-impact scope corrections

The finite MA2 theorem is an impossibility result under full baseline-supported mechanism agreement and autonomous strict anchors. Direct dual contraction and finite four-process occupation factorization do not require general KR duality. C11 total stationary construction is new; C10 total Dirichlet construction is already proved. A seam-invisible symmetric defect has rank at most two; rank one needs the extra constant-diagonal premise. A positive economic example is new, leaving the old X1 negative result unchanged.

The five Appendix E entries remain conditional adapters until actual model/source identifications are proved. General-state and extended-control results are closed only in the stated profiles, not in arbitrary measurable or information structures.
