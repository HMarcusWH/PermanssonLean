# NEXT-03, part 1 — concrete semantic adversaries (draft scoped work)

This is a **subset** of strengthened acceptance fixtures, not the whole NEXT-03 or an independent proof of the generic PR79 mathematics. Historical source, compiler pins, original X1 region, earlier receipts and core theorem declarations are untouched. No release promotion follows from a Python test.

| Round 2 acceptance | New exercise | Actual evidence required | Scope still missing |
|---|---|---|---|
| X-01 | Change one `E/baseline` emitted probability row from `[3/4,1/4]` to `[2/4,2/4]`, retaining nonnegativity and total mass 1 | Positive exact generator source compiles, *actual kernel equality* false mutant rejected with proof diagnostic (Research CI; not performed locally) | None for this one adversary; all other X1 atom cases retain old PR79 checks |
| X-04 | Remove one of nine tied E/action starts, keep the same numerical minimum 271/800 yet falsify original-set equality | Independent exact-rational Python; compiler-level false original-domain coverage still pending | A Lean rejection of the tied-start domain change |
| Q-03 / A2-P01 | Actual three-history-stage survivor kernel with conditional errors 1/10, 1/5 and 1/4; TV exactly 23/50 | Independent exact-rational Python | Concrete Lean dependent-stage witness to be added for complete routing |
| F-01 | Asymmetric deterministic common/private update with explicit coordinate swap; mismatched input transport produces a counterexample | Independent exhaustive Python over all 64 Boolean configurations | Original FiniteProductTwo API instantiation in Lean |
| M-02 | Same key marginals but opposite action-key coupling, with marked law TV 1 | Independent exact-rational Python | Original F1 marked-law theorem adapter in Lean |
| F-05 | Positive finite SCM | No new evidence in this part | Route the existing tested positive Python example to F-05 and provide concrete Lean SCM witness |

Additional Python regression includes the time-zero initial-law shift (TV 1 with zero transitions) as a guard against accidental A2-P02 weakening.

## Build gate

The arithmetic tests require only the repository's immutable X1 exact JSON:

```sh
python -B -m unittest verification.research.test_next03_semantic_arithmetic -v
```

The nontrivial Lean mutant is mandatory in the usual Research-test-discovery CI. It runs the unchanged positive source first, requires exact literal-renderer correspondence, then substitutes a **stochastic** but mathematically incorrect emission without editing the source tree. Parser, missing-module, unavailable Lean, timeouts, and resource errors are never counted as successful proof rejection. The test needs the existing pinned Lean toolchain and built research dependencies; isolated local Python arithmetic cannot certify it.

**NO-GO:** Declaring complete NEXT-03, substituting a normalization-only failure for a genuine equality theorem, treating unchanged tied minima as identical B1 domains, treating equal unmarked key laws as equal action-marked laws, or promoting finite evidence to an Exact GR/PR claim.
