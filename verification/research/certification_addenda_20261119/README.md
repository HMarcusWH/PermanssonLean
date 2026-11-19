# Q-05 proof and certification audit addenda

This additive review candidate corrects the historical Tranche 5 compiler
failure and proves the missing original canonical whole-path outputs and exact
full-comparison-set margins. The baseline is main commit
`4ba5aa4e60391c8f675fef0bc0636ae12503649e`. Frozen mathematical sources,
dependency pins, workflows and acceptance decisions remain byte-identical.

## Historical correction

The original draft PR #122 probe fails under pinned Lean 4.34.0 at its two
`exact_mod_cast hq` steps. Its static test had passed, but that was insufficient
compiler evidence. The historical draft and its bytes are retained. The new
`tranche5_q05_conditional_margin_correction_addendum.lean` uses explicit
`Rat.cast_sub` rewriting and normalization, preserving the original theorem
statements, full comparison sets and conditional scope. Its five audited
declarations compile using only `propext`, `Classical.choice`, `Quot.sound`.

The replacement Python guard scans all code after masking nested comments and
strings. It rejects the standalone and nested proof-placeholder/axiom layouts
missed by the old line-prefix filter. The actual compiler and complete
per-declaration axiom audit remain authoritative.

## Tranche 6 canonical whole-path identities

`tranche6_q05_whole_path_identification.lean` derives the actual row integrals
from the frozen induced-kernel atom theorems. Canonical marginal recursion proves
the fine time-one mean and every later mean, and the coarse mean at every
positive time. The actual compression preserves the world coordinate. Integral
and infinite sum are exchanged using the existing integrability theorem, and
the entire geometric tail is evaluated with `HasSum`.

The two exported identities quantify over every treatment and start. They
have no assumed whole-path-identification or prescribed-margin premises:

- Fine output: `(2/3) * indicator(x) + (2/9) * p(t,s) + (1/9) * p(t,t)`.
- Coarse output: `(2/3) * indicator(x) + (1/3) * pbar(t)`.

## Tranche 7 exact original margins

`tranche7_q05_original_margin_addendum.lean` discharges both historical
identification predicates using Tranche 6 and the actual admitted-intervention
model equalities. It then applies the corrected full-domain infimum proofs:

| Original quantity | Exact value |
| --- | --- |
| Fine effect at either original start and full fine margin | `19/90` |
| Coarse effect at either original start and full coarse margin | `1/5` |
| Absolute difference of the original margins | `1/90` |

The original bound `<= 2/41` is compatible with these exact values. These
results establish neither Exact GR nor independent acceptance of Q-05 or any
other certification case.

## Reproduce the focused checks

Use the existing pinned environment without updating dependencies:

```sh
lake build PermanssonResearch.Quotient.Q05ActualAtomClosure PermanssonResearch.MultipleLimit.CanonicalKernelMarginals
python3 -m unittest verification.research.test_cert_q05_whole_path_addendum verification.research.test_cert_tranche4_q05_original_path_crosscheck -v
python3 verification/research/certification_addenda_20261119/Independent_Fraction_Crosschecks_Addendum.py
```

The integrated suite has nine unittest methods. Its compiler method separately
builds the three probes into an isolated temporary import directory, validates
all fourteen specified axiom receipts, and checks two false numerical claims.
Those controls must fail for mathematical type mismatch; missing imports,
syntax errors or exhausted resources do not qualify. Exact stdout and stderr
are emitted separately in JSON records with source and transcript hashes.

The chronological crosscheck is byte-identical to PR #121. Its loops test
seven horizons, `n = 0,...,6`; six is its unittest-method count. The universal
whole-path proof is supplied by the new Lean source, not by extrapolation from
those finitely many examples.

The independent fraction addendum replaces three historical D-06 constant
self-comparisons with normalized finite joint paths and actual Bayesian
numerator/denominator calculations. It has twenty-five named checks and
remains finite arithmetic evidence, separate from Lean proof receipts.

## Review status

This candidate supersedes the combined implementation scope of draft PRs #121
and #122 while preserving those historical branches. It changes no acceptance
ledger. Local compilation, source review, GitHub CI and non-author independent
certification are distinct evidence stages; retain their actual dates and
commit identities rather than treating one as another.
