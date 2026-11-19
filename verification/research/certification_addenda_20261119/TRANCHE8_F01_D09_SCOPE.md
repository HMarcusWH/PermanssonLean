# Tranche 8 — F-01 and D-09 source-bound evidence

This addendum extends the case-specific technical evidence used to prepare the
mathematical reference guide. It changes no certification decision. The source
specification pins 21 existing files and declares every requested name and false
control. The 56 audited declarations belong to **two cases**; they are distinct
from the separate 56-case certification programme.

## F-01: preserve the original criterion

The receipt has 37 named declarations: 10 new proved facts and 27 existing
declarations. It includes the actual asymmetric physical/common fixture, its
point and non-Dirac canonical transports, generic private/common/physical row
pullbacks, distinct nonconstant Bool-private updates, and named facts importing
the original unchanged Fin3 fixture.

The general player-swap path-law theorem retains finite-coordinate and
measurable-singleton premises. The indexed-to-binary reduction theorem is for
Fin2. The Fin3 witness supplies actual three-player protocol rows; it does not
establish a general three-to-two reduction. The matched measurable protocol
theorems are for conditional-product Fin2 generators, with the declared anchors,
pulled-back property and comparison-set hypotheses. Arbitrary correlated
protocols are outside this scope.

The all-initial-law statements allow an arbitrary probability measure on the
declared joint state, including correlated initial coordinates. The conditional
product restriction concerns the mechanisms, not independence of that initial
measure.

Three false controls reject omitted physical/common input reindexing, omitted
private-update input reindexing, and substitution of the open-loop physical
value for the original Fin3 closed-loop value.

## D-09: retain two separate models and observables

The receipt has 19 existing declarations: 18 theorems and the concrete
`booleanClassFunctional` definition. Twelve declarations concern the original
two-absorbing physical-class family; seven concern the separate native
deterministic phase-blind policy comparison.

For the two-absorbing family, equal constant-descriptor targets do not erase
physical-class identity. The nonlinear-score calculation uses the separately
specified `observedPhysicalBool` observable: its equal-weight original mixed-law
expectation is 1/2, whereas scoring the stationary barycenter gives 5/6.

For the native phase-blind family at the original fixed point start `(0, false)`,
deterministic stationary physical-only `Bool → Bool` policies score at most 5/6,
an attainer reaches 5/6, and the specific
phase-aware policy scores 1. This does not prove universal optimality over
randomized or history-dependent policies. The phase-aware policy is stationary
on its augmented native state.

Three false controls reject collapse of the two physical classes, replacement
of the actual mixed-law score by its barycenter score, and inflation of the
native phase-blind attainer to 1.

## Reproduce

Use the repository's pinned Lean 4.34.0 and unchanged manifest:

```sh
lake build PermanssonResearch.MultiAgent.MeasurableProductTwoMatchedExamples PermanssonResearch.MultiAgent.FiniteProductTwo PermanssonResearch.ReverseSolver.NonlinearMultichainAggregationFixture PermanssonResearch.ReverseSolver.NonlinearPhaseBlindClassGeometry
python3 -m unittest verification.research.test_cert_tranche8_f01_d09_scope_addendum -v
```

The suite has three unittest methods, 56 named declaration receipts and six
semantic controls. These are separate counts. The compiler harness first builds
the unchanged verification-only Fin3 fixture in an isolated temporary module
tree, then compiles the positive probe before checking its negative controls.
All requested names must have exactly one permitted-axiom receipt. Missing
imports, malformed source, resource exhaustion and unrelated elaboration errors
invalidate a negative run.

`TRANCHE8_COMPILER_STAGE` preserves each exact stdout/stderr transcript and hash.
`TRANCHE8_CASE_RECEIPT` records the case, actual checkout, worktree state,
specification hash, observed frozen-source hashes, complete axiom map and
classified controls. Integration and CI status must be read from the receipt
and associated PR/run; source existence alone does not establish either.

The independent fraction addendum remains a separate explicit command:

```sh
python3 verification/research/certification_addenda_20261119/Independent_Fraction_Crosschecks_Addendum.py
```

Its 25 arithmetic checks are not discovered by the workflow's `test_*.py`
unittest pattern. A library build alone also does not compile the verification
probes; run the stated unittest harness.

Original acceptance criteria, source review, compiler execution, GitHub CI,
integration, and non-author certification review are separately recorded.
