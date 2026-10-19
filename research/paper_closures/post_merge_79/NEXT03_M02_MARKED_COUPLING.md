# NEXT-03 / M-02 — marked versus unmarked coupling

## Concrete typed construction

The existing `FiniteProbabilityLaw` record is instantiated on the
**actual pair** (common/opponent key, sampled opponent action) with four
possible Boolean atoms. Two distinct complete, nonnegative, normalized
probability laws assign mass 1/2 to key/action aligned or key/action crossed
atoms, respectively.

All unmarked key marginals agree and equal 1/2 for each key. The diagonal
event `{(key, action) | key=action}` has probability 1 under the aligned law
and probability 0 under the crossed law. It witnesses event total variation
1. The independent exact rational test also calculates the half-L1 total
variation as 1 on all four marked atoms.

## Honest acceptance boundary

This is a genuine Lean **finite probability law** fixture and a concrete
M-02 information-loss counterexample. It does not instantiate the full
`TwoPlayerGenerator` conditional-product history, prove the structural
autonomous restrictions, or replace the original `AutonomousMarkedKernel`
hypotheses with equality of unmarked key laws. That remaining application
routing remains open.

No original F1 theorem, frozen strategic generator, dependency pin,
accepted release, or prior historical negative result is changed.
Pinned Lean/compiler CI, transitive axiom and source review are mandatory.
