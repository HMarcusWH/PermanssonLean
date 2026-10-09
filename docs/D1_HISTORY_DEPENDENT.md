# D1-D1 — Rational history-dependent policy dominance (PR #49)

**Current status: IN PROGRESS, DRAFT.** This document distinguishes the
proved foundational lemmas in the proposed branch from the remaining theorem
obligations; it must not be read as asserting PR #49 is certified.

Base: merged D1-C2 PR #48 (main `0953cdf3efcefa0cbaad95dfa198d4654d26df1c`).

## Mathematical target

For the constructed finite fully observed `FiniteControlSystem`, allow
deterministic history-dependent policy `sigma D i h`, where the complete
observed prefix `h` has coordinates `0..i` and the chosen control belongs
to the local menu of its last state. The policy cannot observe any future
state. P and U remain part of the *separate* typed realization (D1-D2);
this PR concerns the exact rational family only.

The target theorem is first-hit event probability dominance over EVERY
admissible history policy by D1-B's `bellmanValue sys target D x`, together
with attainment through `embedMarkov sys (maximizingSchedule sys target)`.

## Implemented foundations (subject to exact final-head CI)

- `HistoryPolicy`: complete-prefix admissible selectors and Markov embedding.
- `HistoryPrefixKernel`: actual history-conditioned stochastic rows,
  Mathlib `Kernel.partialTraj`, same-original-deadline projectivity and
  complete prefix measure equality for embedded Markov schedules.
- `HistoryPathAtoms`: finite-prefix transition pair, exact atom recurrence
  and product of chronology-specific rational rows.
- `HistoryEventValue`: the ORIGINAL D0 first-hit event probability equals
  the exact sum of rational weights of all successful paths.
- `HistoryBellmanDominance`: admissibility-dependent ONE-STEP Bellman
  bound and attainment of Bellman by an embedded maximizing policy.
  **No universal multi-step history-policy dominance is yet proved.**
- `HistoryPolicyExamples`: D1-C1's authentic 5/8 event mass through the
  Markov-to-history embedding.

## Outstanding acceptance obligations

1. Define a continuation evaluator from an arbitrary supplied history,
   with already-won/already-lost/unresolved behavior matching the original
   success-before-forbidden event (including future visits after success).
2. Prove exact equality of continuation evaluation and the genuine
   `partialTraj` event probability, without dividing by a prefix of
   possibly zero measure.
3. Prove universal multi-step Bellman dominance by induction over remaining
   transitions, and the full Markov-sufficiency theorem.
4. Certify the exact 5/8 Bellman OPTIMUM (not merely the performance of a
   particular policy), reachable-history reconvergence, terminal-memory
   behavior, unreachable/empty targets and original-deadline counterexample.
5. Pass all four workflows, direct import coverage, axiom audit, regression
   tests, source firewall, and resolve code review on the **final** head.

## Exclusions

No history-dependent typed alpha/P/U transport (reserved D1-D2), partial
observation, randomized policy reduction, arbitrary externally supplied
world primitives, empirical validity or revision of the frozen v0.1.8 core.
