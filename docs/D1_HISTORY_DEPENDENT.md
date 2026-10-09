# D1-D1 — Rational history-dependent policy dominance (PR #49)

**Status:** Mathematical proof chain implemented and verified on PR #49's
pre-documentation head. This research-only document is the implementation
and acceptance record; final-head CI, GitHub review, and merge remain
separate workflow gates. Source baseline: merged D1-C2 PR #48 at
`0953cdf3efcefa0cbaad95dfa198d4654d26df1c`.

## Mathematical contract and quantifiers

Let `sys : FiniteControlSystem C n` supply nonempty finite admissible
control menus at each state and rational stochastic matrices for each
control, and let `target : RationalHittingTarget n` have disjoint goal
and forbidden regions. A deterministic `HistoryPolicy sys` chooses
`sigma D i h` from the menu at `last h`. The prefix `h` contains
exactly the observed states from time 0 to elapsed time `i`; no future
states are exposed. The original deadline `D` remains fixed along the
run. The theory is for finite, fully observed state spaces.

The literal D0 first-hit event means entering the goal by transition
deadline D **strictly before** the forbidden region, with time-zero
membership included. A previously reached terminal event is remembered
for evaluation, even if subsequent physical transitions leave that
region; neither goal nor forbidden rows are made absorbing by the proof.

For **every** admissible deterministic complete-history policy sigma,
initial state x, and finite deadline D, the actual history-conditioned
`Kernel.partialTraj` law satisfies

    successProbability sys sigma target D x
      <= ENNReal.ofReal ((bellmanValue sys target D x : ℚ) : ℝ).

There exists an admissible history policy attaining equality, namely
`embedMarkov sys (maximizingSchedule sys target)`. This is **Markov
sufficiency for the declared first-hit objective**, not equality of
complete path laws between all history policies and Markov policies.

## Verified theorem chain

All identifiers below are Lean declarations imported by
`PermanssonResearch.lean`.

1. **Policy and genuine prefix law**
   - `HistoryPolicy.lean`: `HistoryPolicy`, `embedMarkov`,
     `chosen_mem`.
   - `HistoryPrefixKernel.lean`: admissible rational
     `selectedEntry`, normalized `historyStep`, actual
     `prefixLaw`, `prefixLaw_projective` for a **fixed original
     deadline**, and `prefixLaw_embedMarkov` (full finite-prefix
     measure equality on the embedded Markov subclass).
2. **Path atoms and literal event**
   - `HistoryPathAtoms.lean`: genuine `prefix_transition_pair`,
     `prefix_singleton_succ`, chronological `rationalPathWeight`
     and `prefix_atom_product`, including wrong-initial-point zero
     mass.
   - `HistoryEventValue.lean`: `successfulPathSum` and
     `successProbability_eq_rationalPathSum` for the **existing**
     `successPrefixEvent`, without a surrogate probability measure.
3. **Independent history continuation and event memory**
   - `HistoryContinuation.lean`: `HitStatus` (unresolved/won/lost),
     `completionMass`, `forwardValue`, total successor mass,
     `forwardValue_succ`, `forwardValue_won`,
     `forwardValue_lost`,
     `forwardValue_unresolved_le_bellman`, and
     `forwardValue_initial_le_bellman`.
     The induction covers even supplied zero-probability prefixes and
     uses no conditional division.
   - `HistoryStatusBridge.lean`:
     `foldl_status_won_iff_successPrefixEvent` proves that the
     chronological status semantics match D0's original event.
4. **Decisive probability-to-value bridge**
   - `HistoryForwardBridge.lean`:
     `completionMass_eq_rationalPathWeight` identifies independent
     successor-word weights with the genuine chronological history
     product.
   - `HistoryForwardMeasure.lean`:
     `successfulPathSum_eq_forwardValue`,
     `successProbability_eq_forwardValue`,
     `successProbability_le_bellman`, and
     `history_bellman_optimal_and_attained`. The last theorem
     quantifies over **all** admissible history policies and supplies
     an attaining witness.
5. **Attainment and adversarial witnesses**
   - `HistoryBellmanDominance.lean`:
     `history_step_bellman_upper`,
     `successProbability_embedMarkov`, and
     `embedded_maximizingSchedule_attains`.
   - `HistoryPolicyExamples.lean`:
     `embedded_deadline_five_eighths`,
     `every_deadline_schedule_le_five_eighths`,
     `deadline_bellman_optimum_five_eighths`; the existing
     three-state deadline-two Bellman optimum is **exactly 5/8**,
     not merely a witnessed lower bound. The five-state
     `reconverge_history_sensitive` example certifies different
     controls at the same current state and elapsed time after two
     distinct histories; `reconverge_left_mass` and
     `reconverge_right_mass` certify both prefixes have positive
     probability **1/2** under the genuine law.

## Verification and acceptance

The preceding implementation head
`83354689cb1e22b1187d0aad25a20b10ab3be8b5` passed all four
GitHub Actions workflows: Research Lean, Lean, Executable verification,
and Application contract (Ubuntu/Windows). Research Lean includes
building the non-default research target, its transitive axiom audit,
direct-root import coverage, research-only regression tests, D0-F
certificate replay, original-core build, and the ban on `sorry`,
`admit`, or custom axiom declarations.

**Do not infer final-head success from earlier runs.** After any
documentation/source change, check every required workflow against the
exact new head before marking the branch verified. Review findings
remain separate: no approval may be invented from successful CI.
Preserve the frozen v0.1.8 core and original release record.

## Scientific limits and next milestone

These theorems establish optimality only for this **constructed finite
rational, fully observed, deterministic admissible control family**
under its declared finite-horizon first-hit objective. They do not
prove randomized-policy sufficiency, partial-observation reduction,
arbitrary externally supplied strategic-world factorization,
real-world identification or policy efficacy, or optimization of
asymptotic generated/permannsson-regime descriptors.

D1-D2 is a separate prospective milestone: construct genuine
history-conditioned **typed** strategic-world
`alpha -> P -> U` kernels, keep the applicable P/U fixed, and prove
complete typed/rational path-law transport and first-hit optimality.
D1-D1 itself does not certify that typed transport, and a
time-varying/history policy is not silently an original frozen
`AdmissibleStrategicIntervention`.
