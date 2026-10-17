# D2 — finite residence objectives and optimization contracts

This research lane extends D0/D1 while preserving every historical proof,
receipt, toolchain pin, application schema and v0.1.8 artifact. Acceptance is
specific to the final commit and its PR-to-main synthetic merge; this document
does not inherit another branch's green checks.

The state is fully observed and finite, controls come from the same certified
nonempty finite menus, transition rows are rational, and policies are the
unchanged admissible deterministic `HistoryPolicy` objects. Policies see the
original deadline and the complete observed past, including time zero. They
never see future observations. Randomized-policy sufficiency, arbitrary
information structures and general external alpha/P/U factorizations are not
asserted.

## Residence semantics

Freeze a target predicate G, entry deadline T and residence duration m.
Duration counts **m transitions after entry**, requiring **m+1 consecutive
target observations**. Starting in G counts as entry at zero. Failed visits
may be retried: entry means the start of any successful residence run, not
necessarily the first-ever hit of G. The exact event is

`exists e <= T, forall j <= m, Y(e+j) in G`.

It is observed through transition T+m. The completed-by-D objective instead
uses horizon D; its successful entries satisfy e+m <= D. These deadlines are
not interchangeable. Physical transitions continue normally after success;
only the event evaluation remembers the completed run.

`hasRun_iff_block` proves equality with a literal contiguous block in the
chronological path word: `word = pre ++ block ++ post`, `length block=m+1`,
and every block observation lies in G. `mem_entryByResidenceEvent_iff` proves
the entry-deadline constraint. This event definition does not mention a value
recursion or a clock. `startsRun_iff_leading`, `hasRun_iff_count` and
`residenceCount_singleton` separately prove residence-count correspondence and
correct initialization. One observation in G gives count one, hence zero
completed post-entry transitions. The Boolean hit/exit witness proves that
hitting does not establish stay-1.

## Theorem-to-source crosswalk

All new declarations are in namespace
`PermanssonResearch.ReverseSolver.Residence`.

| Anchor | Declaration and precise scope | Source |
|---|---|---|
| D2.1/2 | `reachBeforeForbidden_optimal_and_attained`: directly reuses D1's genuine typed goal-by-deadline strictly-before-forbidden probability and optimality | `ResidenceContracts.lean` |
| D2.3 event | `hasRun_iff_block`, `mem_entryByResidenceEvent_iff`: actual contiguous residence event, initial state and deadlines included | `ResidenceEvent.lean` |
| D2.3 evaluator | `objectiveProbability_eq_pathSum`, `objectivePathSum_eq_enumeration`, `objectiveEnumeration_eq_value`: genuine partialTraj event probability equals independent chronological path enumeration and backwards recursion | `ResidenceValue.lean` |
| D2.3 residence | `residenceProbability_eq_value`, `typed_residenceProbability_eq_value`: specialize to the literal residence event and transport through D1's actual full typed history law | same |
| D2.3 optimization | `objectiveValue_le_bellman`, `objectiveMaximizer_attains`, `objectiveProbability_optimal_and_attained`, `residenceProbability_optimal_and_attained`: all admissible deterministic full-history policies bounded, one admissible maximizer attains | same |
| D2.4 | Reuse C70 `RegimeExit.switchRetainEvent_prob_ge`, `proposition_4_2f_almostSure` and `proposition_4_2f_inProbability`; `eventual_switch_event_semantics` exposes the all-future retention clause | `ResidenceContracts.lean` and unchanged `RegimeExit/Proposition42f.lean` |
| D2.5 | `robust_quantifier_order_separation`: max committed randomized worst-model success 1/2, versus model-revealed-first value one | `ResidenceContracts.lean` |
| risk firewall | `hard_risk_budget_optimum`, `unconstrained_success_is_not_risk_constrained`: unconstrained maximum-success choice violates a hard risk budget | same |

The generic evaluator takes an explicit Boolean test on the final observed
history. Its probability-to-recursion bridge is proved before applying the
finite-menu maximum. D1's `completionMass`, `prefix_atom_product`, history
bijections, `bestControl` and full typed-prefix transport are reused. There is
no second trajectory-law construction. The maximizing residence policy may
depend on the whole past; it is not claimed to be Markov in the original y.

C70's eventual-switch bound needs independently certified source Exact GR,
target Exact GR under the actual intervened model, disjoint regions, a valid
original comparison set and strategic intervention with the world P held
fixed, and the actual infinite exit-routing bound with eta <= 1. Occupation
uses exactly C70's supported convergence modes; grounded PR adds eta < 1 and
all original grounding/confirmatory gates. Finite residence is not a new
Exact-GR certificate.

## Robust order and risk

The robust separation is a one-decision game. Nature commits one unobserved
model; the controller commits probability p of action a, then draws its
private randomization. One model rewards a, the other b. Nature knows p but
does not observe the realized action. Thus the committed robust value is
`max_p min(p,1-p)=1/2`; deterministic controls give zero. If the model is
revealed before policy choice, each model has value one. `IsGreatest` theorems
prove these optima over the full rational interval, not only a sampled grid.
This example makes no rectangularity assumption and supplies no robust
Bellman recursion.

The independent hard-risk example mixes safe action (.8 success, no danger)
and risky action (.9 success, .1 danger). Risk <= .05 forces risky probability
p <= .5. The constrained randomized optimum is .85 at p=.5, whereas the
unconstrained success maximizer p=1 is infeasible. It is an exact one-step
objective example, not a claim that the general residence solver enforces
arbitrary risk constraints.

## Verification and remaining scope

`test_d2_residence.py` has 17 exact-Fraction checks: exhaustive literal-window
versus forward-clock agreement, time-zero initialization, first entry from
counter zero, retries, completion memory, deadline separation, hit-versus-stay,
empty/full targets, five destructive clock mutations, true path enumeration
versus recursion over 25 rational chains, an observed-history policy,
complete deterministic-policy enumeration, product-clock versus history
optimization, robust-order separation and the hard-risk example.

The focused smoke builds all three new modules and audits every declaration.
At source `7c3e7e450f11af9913d393757a52e37e7bb4f4fa`, PR #74's focused
run `39038337508` checked synthetic merge
`bc0dc18659e22745003cdb45f8a0968029129547` against then-main
`2a2246ad851e2cdc435dcd0f98f259e1264541b3`: all three modules compiled on
Lean 4.34.0 and pinned mathlib, all 51 declarations passed the three-axiom
audit, all 17 exact tests passed, and the source firewall passed.

This candidate incorporates main
`9cf3410e9786b68f68d93c0684613329cdc9159e`, retaining C70, E1, repaired
F1 and accepted conditional A3. Fresh final-head synthetic-merge CI and review are pending; the earlier
focused result is evidence for that recorded source, not acceptance of this
combined tree.

The full Research Lean workflow must still build the research root, audit
transitive axioms, run all regressions and direct-import/source firewalls,
replay D0 goldens and execute the PR-only C10 source-bound evidence step.
The original Lean, executable and Linux/Windows application workflows remain
mandatory at the exact final head and synthetic merge.

**OPEN:** a formally proved reduction of the controller to a small product
state `(y,k,completed)`, beyond the independently tested product-clock
calculation; randomized-policy optimality; a first-ever-entry-only objective;
joint reach/avoid/residence under one objective; robust dynamic programming
with a declared rectangular uncertainty model; general hard-risk-constrained
optimization. None is silently inferred from the full-history theorem.
