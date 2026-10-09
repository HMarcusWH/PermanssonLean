# D1-B — Finite-horizon Bellman optimality (research only)

**Status:** PR #46, subject to final-head Lean CI and review gates.
**Base:** D1-A (#45) on main. Frozen v0.1.8 and historical release evidence stay untouched.

## Exact mathematical object

A system from D1-A supplies a nonempty finite permissible control set at
each state and an exact rational stochastic matrix for each control.

The one-step score of choosing control c in state y with continuation v is

    score(v,y,c) = sum_z K_c(y,z) * v(z).

Bellman.lean uses the Mathlib result Finset.exists_max_image to obtain an
admissible maximizing control in each local finite nonempty menu. It does
not require a globally finite control universe. The Bellman recursion is:

    V_0(y) = 1 when y is in G, otherwise 0.
    V_(t+1)(y) = 1, y in G;
                   0, y in D;
                   max_(c in C(y)) score(V_t,y,c), otherwise.

G and D are disjoint. Their terminal status is only for hitting-event value
evaluation: no underlying transition row is silently replaced.

## Time-dependent Markov schedule

BellmanPolicyValue.lean defines MarkovSchedule as a function taking a
number of transitions REMAINING to a full admissible StateFeedback selector.
The action used at t+1 remaining transitions is that schedule's t+1 rule,
before the first transition. The continuation uses the t rule.

This is NOT the same as the D1-A constantFeedback construction:
stationarySchedule repeats one STATE-DEPENDENT policy at every time index,
whereas constantFeedback selects a single control globally.

The exact rational policyValue function is an algebraic recursion, not yet
a certified nonstationary canonical trajectory measure.

## Mathematical theorems

- Every Bellman value lies in [0,1].
- The selected admissible control attains the finite one-step maximum.
- For all deterministic admissible remaining-horizon Markov schedules pi,
  all horizons T and states y, policyValue(pi,T,y) <= V_T(y).
- A single remaining-horizon-indexed maximizing schedule attains equality
  for every T and y simultaneously.
- Boundary cases include T=0, goal at start, forbidden at start,
  empty goal, and the no-forbidden reachability recursion.
- A nonempty unreachable goal witness demonstrates value zero at state 0.
- A stationary schedule's exact recursive value equals the corresponding
  D1-A rational value and the actual canonical typed hitting value.

## Deadline-sensitive counterexample

Three states 0=start, 1=goal, 2=forbidden.
Control A at 0: 1/4 success, 3/4 return to 0.
Control B at 0: 1/2 success, 1/2 forbidden.
Other states remain fixed.

At horizon 2, A first and B with one transition remaining gives 5/8.
Stationary deterministic feedback choices at state 0 give exactly 7/16
(always A at 0) or 1/2 (always B at 0). The strong Lean claim quantifies
over *all deterministic stationary state-feedback policies*, not merely
globally constant controls. Randomized stationary policies are not part
of the proved policy class.

## Boundaries and next PR

This is an exact rational recursive optimality result in the explicitly
constructed finite control family; it does NOT yet establish a nonstationary
canonical finite-prefix law for arbitrary time-dependent schedules.
D1-C (#47) should construct that path law and prove it equals policyValue.
A history-dependent policy reduction, randomized policies, and arbitrary
externally specified strategic-world P/U remain separate proof obligations.
No claim of a universal intervention optimum or empirical effectiveness.

## Verification

Run lake build PermanssonResearch and lake build. The existing Research Lean
workflow also audits transitive axioms, all direct module imports, the
proof-placeholder/custom-axiom firewall and research rational regressions.
Require all four original repository workflows green at exact final HEAD,
and incorporate automated code review before merging.
