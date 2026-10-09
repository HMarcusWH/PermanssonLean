# D1-A — finite fully observed state-feedback kernels

**Status:** Research-only PR #45; final-head Lean/CI audit pending.
Depends on merged D0-E mathematics, not on D0-F's Python report layer.
The frozen v0.1.8 core, historical paper, release evidence, toolchain, and
application contracts are not modified.

## Mathematical contract

The Lean module ControlledKernel.lean declares a finite control system with:
(a) a certified baseline rational stochastic matrix over Fin n;
(b) a finite, provably nonempty permitted set options(y) at each current state;
(c) a certified rational row-stochastic action-selection kernel for each control.

A StateFeedback policy provides a choice pi(y) and a proof that pi(y) belongs
to the permitted set at y. Its selected-row transition law is

    K_pi(y,z) = K_(pi(y))(y,z).

This is state-dependent and **stationary**, not an arbitrary time-indexed
policy pi_t(y) and not a single D0 frozen intervention held fixed globally.

## Canonical strategic-world semantics

Within the constructed Unit × Fin n research family, feedbackModel uses
the actual canonical typed alpha -> P -> U composition. The selected control
determines the action-selection law at the current joint state. The world
transition P still copies actions into the next world state, and strategic
update U is unchanged.

Proof inventory:
- feedbackMatrix_entry, feedback_entry_nonneg, feedback_row_sum_one
- constantFeedback, feedbackMatrix_constant
- feedback_preserves_world, feedback_preserves_update
- feedback_induced_encodedEntry
- feedback_agrees_with_frozen_at_state: all measurable encoded next-world events
- feedback_prefixLaw_transport: full canonical prefix-law pushforward
- feedback_typed_hitting_value: all-horizon exact typed/rational event equality

Equality to a frozen replacement is **at one current state only**; it does not
assert feedback trajectories equal a single frozen intervention's path law.

## Nontrivial two-transition counterexample

Three states: 0 start, 1 bridge, 2 goal.

- False control moves 0 -> 1 and leaves 1 fixed.
- True control leaves 0 fixed and moves 1 -> 2.
- Feedback chooses false at 0 and true at 1.

Both fixed controls have zero goal-hitting probability from 0 at horizon 2.
The state-feedback policy reaches goal by horizon 2 with probability 1.
Lean proves the separation both for exact rational values and the genuine
canonical typed finite-prefix target probabilities. World P and update U
are proved unchanged.

## Scope

Research-only constructed family with permissive action-selection choices.
No arbitrary externally supplied strategic-world factorization or
identification, no Bellman optimality, no controller synthesis over horizon-
dependent policies, no reduction of history-dependent policies, and no
real-world effectiveness claim. These are independent D1 follow-up tasks.

D1-B: finite-horizon Bellman value recursion and correctness for a finite
fully observed Markov-control class.
D1-C: synthesizing a maximizing time-dependent policy and proving its
nonstationary forward probability law.
D1-D: history-dependent-policy reduction if proved and general typed
finite-world admissibility extensions.

Reproduce on the pinned Lean/mathlib toolchain:

    lake build PermanssonResearch
    lake build

Research Lean CI additionally audits transitive axioms, import coverage
and absence of proof placeholders/custom axioms. All four preexisting
repository workflows must pass at the PR's exact final head.
