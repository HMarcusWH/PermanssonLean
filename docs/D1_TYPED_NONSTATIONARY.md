# D1-C2 — Genuine typed nonstationary alpha/P/U path-law transport

**PR #48 (research-only; CI verification required).**
Base: D1-C1 (#47), merged. Frozen v0.1.8 and historical release evidence
are outside the change surface.

## Mathematical contract

The complete finite-horizon Markov schedule is deterministic, fully observed
and state-dependent. Controls are selected from D1-A's finite nonempty local
admissibility menu. The controlling clock is the number of transitions
REMAINING. Fix initial deadline D. At elapsed step i the feedback controller
is pi(D-i). For physical transitions i<D, the selected typed strategic-world
model is feedbackModel sys (pi (D-i)).

The selected typed kernel is the actual StrategicWorldModel.inducedKernel
from the original canonical alpha -> P -> U integration order. It is not a
new rational table presented as a typed model and is not a single frozen
AdmissibleStrategicIntervention.

At EVERY step P is literally the baseline copiedActionWorld and U is
literally the baseline trivialStrategicUpdate of the Unit × Fin n realized
finite-world family. Only the action-selection alpha changes with the
feedback choice. No statement is made about arbitrary externally specified
world transition or update kernels.

The actual typed prefix measure is Mathlib Kernel.partialTraj composed from
those chronological induced kernels. For every original deadline D,
initial world point x and prefix length t (in particular all t <= D):

    (typedPrefixLaw sys pi D x t).map (prefixEncode t)
       = Nonstationary.prefixLaw sys pi D x t.

The proof establishes full finite-path measure equality (all measurable
sets) from atomwise equality using a typed transition recurrence and the
existing D0-E prefixEncode/prefixDecode bijection. Point-mass initial
conditions, Markov normalization, and prefix restriction are verified.

The SAME original deadline is preserved when restricting to a shorter
observed prefix. The claim is not cross-deadline projectivity; D1-C1's
deadline-sensitive counterexample gives a formal counterexample to that
stronger and generally false equation.

## First-hit event

Use the existing measurable D0 successPrefixEvent, including time zero
and reaching the goal strictly before an earlier forbidden visit. Preserve
goal/forbidden as terminal for value evaluation ONLY; no transition kernel
is physically changed to make those states absorbing.

The typed event is the established D0-E typedTarget. Its preimage under
prefixEncode is the rational successPrefixEvent. Hence typed event
probability equals D1-C1's rational probability, and by its certified
first-hit correspondence equals the D1-B exact policyValue.

Transport D1-B's universal finite-horizon deterministic Markov-policy
upper bound and its attaining maximizingSchedule onto this ACTUAL
time-dependent typed strategic-world probability measure.

## Regression contract

* Full typed/rational prefix measure identity for every deadline and
  prefix length.
* Stationary feedback specialization equals D1-A's original canonical
  finitePrefixLaw.
* Initial typed state is a Dirac point mass at time zero.
* Deadline-dependent three-state example: true typed success 5/8 by T=2.
* Typed prefix laws from initial deadlines 1 and 2 are provably different.
* Every step preserves baseline P and U.

## Scientific boundary

This certifies the constructed Unit × Fin n realization under
deterministic admissible remaining-horizon Markov schedules. It does NOT
prove history-dependent reduction, randomized-policy optimality, any
partially observed result, or admissibility of a time-varying policy as
a single original frozen intervention. General externally specified
strategic-world alpha/P/U models require separate realization proof.

## Acceptance

The exact PR head must pass all four CI workflows, full Lean compilation
of all imported research modules, transitive axiom audit, no sorry/admit
or new axioms, import coverage, and source firewall. Code review findings
must be addressed when available.
