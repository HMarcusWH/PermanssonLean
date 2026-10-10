# D1-D2 — Genuine typed complete-history control transport (PR #50)

**Status: implementation branch, draft until final-head CI and review pass.**
Base: merged D1-D1 PR #49 (`aaa7bd56e723b139af7f5d12fa6c2360b76a0d8e`).

## Scope and mathematical objective

Given a constructed finite fully observed rational `FiniteControlSystem C n`,
an admissible deterministic `HistoryDependent.HistoryPolicy sys`, an
original deadline D and time i, the next typed state is drawn from the
actual `StrategicWorldModel.inducedKernel` of the fully typed
`Unit × Fin n` feedback model selected by the **entire observed prefix**.

The complete prefix `H : TypedHistory n i` is encoded using the existing
D0-E `prefixEncode i`. A globally admissible `StateFeedback` is
constructed from the policy's control at its current last encoded state,
using the local nonempty menus to fill in all other states. Those filler
controls must not affect the selected transition row.

For all admissible policies, deadlines, initial states and prefix lengths,
prove equality of the **actual finite-prefix probability measures**:

    (HistoryDependentTyped.typedPrefixLaw sys sigma D x t).map
      (prefixEncode t) =
      HistoryDependent.prefixLaw sys sigma D x t

No time-dependent process is silently identified with one frozen original
intervention. The original deadline is held fixed when taking prefixes.

## Proof chain

- `HistoryTypedFeedback.lean`: admissible history-to-feedback lift,
  exact selected current-state control, row and complete selected-measure
  independence from other-state fillers.
- `HistoryTypedKernel.lean`: canonical `alpha -> P -> U` induced typed
  history kernel, fixed P and fixed U at every history, normalization,
  full measurable-event encoded one-step equality for **all** histories.
- `HistoryTypedPrefix.lean`: genuine typed Mathlib `Kernel.partialTraj`
  prefix law, time-zero Dirac, probability normalization and same-original-
  deadline projectivity.
- `HistoryTypedAtoms.lean`: actual typed history prefix/transition
  decomposition and singleton recurrence.
- `HistoryTypedTransport.lean`: all-prefix typed/rational atom equality
  followed by measure extensionality on the finite complete history space.
- `HistoryTypedHitting.lean`: the unchanged original D0 first-hit
  event under typed trajectories; exact typed/rational event probability,
  universal typed history-policy Bellman upper bound and attaining embedded
  D1-B Markov witness.
- `HistoryTypedExamples.lean`: exact typed 5/8 benchmark and
  reachable positive-mass history separation. Two histories (0,1,0)
  and (0,2,0) reconverge at state 0 at elapsed time 2; under the genuine
  typed kernel they choose different controls leading surely to
  goal 3 or forbidden 4 respectively.

## Key scientific nonclaims

- Not a theorem about arbitrary externally supplied `alpha/P/U` worlds:
  the typed models are constructed, with P copying the action and U
  updating trivial `Unit` strategic memory.
- No modification of P or U, even implicitly to encode controller memory.
  The **policy** observes an external history of joint states.
- No partially observed or randomized policy reduction; no arbitrary
  infinite-horizon regime or empirical causal conclusion.
- Hitting events are terminal for **evaluation** only, never by mutation
  of the world's physical transition kernel.
- The exact rational D1-D1 Bellman theorem is reused; not re-proven via
  hypothetical probabilities or numerical approximation.

## Acceptance

Do not mark complete until ALL exact final-head GitHub workflows pass:
`Research Lean` (including direct import coverage, transitive axiom
audit and research regression replay), `Lean`, `Executable verification`,
and `Application contract`. No `sorry`, `admit` or new axioms;
keep `PermanssonLean/`, `PermanssonLean.lean`, paper/release snapshot
and pinned toolchain unchanged. Address code review before merge.
