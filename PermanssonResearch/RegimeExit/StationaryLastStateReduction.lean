import PermanssonResearch.RegimeExit.ConditionalRestartBridge
import PermanssonLean.StrategicWorld.WellPosedness
import Mathlib.Tactic

/-!
# C-Exit C — projective-limit reduction of the full last-state property

Infinite-path equality follows from equality of all genuine finite
prefix marginals under the ORIGINAL stochastic process. This is the
v0.1.8 well-posedness/projective-uniqueness theorem, not a new axiom.

The finite-prefix stationarity statement is still a mathematical
obligation. In particular, observing one or two coordinates does NOT
satisfy the quantifier over every prefix length.

**Update (C69, PR #69):** `HasCanonicalShiftedPrefixLaws N` is now PROVED
for every canonical model (`hasCanonicalShiftedPrefixLaws` in
`RegimeExit/ShiftedPrefixStationarity.lean`). No declaration here changed.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit

set_option autoImplicit false
open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA
variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

/-- The remaining finite-dimensional stationarity obligations:
for EVERY finite history and EVERY future prefix horizon, the
shifted future has the same prefix law as the canonical Dirac-point
process started at the final history state. -/
def HasCanonicalShiftedPrefixLaws
    (N : StrategicWorldModel S X A) : Prop :=
  ∀ (m : ℕ) (h : (i : Finset.Iic m) → JointState S X) (T : ℕ),
    (canonicalShiftedHistoryKernel N m h).map
        (Preorder.frestrictLe T) =
      (canonicalFutureKernel N (h ⟨m, Finset.mem_Iic.mpr le_rfl⟩)).map
        (Preorder.frestrictLe T)

/-- Every finite-dimensional prefix equality closes the ACTUAL
whole-future stationary Markov restart property by original
projective-limit measure uniqueness, with no finite-state shortcut. -/
theorem hasCanonicalLastStateRestart_of_allPrefixLaws
    (N : StrategicWorldModel S X A)
    (hPrefix : HasCanonicalShiftedPrefixLaws N) :
    HasCanonicalLastStateRestart N := by
  intro m h
  apply StrategicWorldModel.measure_eq_of_prefix_maps_eq
  intro T
  exact hPrefix m h T

end PermanssonResearch.RegimeExit
