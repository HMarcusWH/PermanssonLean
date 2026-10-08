import PermanssonResearch.ConstitutiveQuasi.PathOutput
import Mathlib.Data.Finset.Max

/-!
# D0: finite-horizon target-before-forbidden objective

A time index t includes time zero. The event succeeds when the target is
entered by t <= T and no forbidden state was entered strictly earlier.
Target and forbidden sets are disjoint. No absorbing transition assumption.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

namespace PermanssonResearch
namespace ReverseSolver

universe uY
variable {Y : Type uY} [MeasurableSpace Y]

/-- Frozen measurable target and forbidden regions of a point-started
finite-horizon reachability query. -/
structure FrozenHittingTarget (Y : Type uY) [MeasurableSpace Y] where
  goal : Set Y
  forbidden : Set Y
  goal_measurable : MeasurableSet goal
  forbidden_measurable : MeasurableSet forbidden
  disjoint : Disjoint goal forbidden

/-- The finite-prefix event for entering G no later than T, strictly
before the first entrance into D. In particular, the initial state counts. -/
def successPrefixEvent (target : FrozenHittingTarget Y) (T : ℕ) :
    Set ((i : Finset.Iic T) → Y) :=
  ⋃ t : Finset.Iic T,
    {w | w t ∈ target.goal} ∩
      ⋂ u : Finset.Iic T, {w | (u : ℕ) < (t : ℕ) → w u ∉ target.forbidden}

/-- This is an actual measurable finite-prefix event, not an outer-measure
substitute for a nonmeasurable stopping-time condition. -/
theorem measurableSet_successPrefixEvent
    (target : FrozenHittingTarget Y) (T : ℕ) :
    MeasurableSet (successPrefixEvent target T) := by
  classical
  unfold successPrefixEvent
  refine MeasurableSet.iUnion (fun t => ?_)
  refine (target.goal_measurable.preimage (measurable_pi_apply t)).inter ?_
  refine MeasurableSet.iInter (fun u => ?_)
  by_cases h : (u : ℕ) < (t : ℕ)
  · simpa [h] using
      (target.forbidden_measurable.compl.preimage (measurable_pi_apply u))
  · simp [h]

/-- Success at an initial target point is certain pathwise, independently
of any transition dynamics and the frozen horizon. -/
theorem initial_goal_mem_successPrefixEvent
    (target : FrozenHittingTarget Y) (T : ℕ)
    (w : (i : Finset.Iic T) → Y)
    (hw : w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le T)⟩ ∈ target.goal) :
    w ∈ successPrefixEvent target T := by
  classical
  unfold successPrefixEvent
  refine Set.mem_iUnion.mpr ⟨⟨0, Finset.mem_Iic.mpr (Nat.zero_le T)⟩, ?_⟩
  refine ⟨hw, Set.mem_iInter.mpr ?_⟩
  intro u
  simp

/-- D0's exact mathematical objective: success probability under the real
finite-prefix law of a fixed time-homogeneous kernel and common initial point. -/
noncomputable def hittingValue
    (target : FrozenHittingTarget Y)
    (K : Kernel Y Y) [IsMarkovKernel K] (y : Y) (T : ℕ) : ℝ :=
  (PermanssonLean.ProbabilitySupport.finitePrefixLaw K y T).real
    (successPrefixEvent target T)

theorem hittingValue_nonneg
    (target : FrozenHittingTarget Y)
    (K : Kernel Y Y) [IsMarkovKernel K] (y : Y) (T : ℕ) :
    0 ≤ hittingValue target K y T := by
  unfold hittingValue
  exact ENNReal.toReal_nonneg

end ReverseSolver
end PermanssonResearch
