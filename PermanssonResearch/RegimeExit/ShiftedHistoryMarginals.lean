import PermanssonResearch.RegimeExit.ShiftedHistoryJoint
import Mathlib.Tactic

/-!
# C-Exit C — shifted canonical future state marginals

The infinite shifted-future history kernel must begin at the observed
history endpoint, and its next step must be the ORIGINAL induced Markov
kernel evaluated at that endpoint. These are necessary consistency
conditions for the whole-future last-state reduction, not sufficient
proofs of that reduction.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit

set_option autoImplicit false
open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA
variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

/-- The time-zero state of the reindexed future is exactly the
last state in the input history, even on an arbitrary measurable
joint-state space. -/
theorem shiftedHistory_zero_marginal
    (N : StrategicWorldModel S X A)
    (m : ℕ)
    (h : (i : Finset.Iic m) → JointState S X) :
    (canonicalShiftedHistoryKernel N m h).map
      (fun w : ℕ → JointState S X => w 0) =
        Measure.dirac (h ⟨m, Finset.mem_Iic.mpr le_rfl⟩) := by
  change ((canonicalHistoryContinuation N m h).map
    (pathTailShift (S := S) (X := X) m)).map
      (fun w : ℕ → JointState S X => w 0) = _
  rw [Measure.map_map (by fun_prop)
    (measurable_pathTailShift (S := S) (X := X) m)]
  have hcomp :
      (fun w : ℕ → JointState S X =>
        w m) =
        (fun q : (i : Finset.Iic m) → JointState S X =>
          q ⟨m, Finset.mem_Iic.mpr le_rfl⟩) ∘
            (Preorder.frestrictLe m) := rfl
  change (canonicalHistoryContinuation N m h).map
    (fun w : ℕ → JointState S X => w m) = _
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [canonicalHistoryContinuation_prefix N m h]
  rw [Measure.map_dirac' (by fun_prop) h]

/-- Exactly one further state after the restart obeys the frozen
one-step induced kernel, with no prefix-history dependence beyond
its endpoint. This does NOT yet prove the entire future-path law. -/
theorem shiftedHistory_one_step
    (N : StrategicWorldModel S X A)
    (m : ℕ)
    (h : (i : Finset.Iic m) → JointState S X) :
    (canonicalShiftedHistoryKernel N m h).map
      (fun w : ℕ → JointState S X => w 1) =
        N.inducedKernel (h ⟨m, Finset.mem_Iic.mpr le_rfl⟩) := by
  letI : IsMarkovKernel N.inducedKernel :=
    StrategicWorldModel.inducedKernel_isMarkov N
  let κ : (n : ℕ) →
      Kernel ((i : Finset.Iic n) → JointState S X)
        (JointState S X) :=
    fun n => StrategicWorldModel.stationaryHistoryKernel N.inducedKernel n
  change ((Kernel.traj (X := fun _ : ℕ => JointState S X)
    κ m h).map
      (pathTailShift (S := S) (X := X) m)).map
        (fun w : ℕ → JointState S X => w 1) = _
  rw [Measure.map_map (by fun_prop)
    (measurable_pathTailShift (S := S) (X := X) m)]
  have hcomp :
      ((fun w : ℕ → JointState S X => w 1) ∘
        (pathTailShift (S := S) (X := X) m)) =
        (fun w : ℕ → JointState S X => w (m+1)) := by
    funext w
    simp [pathTailShift]
  rw [hcomp]
  have hnext := congrArg
    (fun L : Kernel ((i : Finset.Iic m) → JointState S X)
       (JointState S X) => L h)
      (Kernel.map_traj_succ_self
        (X := fun _ : ℕ => JointState S X)
        (κ := κ) (a := m))
  exact hnext

end PermanssonResearch.RegimeExit
