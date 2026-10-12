import PermanssonResearch.MultipleLimit.FiniteCanonicalConditionalStep
import PermanssonResearch.MultipleLimit.FiniteMarkovCentered
import PermanssonResearch.MultipleLimit.FiniteOccupationTelescoping
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Adapted
import Mathlib.Tactic

/-!
# C53-02 — canonical past filtration and exact centered increments

Work with the very same infinite canonical Markov trajectories used elsewhere
in C2.  The past filtration is mathlib's piLE, not a new stochastic model.
This module first certifies the filtration, its measurable coordinates, and
pathwise centered residual identities.  The further all-past conditional
integral and martingale SLLN are separate dependent proof obligations.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteMarkovMartingaleStep

open FiniteCanonicalPath
open FiniteCanonicalConditionalStep
open FiniteKernelRealBridge
open FiniteMarkovCentered
open FiniteOccupationTelescoping

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [DecidableEq Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- The canonical increasing sigma algebras on genuine infinite trajectories.
At time t they contain exactly the events measurable from Y₀,...,Yₜ. -/
def pastFiltration :
    Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Y)) :=
  Filtration.piLE (X := fun _ : ℕ => Y)

/-- An event of the natural filtration is exactly the inverse image of
a measurable finite-prefix event.  This is the bridge from the existing
canonical_joint_next_singleton theorem to full conditional means. -/
theorem past_event_iff_prefix (t : ℕ) (B : Set (ℕ → Y)) :
    MeasurableSet[pastFiltration (Y := Y) t] B ↔
      ∃ C : Set ((i : Finset.Iic t) → Y),
        MeasurableSet C ∧ Preorder.frestrictLe t ⁻¹' C = B := by
  change MeasurableSet[Filtration.piLE (X := fun _ : ℕ => Y) t] B ↔ _
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact MeasurableSpace.measurableSet_comap

/-- An individual coordinate is measurable in every subsequent past sigma
algebra; in particular there is no future-information leak. -/
theorem coordinate_measurable_at
    (s t : ℕ) (hst : s ≤ t) :
    Measurable[pastFiltration (Y := Y) t]
      (fun w : ℕ → Y => w s) := by
  change Measurable[Filtration.piLE (X := fun _ : ℕ => Y) t] _
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have hs : (fun w : ℕ → Y => w s) =
      (fun h : ((i : Finset.Iic t) → Y) =>
        h ⟨s, Finset.mem_Iic.mpr hst⟩) ∘
          (Preorder.frestrictLe t) := by
    funext w
    rfl
  rw [hs]
  have hEval :
      Measurable (fun h : ((i : Finset.Iic t) → Y) =>
        h ⟨s, Finset.mem_Iic.mpr hst⟩) :=
    measurable_pi_apply (⟨s, Finset.mem_Iic.mpr hst⟩ : Finset.Iic t)
  exact hEval.comp (comap_measurable _)

/-- True centered next-event increment of the original homogeneous kernel. -/
noncomputable def increment (z : Y) (t : ℕ)
    (w : ℕ → Y) : ℝ :=
  indicatorAt w z (t+1) - realTransition K (w t) z

/-- Exact partial sum of the genuine centered Markov innovations. -/
noncomputable def partialSum (z : Y) (T : ℕ)
    (w : ℕ → Y) : ℝ :=
  ∑ t ∈ Finset.range T, increment K z t w

theorem increment_bounded (z : Y) (t : ℕ) (w : ℕ → Y) :
    |increment K z t w| ≤ 1 := by
  simpa [increment, indicatorAt] using
    centered_increment_abs_le_one K (w t) (w (t+1)) z

theorem partialSum_eq_residual (z : Y) (T : ℕ) (w : ℕ → Y) :
    partialSum K z T w =
      transitionResidual (realTransition K) w z T := by
  rfl

theorem partialSum_zero (z : Y) (w : ℕ → Y) :
    partialSum K z 0 w = 0 := by
  simp [partialSum]

theorem partialSum_succ (z : Y) (t : ℕ) (w : ℕ → Y) :
    partialSum K z (t+1) w =
      partialSum K z t w + increment K z t w := by
  simp [partialSum, Finset.sum_range_succ]

/-- The centered increment is measurable by the *next* observation time. -/
theorem increment_measurable_at (z : Y) (t : ℕ) :
    Measurable[pastFiltration (Y := Y) (t+1)]
      (increment K z t) := by
  classical
  have hnext : Measurable[pastFiltration (Y := Y) (t+1)]
      (fun w : ℕ → Y => w (t+1)) :=
    coordinate_measurable_at (Y := Y) (t+1) (t+1) le_rfl
  have hnow : Measurable[pastFiltration (Y := Y) (t+1)]
      (fun w : ℕ → Y => w t) :=
    coordinate_measurable_at (Y := Y) t (t+1) (Nat.le_succ t)
  have hindicator : Measurable[pastFiltration (Y := Y) (t+1)]
      (fun w : ℕ → Y => indicatorAt w z (t+1)) := by
    unfold indicatorAt
    exact Measurable.ite
      (measurableSet_eq_fun hnext measurable_const)
      measurable_const measurable_const
  have htransition : Measurable[pastFiltration (Y := Y) (t+1)]
      (fun w : ℕ → Y => realTransition K (w t) z) :=
    (measurable_of_finite (fun y : Y => realTransition K y z)).comp hnow
  exact hindicator.sub htransition

/-- The cumulative innovation uses only observations through time T,
and is therefore adapted to the natural finite-history filtration. -/
theorem partialSum_measurable_at (z : Y) (T : ℕ) :
    Measurable[pastFiltration (Y := Y) T]
      (partialSum K z T) := by
  classical
  unfold partialSum
  apply Finset.measurable_fun_sum
  intro t ht
  have hst : t+1 ≤ T := Finset.mem_range.mp ht
  exact (increment_measurable_at K z t).mono
    ((pastFiltration (Y := Y)).mono hst) le_rfl

end FiniteMarkovMartingaleStep
end MultipleLimit
end PermanssonResearch
