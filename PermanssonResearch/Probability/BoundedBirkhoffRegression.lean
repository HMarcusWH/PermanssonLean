import PermanssonResearch.Probability.BoundedBirkhoffConditional
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace PermanssonResearch.Probability.Hopf.Regression

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

def boolMeasurable : MeasurableSpace Bool := ⊤
attribute [local instance] boolMeasurable

def boolDiscrete : DiscreteMeasurableSpace Bool := ⟨fun _ => trivial⟩
attribute [local instance] boolDiscrete

def label (b : Bool) : ℝ := if b then 1 else 0

theorem label_bound (b : Bool) : |label b| ≤ 1 := by cases b <;> norm_num [label]

theorem identity_average_tendsto (b : Bool) :
    Tendsto (fun n => birkhoffAverage ℝ id label n b) atTop (𝓝 (label b)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (birkhoffAverage_apply_of_comp_eq ℝ (by rfl)
    (show (n : ℝ) ≠ 0 by exact_mod_cast (show n ≠ 0 by omega)) b).symm

theorem identity_upperAverage (b : Bool) : upperAverage id label b = label b :=
  (identity_average_tendsto b).limsup_eq

/-- A nonergodic invariant system has genuinely different pointwise limits. -/
theorem identity_limits_distinct : upperAverage id label true ≠ upperAverage id label false := by
  rw [identity_upperAverage, identity_upperAverage]
  norm_num [label]

def reset (_ : Bool) : Bool := false

theorem reset_not_injective : ¬Function.Injective reset := by
  intro h
  have hh := h (show reset true = reset false from rfl)
  contradiction

theorem reset_preserves : MeasurePreserving reset (Measure.dirac false) (Measure.dirac false) := by
  refine ⟨measurable_const, ?_⟩
  simp [reset, Measure.map_dirac]

/-- The checked theorem applies to a genuinely noninjective transformation. -/
theorem reset_conditional_time_average :
    ∀ᵐ b ∂Measure.dirac false,
      Tendsto (fun n => birkhoffAverage ℝ reset label n b) atTop
        (𝓝 (((Measure.dirac false)[label | invariantSigma reset]) b)) :=
  bounded_birkhoff_condExp reset_preserves (measurable_of_finite label)
    1 (by norm_num) label_bound

end
end PermanssonResearch.Probability.Hopf.Regression
