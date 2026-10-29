import PermanssonResearch.Quotient.DiscountedCanonicalMarginClosure
import PermanssonResearch.Quotient.DiscountedOriginalMarginExamples
import Mathlib.Tactic

/-!
Exact discounted arithmetic adversaries. These facts inspect literal
closed-form model-output envelopes. They do not establish Exact GR or
identify the physical source kernels for an arbitrary outside model.
-/
namespace PermanssonResearch.Quotient.DiscountedCanonicalWitnessExamples
open PermanssonResearch.Quotient.DiscountedOriginalMargin
open PermanssonResearch.Probability

theorem correct_frozen_discounted_budget :
    (∑' n : ℕ, (1-(1/3:ℝ))*(1/3:ℝ)^n*
      (1-(1-(1/5:ℝ))*(1-(1/4:ℝ))^n)) = 13/45 :=
  exact_thirteen_fortyfive_budget

/-- A well-formed but wrong rational literal cannot be substituted for the
true stationary discounted defect bound. -/
theorem wrong_frozen_discounted_budget :
    (∑' n : ℕ, (1-(1/3:ℝ))*(1/3:ℝ)^n*
      (1-(1-(1/5:ℝ))*(1-(1/4:ℝ))^n)) ≠ 14/45 := by
  rw [correct_frozen_discounted_budget]
  norm_num



namespace SourceBoundExactWitness
open PermanssonLean
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open PermanssonResearch.Probability.DependentHistory
open PermanssonResearch.Quotient.DiscountedCanonicalMarginClosure

variable {S X A Sb Xb Ab : Type*}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace Sb] [MeasurableSpace Xb] [MeasurableSpace Ab]

/-- The zero-leakage case is constructed from the REAL source Markov kernel
and a proved exact projection intertwining, not from an assumed TV bound. -/
noncomputable def exactKernelPointWitness
    (Qc : TypeRespectingStateCompression S X Sb Xb)
    (M : StrategicWorldModel S X A)
    (Mbar : StrategicWorldModel Sb Xb Ab)
    (hK : KernelIntertwines Qc M.inducedKernel Mbar.inducedKernel) :
    PointWitness Qc M Mbar where
  R := M.inducedKernel
  R_finite := by
    letI : IsMarkovKernel M.inducedKernel :=
      StrategicWorldModel.inducedKernel_isMarkov M
    infer_instance
  R_sub := le_rfl
  R_projected := le_of_eq hK
  eta := fun _ => 0
  eta_nonneg := by intro n; norm_num
  eta_le_one := by intro n; norm_num
  retention := by
    letI : IsMarkovKernel M.inducedKernel :=
      StrategicWorldModel.inducedKernel_isMarkov M
    intro n y
    simpa using (show (1 : ℝ≥0∞) ≤ M.inducedKernel y Set.univ from by simp)

/-- Every horizon of this source-derived witness retains full mass. -/
theorem exactKernelPointWitness_retained_one
    (Qc : TypeRespectingStateCompression S X Sb Xb)
    (M : StrategicWorldModel S X A)
    (Mbar : StrategicWorldModel Sb Xb Ab)
    (hK : KernelIntertwines Qc M.inducedKernel Mbar.inducedKernel)
    (n : ℕ) :
    retained (exactKernelPointWitness Qc M Mbar hK).eta n = 1 := by
  simp [exactKernelPointWitness, retained]

/-- A genuinely type-respecting identity projection, used to regression-test
that no fictitious error can be inserted at a matched point start. -/
def identityStateCompression (S X : Type*) [MeasurableSpace S]
    [MeasurableSpace X] : TypeRespectingStateCompression S X S X where
  strategic := id
  world := id
  strategic_measurable := measurable_id
  world_measurable := measurable_id
  strategic_surjective := Function.surjective_id
  world_surjective := Function.surjective_id

theorem identity_canonical_full_path
    (M : StrategicWorldModel S X A)
    (μ : Measure (JointState S X)) [IsProbabilityMeasure μ] :
    (M.pathLaw μ).map (identityStateCompression S X).pathMap =
      M.pathLaw μ := by
  have hmap : (identityStateCompression S X).pathMap =
      (id : (ℕ → JointState S X) → (ℕ → JointState S X)) := by
    funext w n
    rfl
  rw [hmap]
  simp

end SourceBoundExactWitness

end PermanssonResearch.Quotient.DiscountedCanonicalWitnessExamples
