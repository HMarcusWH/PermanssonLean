import PermanssonResearch.Quotient.Q05ActualAtomClosure
import PermanssonResearch.MultipleLimit.CanonicalKernelMarginals
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic

/-!
# Q-05 addendum: canonical whole-path output identification

The marginal calculation below starts with the original alpha/P/U induced
kernel and the original canonical infinite path law.  It does not substitute
an independent-coordinate process or an assumed transition matrix.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

namespace PermanssonResearch.Quotient.Q05WholePathIdentification

open PermanssonLean
open PermanssonLean.RegimeSpecification
open PermanssonResearch.Probability
open PermanssonResearch.X1 (coin coin_true coin_false)
open PermanssonResearch.MultipleLimit.FiniteCanonicalPath
open PermanssonResearch.MultipleLimit.CanonicalKernelMarginals
open PermanssonResearch.Quotient.DiscountedCanonicalBridge
open PermanssonResearch.Quotient.DiscountedOriginalMargin
open PermanssonResearch.Quotient.Q05ActualOriginalMarginWitnessFixture
open PermanssonResearch.Quotient.Q05ActualOriginalMarginAdapter
open PermanssonResearch.Quotient.Q05ActualAtomClosure

set_option autoImplicit false
attribute [local instance] StrategicWorldModel.inducedKernel_isMarkov

theorem coin_weights_sum (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) :
    ENNReal.ofReal (p : ℝ) + ENNReal.ofReal ((1-p : ℚ) : ℝ) = 1 := by
  have hp0 : 0 ≤ (p : ℝ) := by exact_mod_cast hp.1
  have hq0 : 0 ≤ ((1-p : ℚ) : ℝ) := by exact_mod_cast sub_nonneg.mpr hp.2
  rw [← ENNReal.ofReal_add hp0 hq0]
  have hsum : (p : ℝ) + ((1-p : ℚ) : ℝ) = 1 := by push_cast; ring
  rw [hsum]
  norm_num

/-- Integrating an arbitrary nonnegative score against the actual fine row.
The two terms are derived from the already proved typed singleton atoms. -/
theorem fine_induced_lintegral (t : Bool) (y : FineState)
    (f : FineState → ℝ≥0∞) :
    (∫⁻ z, f z ∂(fineModel t).inducedKernel y) =
      f (t, true) * ENNReal.ofReal (fineActionRate t y.1 : ℝ) +
      f (t, false) * ENNReal.ofReal ((1-fineActionRate t y.1 : ℚ) : ℝ) := by
  rw [lintegral_fintype]
  simp_rw [fine_induced_singleton]
  cases t <;>
    simp [Fintype.sum_prod_type, coin_true, coin_false]

theorem coarse_induced_lintegral (t : Bool) (y : CoarseState)
    (f : CoarseState → ℝ≥0∞) :
    (∫⁻ z, f z ∂(coarseModel t).inducedKernel y) =
      f ((), true) * ENNReal.ofReal (coarseActionRate t : ℝ) +
      f ((), false) * ENNReal.ofReal ((1-coarseActionRate t : ℚ) : ℝ) := by
  rw [lintegral_fintype]
  simp_rw [coarse_induced_singleton]
  simp [Fintype.sum_prod_type, coin_true, coin_false]

/-- After one update the fine strategic coordinate is t, so one further
transition has the same law for every original starting state. -/
theorem fine_two_step_row (t : Bool) (y : FineState) :
    (fineModel t).inducedKernel ∘ₘ (fineModel t).inducedKernel y =
      (fineModel t).inducedKernel (t, false) := by
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.bind_apply (measurableSet_singleton z) (Kernel.aemeasurable _),
    fine_induced_lintegral]
  simp_rw [fine_induced_singleton]
  rw [← mul_add, coin_weights_sum _ (fineActionRate_bounds t y.1), mul_one]

theorem coarse_two_step_row (t : Bool) (y : CoarseState) :
    (coarseModel t).inducedKernel ∘ₘ (coarseModel t).inducedKernel y =
      (coarseModel t).inducedKernel ((), false) := by
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.bind_apply (measurableSet_singleton z) (Kernel.aemeasurable _),
    coarse_induced_lintegral]
  simp_rw [coarse_induced_singleton]
  rw [← mul_add, coin_weights_sum _ (coarseActionRate_bounds t), mul_one]

theorem typed_marginal_succ
    {S X A : Type*} [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    (M : StrategicWorldModel S X A) (y : JointState S X) (n : ℕ) :
    (M.pathLaw (Measure.dirac y)).map (fun w => w (n+1)) =
      M.inducedKernel ∘ₘ (M.pathLaw (Measure.dirac y)).map (fun w => w n) := by
  rw [typed_pathLaw_eq_canonical]
  exact canonical_eval_succ M.inducedKernel (Measure.dirac y) n

theorem typed_marginal_one
    {S X A : Type*} [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSingletonClass (JointState S X)]
    (M : StrategicWorldModel S X A) (y : JointState S X) :
    (M.pathLaw (Measure.dirac y)).map (fun w => w 1) = M.inducedKernel y := by
  rw [show (1 : ℕ) = 0+1 by rfl, typed_marginal_succ, canonical_point_start_zero]
  exact Measure.dirac_bind (Kernel.measurable M.inducedKernel) y

/-- All infinitely many canonical fine marginals from time two onward. -/
theorem fine_marginal_after_two (t : Bool) (y : FineState) (n : ℕ) :
    ((fineModel t).pathLaw (Measure.dirac y)).map (fun w => w (n+2)) =
      (fineModel t).inducedKernel (t, false) := by
  induction n with
  | zero =>
      rw [show 0+2 = 1+1 by rfl, typed_marginal_succ, typed_marginal_one,
        fine_two_step_row]
  | succ n ih =>
      rw [show n.succ+2 = (n+2)+1 by omega, typed_marginal_succ, ih,
        fine_two_step_row]

/-- All infinitely many canonical coarse marginals after the initial state. -/
theorem coarse_marginal_after_one (t : Bool) (x : Bool) (n : ℕ) :
    ((coarseModel t).pathLaw (Measure.dirac ((), x))).map (fun w => w (n+1)) =
      (coarseModel t).inducedKernel ((), false) := by
  induction n with
  | zero =>
      rw [typed_marginal_one]
      apply Measure.ext_of_singleton
      intro z
      simp only [coarse_induced_singleton]
  | succ n ih =>
      rw [show n.succ+1 = (n+1)+1 by omega, typed_marginal_succ, ih,
        coarse_two_step_row]

theorem fine_induced_world_integral (t : Bool) (y : FineState) :
    (∫ z, (if z.2 then 1 else 0 : ℝ) ∂(fineModel t).inducedKernel y) =
      (fineActionRate t y.1 : ℝ) := by
  rw [integral_fintype (Integrable.of_finite)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Measure.real_def,
    fine_induced_singleton]
  cases t <;> cases y with
  | mk s x =>
      cases s <;>
        norm_num [coin_true, coin_false, fineActionRate, smul_eq_mul]

theorem coarse_induced_world_integral (t : Bool) (y : CoarseState) :
    (∫ z, (if z.2 then 1 else 0 : ℝ) ∂(coarseModel t).inducedKernel y) =
      (coarseActionRate t : ℝ) := by
  rw [integral_fintype (Integrable.of_finite)]
  simp [Fintype.sum_prod_type, Measure.real_def,
    coarse_induced_singleton, coin_true, smul_eq_mul,
    ENNReal.toReal_ofReal (show 0 ≤ (coarseActionRate t : ℝ) by
      exact_mod_cast (coarseActionRate_bounds t).1)]

theorem coordinate_integral {Y : Type*} [MeasurableSpace Y]
    (μ : Measure (ℕ → Y)) (f : Y → ℝ) (hf : Measurable f) (n : ℕ) :
    (∫ w, f (w n) ∂μ) = ∫ y, f y ∂μ.map (fun w => w n) :=
  (integral_map (measurable_pi_apply n).aemeasurable hf.aestronglyMeasurable).symm

theorem fine_world_mean_zero (t : Bool) (s x : Bool) :
    (∫ w, (if (w 0).2 then 1 else 0 : ℝ)
      ∂(fineModel t).pathLaw (Measure.dirac (s,x))) = (if x then 1 else 0) := by
  have h := canonical_point_start_zero (fineModel t) (s,x)
  have hm : Measurable (fun z : FineState => (if z.2 then 1 else 0 : ℝ)) :=
    Measurable.of_discrete
  rw [coordinate_integral _ (fun z : FineState => (if z.2 then 1 else 0 : ℝ)) hm 0,
    h, integral_dirac]

theorem fine_world_mean_one (t : Bool) (y : FineState) :
    (∫ w, (if (w 1).2 then 1 else 0 : ℝ)
      ∂(fineModel t).pathLaw (Measure.dirac y)) = (fineActionRate t y.1 : ℝ) := by
  have hm : Measurable (fun z : FineState => (if z.2 then 1 else 0 : ℝ)) :=
    Measurable.of_discrete
  rw [coordinate_integral _ (fun z : FineState => (if z.2 then 1 else 0 : ℝ)) hm 1,
    typed_marginal_one, fine_induced_world_integral]

theorem fine_world_mean_after_two (t : Bool) (y : FineState) (n : ℕ) :
    (∫ w, (if (w (n+2)).2 then 1 else 0 : ℝ)
      ∂(fineModel t).pathLaw (Measure.dirac y)) = (fineActionRate t t : ℝ) := by
  have hm : Measurable (fun z : FineState => (if z.2 then 1 else 0 : ℝ)) :=
    Measurable.of_discrete
  rw [coordinate_integral _ (fun z : FineState => (if z.2 then 1 else 0 : ℝ)) hm (n+2),
    fine_marginal_after_two, fine_induced_world_integral]

theorem coarse_world_mean_zero (t : Bool) (x : Bool) :
    (∫ w, (if (w 0).2 then 1 else 0 : ℝ)
      ∂(coarseModel t).pathLaw (Measure.dirac ((),x))) = (if x then 1 else 0) := by
  have hm : Measurable (fun z : CoarseState => (if z.2 then 1 else 0 : ℝ)) :=
    Measurable.of_discrete
  rw [coordinate_integral _ (fun z : CoarseState => (if z.2 then 1 else 0 : ℝ)) hm 0,
    canonical_point_start_zero, integral_dirac]

theorem coarse_world_mean_after_one (t : Bool) (x : Bool) (n : ℕ) :
    (∫ w, (if (w (n+1)).2 then 1 else 0 : ℝ)
      ∂(coarseModel t).pathLaw (Measure.dirac ((),x))) = (coarseActionRate t : ℝ) := by
  have hm : Measurable (fun z : CoarseState => (if z.2 then 1 else 0 : ℝ)) :=
    Measurable.of_discrete
  rw [coordinate_integral _ (fun z : CoarseState => (if z.2 then 1 else 0 : ℝ)) hm (n+1),
    coarse_marginal_after_one, coarse_induced_world_integral]

theorem fine_projected_world_mean (t : Bool) (y : FineState) (n : ℕ) :
    (∫ w, observedWorldScore n (w n)
      ∂(((fineModel t).pathLaw (Measure.dirac y)).map compression.pathMap)) =
    (∫ w, (if (w n).2 then 1 else 0 : ℝ)
      ∂(fineModel t).pathLaw (Measure.dirac y)) := by
  exact integral_map (φ := compression.pathMap)
    (f := fun w : ℕ → CoarseState => observedWorldScore n (w n))
    compression.pathMap_measurable.aemeasurable
    ((observedWorldScore_measurable n).comp
      (measurable_pi_apply n)).aestronglyMeasurable

theorem discount_weights_nonneg (n : ℕ) :
    0 ≤ (1-(1/3 : ℝ)) * (1/3 : ℝ)^n :=
  mul_nonneg (by norm_num) (pow_nonneg (by norm_num) n)

theorem discount_weights_summable :
    Summable (fun n : ℕ => (1-(1/3 : ℝ)) * (1/3 : ℝ)^n) :=
  (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/3)
    (by norm_num : (1/3 : ℝ) < 1)).mul_left (1-(1/3 : ℝ))

/-- The exact fine output for every treatment, strategic start, and world
start, evaluated on the original compressed canonical whole-path law. -/
theorem fine_whole_path_output (t s x : Bool) :
    baselinePropertyValue
      (projectedDiscountedProperty compression (1/3 : ℝ) observedWorldScore)
      (fineModel t) (s,x) = (fineDiscountedOutput t s x : ℝ) := by
  unfold baselinePropertyValue projectedDiscountedProperty discountedWholePathProperty
  change (∫ w, summablePathScore (fun n => (1-(1/3 : ℝ))*(1/3 : ℝ)^n)
      (fun n w => observedWorldScore n (w n)) w
      ∂(((fineModel t).pathLaw (Measure.dirac (s,x))).map compression.pathMap)) = _
  have : IsProbabilityMeasure
      (((fineModel t).pathLaw (Measure.dirac (s,x))).map compression.pathMap) :=
    (Measure.isProbabilityMeasure_map_iff compression.pathMap_measurable.aemeasurable).mpr
      inferInstance
  rw [integral_summablePathScore
    (((fineModel t).pathLaw (Measure.dirac (s,x))).map compression.pathMap)
    (fun n : ℕ => (1-(1/3 : ℝ))*(1/3 : ℝ)^n)
    discount_weights_nonneg discount_weights_summable
    (fun n (w : ℕ → CoarseState) => observedWorldScore n (w n))
    (fun n => (observedWorldScore_measurable n).comp (measurable_pi_apply n))
    (fun n w => (observedWorldScore_bounded n (w n)).1)
    (fun n w => (observedWorldScore_bounded n (w n)).2)]
  simp_rw [fine_projected_world_mean]
  have htail : HasSum
      (fun n : ℕ => (1-(1/3 : ℝ))*(1/3 : ℝ)^(n+2) *
        (∫ w, (if (w (n+2)).2 then 1 else 0 : ℝ)
          ∂(fineModel t).pathLaw (Measure.dirac (s,x))))
      ((1/9 : ℝ)*(fineActionRate t t : ℝ)) := by
    simp_rw [fine_world_mean_after_two]
    have h := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/3)
      (by norm_num : (1/3 : ℝ) < 1)).mul_left
        ((2/27 : ℝ)*(fineActionRate t t : ℝ))
    convert h using 1
    · funext n
      rw [pow_add]
      ring
    · norm_num
      ring
  have hall := HasSum.sum_range_add
    (f := fun n : ℕ => (1-(1/3 : ℝ))*(1/3 : ℝ)^n *
      (∫ w, (if (w n).2 then 1 else 0 : ℝ)
        ∂(fineModel t).pathLaw (Measure.dirac (s,x)))) (k := 2) htail
  rw [hall.tsum_eq]
  cases t <;> cases s <;> cases x <;>
    norm_num [Finset.sum_range_succ, fine_world_mean_zero, fine_world_mean_one,
      fineDiscountedOutput, fineActionRate]

/-- The exact coarse output on its separately specified original canonical
path law, including its initial world state. -/
theorem coarse_whole_path_output (t x : Bool) :
    baselinePropertyValue
      (discountedWholePathProperty (1/3 : ℝ) observedWorldScore)
      (coarseModel t) ((),x) = (coarseDiscountedOutput t x : ℝ) := by
  unfold baselinePropertyValue discountedWholePathProperty
  change (∫ w, summablePathScore (fun n => (1-(1/3 : ℝ))*(1/3 : ℝ)^n)
      (fun n w => observedWorldScore n (w n)) w
      ∂(coarseModel t).pathLaw (Measure.dirac ((),x))) = _
  rw [integral_summablePathScore
    ((coarseModel t).pathLaw (Measure.dirac ((),x)))
    (fun n : ℕ => (1-(1/3 : ℝ))*(1/3 : ℝ)^n)
    discount_weights_nonneg discount_weights_summable
    (fun n (w : ℕ → CoarseState) => observedWorldScore n (w n))
    (fun n => (observedWorldScore_measurable n).comp (measurable_pi_apply n))
    (fun n w => (observedWorldScore_bounded n (w n)).1)
    (fun n w => (observedWorldScore_bounded n (w n)).2)]
  change (∑' n : ℕ, (1-(1/3 : ℝ))*(1/3 : ℝ)^n *
      (∫ w, (if (w n).2 then 1 else 0 : ℝ)
        ∂(coarseModel t).pathLaw (Measure.dirac ((),x)))) = _
  have htail : HasSum
      (fun n : ℕ => (1-(1/3 : ℝ))*(1/3 : ℝ)^(n+1) *
        (∫ w, (if (w (n+1)).2 then 1 else 0 : ℝ)
          ∂(coarseModel t).pathLaw (Measure.dirac ((),x))))
      ((1/3 : ℝ)*(coarseActionRate t : ℝ)) := by
    simp_rw [coarse_world_mean_after_one]
    have h := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/3)
      (by norm_num : (1/3 : ℝ) < 1)).mul_left
        ((2/9 : ℝ)*(coarseActionRate t : ℝ))
    convert h using 1
    · funext n
      rw [pow_add]
      ring
    · norm_num
      ring
  have hall := HasSum.sum_range_add
    (f := fun n : ℕ => (1-(1/3 : ℝ))*(1/3 : ℝ)^n *
      (∫ w, (if (w n).2 then 1 else 0 : ℝ)
        ∂(coarseModel t).pathLaw (Measure.dirac ((),x)))) (k := 1) htail
  rw [hall.tsum_eq]
  cases t <;> cases x <;>
    norm_num [Finset.sum_range_succ, coarse_world_mean_zero,
      coarseDiscountedOutput, coarseActionRate]

end PermanssonResearch.Quotient.Q05WholePathIdentification

#check PermanssonResearch.Quotient.Q05WholePathIdentification.fine_whole_path_output
#print axioms PermanssonResearch.Quotient.Q05WholePathIdentification.fine_whole_path_output
#check PermanssonResearch.Quotient.Q05WholePathIdentification.coarse_whole_path_output
#print axioms PermanssonResearch.Quotient.Q05WholePathIdentification.coarse_whole_path_output
