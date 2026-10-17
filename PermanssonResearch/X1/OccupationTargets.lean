import PermanssonResearch.X1.Occupation
import PermanssonResearch.X1.OccupationNumerics
import PermanssonResearch.X1.Comparison

/-!
# X1: actual-kernel Poisson identification of descriptor occupation targets

The finite rational bias identities are connected atom by atom to the actual
typed induced kernels. Finite invariant-law cancellation then identifies the
descriptor image of every actual invariant probability. Combining this with
the existing C2 random occupation theorem gives the deterministic descriptor
target without assuming stationarity, irreducibility, or an ergodic bridge.

These occupation conclusions do not repair the failed exact invariance of
the frozen replete region. They are not Exact-GR or PR certificates.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace PermanssonResearch.X1

set_option autoImplicit false

open PermanssonLean
open PermanssonResearch.MultipleLimit
open FiniteKernelRealBridge FiniteKernelInvariantUniqueness FiniteCesaroAlgebra

attribute [local instance] StrategicWorldModel.inducedKernel_isMarkov

def learnerFlag : Mode → Bool
  | .equilibrium => false
  | .learner => true

theorem numerical_rates_eq (m : Mode) (y : Y) :
    OccupationNumerics.rates (learnerFlag m) y = extractionRate m y := by
  cases m <;> rfl

theorem numerical_next_eq (m : Mode) (y : Y) (a : Action) :
    OccupationNumerics.next (learnerFlag m) y a = nextMemory m y a := by
  cases m <;> rfl

theorem numerical_target_eq (m : Mode) :
    OccupationNumerics.target (learnerFlag m) = targetReplete m := by
  cases m <;> rfl

theorem boolMass_nonneg (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (b : Bool) :
    0 ≤ boolMass p b := by
  cases b with
  | false => simpa [boolMass] using sub_nonneg.mpr hp.2
  | true => simpa [boolMass] using hp.1

theorem numerical_entry_nonneg (m : Mode) (y z : Y) :
    0 ≤ OccupationNumerics.entry (learnerFlag m) y z := by
  unfold OccupationNumerics.entry
  simp only [numerical_rates_eq]
  apply Finset.sum_nonneg
  intro a _
  apply mul_nonneg
  · exact mul_nonneg
      (mul_nonneg (boolMass_nonneg _ (extractionRate_bounds m y).1 _)
        (boolMass_nonneg _ (extractionRate_bounds m y).2 _))
      (boolMass_nonneg _ (pRep_bounds y.2 a) _)
  · split_ifs <;> norm_num

theorem world_atom_sum (p : ℚ) (q : Memory) (z : Y) :
    (∑ x : Bool, ENNReal.ofReal (boolMass p x : ℝ) *
      if (q, x) = z then 1 else 0) =
    ENNReal.ofReal (boolMass p z.2 : ℝ) * if q = z.1 then 1 else 0 := by
  rcases z with ⟨qz, xz⟩
  cases xz <;> simp [sum_bool, Prod.mk.injEq]

theorem ofReal_mass_term (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (P : Prop) [Decidable P] :
    ENNReal.ofReal (a : ℝ) * ENNReal.ofReal (b : ℝ) *
        (ENNReal.ofReal (c : ℝ) * if P then 1 else 0) =
      ENNReal.ofReal ((a * b * c * if P then 1 else 0 : ℚ) : ℝ) := by
  by_cases h : P
  · simp only [h, if_true, mul_one]
    push_cast
    rw [ENNReal.ofReal_mul (show 0 ≤ (a : ℝ) * (b : ℝ) by
        exact mul_nonneg (by exact_mod_cast ha) (by exact_mod_cast hb)),
      ENNReal.ofReal_mul (by exact_mod_cast ha)]
  · simp [h]

/-- Every rational certificate row is the ACTUAL primitive-derived atom,
not an independently postulated matrix or a quotient hypothesis. -/
theorem transitionEntry_eq_numerical (m : Mode) (y z : Y) :
    transitionEntry m y z =
      ENNReal.ofReal (OccupationNumerics.entry (learnerFlag m) y z : ℝ) := by
  unfold transitionEntry
  simp_rw [world_atom_sum]
  simp_rw [ofReal_mass_term _ _ _
    (boolMass_nonneg _ (extractionRate_bounds m y).1 _)
    (boolMass_nonneg _ (extractionRate_bounds m y).2 _)
    (boolMass_nonneg _ (pRep_bounds y.2 _) _)]
  unfold OccupationNumerics.entry
  simp only [numerical_rates_eq, numerical_next_eq]
  have hnonneg : ∀ a ∈ (Finset.univ : Finset Action),
      0 ≤ ((boolMass (extractionRate m y).1 a.1 * boolMass (extractionRate m y).2 a.2 *
        boolMass (pRep y.2 a) z.2 * if nextMemory m y a = z.1 then 1 else 0 : ℚ) : ℝ) := by
    intro a _
    have hq : 0 ≤ (boolMass (extractionRate m y).1 a.1 *
        boolMass (extractionRate m y).2 a.2 * boolMass (pRep y.2 a) z.2 *
          if nextMemory m y a = z.1 then 1 else 0 : ℚ) :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (boolMass_nonneg _ (extractionRate_bounds m y).1 _)
          (boolMass_nonneg _ (extractionRate_bounds m y).2 _))
          (boolMass_nonneg _ (pRep_bounds y.2 a) _)) (by split_ifs <;> norm_num)
    exact_mod_cast hq
  rw [← ENNReal.ofReal_sum_of_nonneg hnonneg]
  congr 1
  push_cast <;> rfl

/-- Exact Poisson identity for the REAL singleton entries of the actual
typed kernel, including both transient learner states. -/
theorem actual_poisson_identity (m : Mode) (y : Y) :
    (OccupationNumerics.bias (learnerFlag m) y : ℝ) -
        ∑ z : Y, realTransition (model m).inducedKernel y z *
          (OccupationNumerics.bias (learnerFlag m) z : ℝ) =
      (indicator y.2 : ℝ) - (targetReplete m : ℝ) := by
  have h := congrArg (fun q : ℚ => (q : ℝ))
    (OccupationNumerics.poisson_identity (learnerFlag m) y)
  push_cast at h
  have hentry (z : Y) : realTransition (model m).inducedKernel y z =
      (OccupationNumerics.entry (learnerFlag m) y z : ℝ) := by
    rw [realTransition, inducedKernel_atom_entry, transitionEntry_eq_numerical]
    exact ENNReal.toReal_ofReal (by exact_mod_cast numerical_entry_nonneg m y z)
  simp_rw [hentry]
  simpa only [numerical_target_eq] using h

/-- Finite-sum cancellation, using exact invariant-vector equations. -/
theorem poisson_invariant_mean
    (R : Y → Y → ℝ) (v g f : Y → ℝ) (ν : ℝ)
    (htotal : (∑ y : Y, v y) = 1)
    (hstat : ∀ z, (∑ y : Y, v y * R y z) = v z)
    (hpoisson : ∀ y, g y - ∑ z : Y, R y z * g z = f y - ν) :
    (∑ y : Y, v y * f y) = ν := by
  have hdouble : (∑ y : Y, v y * ∑ z : Y, R y z * g z) =
      ∑ z : Y, v z * g z := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, hstat z]
  have hzero : (∑ y : Y, v y * (g y - ∑ z : Y, R y z * g z)) = 0 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [hdouble, sub_self]
  simp_rw [hpoisson, mul_sub, Finset.sum_sub_distrib] at hzero
  rw [← Finset.sum_mul, htotal, one_mul] at hzero
  exact sub_eq_zero.mp hzero

/-- EVERY actual invariant probability has the registered descriptor mean;
existence/uniqueness of a global invariant law is not assumed. -/
theorem invariant_descriptor_mean (m : Mode) (π : ProbabilityMeasure Y)
    (hπ : Kernel.Invariant (model m).inducedKernel π.toMeasure) :
    (∑ y : Y, realPointMass π y * (indicator y.2 : ℝ)) = (targetReplete m : ℝ) := by
  apply poisson_invariant_mean (realTransition (model m).inducedKernel)
    (realPointMass π) (fun y => (OccupationNumerics.bias (learnerFlag m) y : ℝ))
    (fun y => (indicator y.2 : ℝ)) (targetReplete m : ℝ)
    (realPointMass_total π)
  · intro z
    exact realPointMass_stationary (model m).inducedKernel π hπ z
  · exact actual_poisson_identity m

/-- On the finite state space, the descriptor's true mass is exactly its
indicator mean. No unproved moment or occupation identification is used. -/
theorem descriptor_true_real_eq_mean (π : ProbabilityMeasure Y) :
    ((π.map descriptor).toMeasure {true}).toReal =
      ∑ y : Y, realPointMass π y * (indicator y.2 : ℝ) := by
  have hbool (μ : ProbabilityMeasure Bool) :
      (∫ b, (indicator b : ℝ) ∂μ.toMeasure) = (μ.toMeasure {true}).toReal := by
    rw [integral_fintype (Integrable.of_finite), sum_bool]
    simp [indicator, smul_eq_mul, Measure.real_def]
  calc
    _ = ∫ b, (indicator b : ℝ) ∂(π.map descriptor).toMeasure := (hbool _).symm
    _ = ∫ y, (indicator (descriptor y) : ℝ) ∂π.toMeasure := by
      change (∫ b, (indicator b : ℝ) ∂π.toMeasure.map descriptor) = _
      rw [integral_map (Measurable.of_discrete.aemeasurable)
        (Measurable.of_discrete.aestronglyMeasurable)]
    _ = _ := by
      rw [integral_fintype (Integrable.of_finite)] <;>
        simp only [realPointMass, descriptor, smul_eq_mul, Measure.real_def]

theorem probability_bool_eq_of_true_real (μ ν : ProbabilityMeasure Bool)
    (h : (μ.toMeasure {true}).toReal = (ν.toMeasure {true}).toReal) : μ = ν := by
  have ht : μ.toMeasure {true} = ν.toMeasure {true} := by
    calc
      _ = ENNReal.ofReal (μ.toMeasure {true}).toReal :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ = ENNReal.ofReal (ν.toMeasure {true}).toReal := congrArg ENNReal.ofReal h
      _ = _ := ENNReal.ofReal_toReal (measure_ne_top _ _)
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_singleton
  intro b
  cases b with
  | true => exact ht
  | false =>
      have hc : ({false} : Set Bool) = ({true} : Set Bool)ᶜ := by
        ext b; cases b <;> simp
      simp only [hc, MeasureTheory.prob_compl_eq_one_sub
        (measurableSet_singleton true), ht]

/-- Every invariant law of the ACTUAL typed kernel has the separately
registered Boolean descriptor law, even though E has many physical invariant
laws. This is descriptor identification, not global stationary uniqueness. -/
theorem invariant_observed_law (m : Mode) (π : ProbabilityMeasure Y)
    (hπ : Kernel.Invariant (model m).inducedKernel π.toMeasure) :
    π.map descriptor = (specification m).target := by
  apply probability_bool_eq_of_true_real
  rw [descriptor_true_real_eq_mean, invariant_descriptor_mean m π hπ]
  change (targetReplete m : ℝ) = (coin (targetReplete m) {true}).toReal
  rw [coin_true, ENNReal.toReal_ofReal (by exact_mod_cast (targetReplete_bounds m).1)]

/-- C2's class-selected random invariant probability has a deterministic
descriptor image. The exact Poisson certificate supplies the bridge. -/
theorem observedRandomLimit_eq_target (m : Mode) (w : ℕ → Y) :
    observedRandomLimit m w = (specification m).target := by
  change (physicalRandomLimit m w).map descriptor = _
  apply invariant_observed_law
  exact (ClassStationarySelectionLaw.selectedStationary_spec (model m).inducedKernel w).1

/-- The ORIGINAL empirical descriptor occupations under the ACTUAL typed
infinite path law converge a.s. to their DISTINCT registered E/L targets,
for every initial probability law. The replete region still leaks, so this
occupation theorem does not establish Exact GR or PR. -/
theorem canonical_occupation_target_ae (m : Mode) (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂(model m).pathLaw μ.toMeasure,
      Tendsto (fun n : ℕ =>
        RegimeSpecification.empiricalOccupation (specification m) w (n+1) (Nat.succ_pos n))
        atTop (𝓝 (specification m).target) := by
  filter_upwards [original_empirical_randomLimit_ae m (specification m) rfl μ] with w hw
  rwa [observedRandomLimit_eq_target] at hw

end PermanssonResearch.X1
