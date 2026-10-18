import PermanssonResearch.MultipleLimit.StationaryCanonicalShift
import PermanssonResearch.Probability.BoundedBirkhoffConditional
import Mathlib.Probability.Kernel.CondDistrib

/-! The limiting random probability is the genuine regular conditional law
of the time-zero state given the invariant sigma-algebra of the actual shift.
The conditioning space need not itself be standard Borel; the state space is.
Measurability here is the probability-measure Giry sigma-algebra. -/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace PermanssonResearch.MultipleLimit.StationaryConditional

set_option autoImplicit false
noncomputable section
variable {Y : Type*} [mY : MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
open FiniteCanonicalPath StationaryCanonical
open PermanssonResearch.Probability

abbrev invariantSpace : MeasurableSpace (ℕ → Y) := Hopf.invariantSigma shift

def conditionalKernel (K : Kernel Y Y) [IsMarkovKernel K] (π : ProbabilityMeasure Y) :
    @Kernel (ℕ → Y) Y invariantSpace mY :=
  @condDistrib (ℕ → Y) (ℕ → Y) Y mY _ _ inferInstance invariantSpace
    (fun w : ℕ → Y => w 0) id (canonicalPathLaw K π.toMeasure) _

instance conditionalKernel_isMarkov (K : Kernel Y Y) [IsMarkovKernel K]
    (π : ProbabilityMeasure Y) : IsMarkovKernel (conditionalKernel K π) := by
  unfold conditionalKernel
  infer_instance

def randomLaw (K : Kernel Y Y) [IsMarkovKernel K] (π : ProbabilityMeasure Y)
    (w : ℕ → Y) : ProbabilityMeasure Y := ⟨conditionalKernel K π w,inferInstance⟩

theorem randomLaw_measurable_invariant (K : Kernel Y Y) [IsMarkovKernel K]
    (π : ProbabilityMeasure Y) :
    Measurable[invariantSpace] (randomLaw K π) := by
  exact (Kernel.measurable (conditionalKernel K π)).subtype_mk

theorem randomLaw_measurable (K : Kernel Y Y) [IsMarkovKernel K]
    (π : ProbabilityMeasure Y) : Measurable (randomLaw K π) :=
  (randomLaw_measurable_invariant K π).mono (Hopf.invariantSigma_le shift) le_rfl

theorem conditional_integral (K : Kernel Y Y) [IsMarkovKernel K]
    (π : ProbabilityMeasure Y) (f : Y → ℝ) (hf : Measurable f)
    (hfi : Integrable (fun w : ℕ → Y => f (w 0)) (canonicalPathLaw K π.toMeasure)) :
    (canonicalPathLaw K π.toMeasure)[fun w => f (w 0) | invariantSpace] =ᵐ[
      canonicalPathLaw K π.toMeasure] fun w => ∫ y, f y ∂(randomLaw K π w).toMeasure := by
  simpa only [MeasurableSpace.comap_id, id_eq, randomLaw, conditionalKernel,ProbabilityMeasure.coe_mk]
    using condExp_ae_eq_integral_condDistrib
      (μ := canonicalPathLaw K π.toMeasure)
      (mβ := invariantSpace) (X := id) (Y := fun w : ℕ → Y => w 0)
      (measurable_id'' (Hopf.invariantSigma_le shift)) (measurable_pi_apply 0).aemeasurable
      hf.stronglyMeasurable hfi

theorem state_average_eq_birkhoff (f : Y → ℝ) (n : ℕ) (w : ℕ → Y) :
    (∑ t ∈ Finset.range n, f (w t)) / (n : ℝ) =
      birkhoffAverage ℝ shift (fun q : ℕ → Y => f (q 0)) n w := by
  unfold birkhoffAverage birkhoffSum
  simp only [shift_iterate_zero,smul_eq_mul]
  exact div_eq_inv_mul _ _

theorem state_average_tendsto (K : Kernel Y Y) [IsMarkovKernel K]
    (π : ProbabilityMeasure Y) (hπ : K ∘ₘ π.toMeasure = π.toMeasure)
    (f : Y → ℝ) (hf : Measurable f) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ y, |f y| ≤ B) :
    ∀ᵐ w ∂canonicalPathLaw K π.toMeasure,
      Tendsto (fun n => (∑ t ∈ Finset.range (n+1), f (w t)) / ((n+1:ℕ):ℝ))
        atTop (𝓝 (∫ y, f y ∂(randomLaw K π w).toMeasure)) := by
  have hfi := Hopf.integrable_of_abs_bound (μ := canonicalPathLaw K π.toMeasure)
    (hf.comp (measurable_pi_apply 0)) B (fun w : ℕ → Y => hb (w 0))
  filter_upwards [Hopf.bounded_birkhoff_condExp (shift_measurePreserving K π hπ)
    (hf.comp (measurable_pi_apply 0)) B hB (fun w => hb (w 0)),
    conditional_integral K π f hf hfi] with w hw he
  have hn := hw.comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun n => birkhoffAverage ℝ shift (fun q : ℕ → Y => f (q 0)) (n+1) w)
    atTop (𝓝 ((canonicalPathLaw K π.toMeasure)[fun q => f (q 0) | invariantSpace] w)) at hn
  rw [he] at hn
  simpa only [state_average_eq_birkhoff] using hn

end
end PermanssonResearch.MultipleLimit.StationaryConditional
