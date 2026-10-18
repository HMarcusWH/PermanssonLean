import PermanssonResearch.MultipleLimit.FiniteStateOccupation
import PermanssonResearch.MultipleLimit.FiniteUniformAverage
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! A genuine countable convergence-determining class: finite intersections
of a countable open basis. Simultaneous bounded measurable indicator averages
imply weak empirical convergence to a probability which may depend on the
path. No supnorm-density or compactness assumption is used. -/

open MeasureTheory ProbabilityTheory Filter TopologicalSpace Set
open scoped Topology

namespace PermanssonResearch.MultipleLimit.CountableEmpirical

set_option autoImplicit false
open FiniteStateOccupation
variable {Y : Type*} [MeasurableSpace Y]

theorem empirical_integral (w : ℕ → Y) (n : ℕ) (f : Y → ℝ) (hf : Measurable f) :
    (∫ y, f y ∂(empiricalOccupation w (n+1) (Nat.succ_pos n)).toMeasure) =
      (∑ t ∈ Finset.range (n+1), f (w t))/((n+1 : ℕ) : ℝ) := by
  change (∫ y, f y ∂Measure.map (fun i : Fin (n+1) => w (i : ℕ))
    (PermanssonLean.RegimeSpecification.uniformFinProbability (n+1) (Nat.succ_pos n)).toMeasure) = _
  rw [integral_map (by fun_prop) hf.aestronglyMeasurable,
    FiniteUniformAverage.integral_uniformFin_eq_average,
    Fin.sum_univ_eq_sum_range (fun i : ℕ => f (w i))]
  rw [div_eq_mul_inv,mul_comm]

variable [TopologicalSpace Y] [SecondCountableTopology Y] [OpensMeasurableSpace Y]

def basisCell (F : Finset (countableBasis Y)) : Set Y := ⋂ b ∈ F, (b : Set Y)
def basisFamily : Set (Set Y) := Set.range (basisCell (Y := Y))

theorem basisCell_open (F : Finset (countableBasis Y)) : IsOpen (basisCell F) :=
  isOpen_biInter_finset (fun b _ => isOpen_of_mem_countableBasis b.2)

theorem basisFamily_pi : IsPiSystem (basisFamily (Y := Y)) := by
  classical
  rintro _ ⟨F,rfl⟩ _ ⟨G,rfl⟩ _
  refine ⟨F∪G,?_⟩
  ext y
  simp [basisCell,Finset.mem_union,or_imp,forall_and]

theorem basisFamily_measurable : ∀ s ∈ basisFamily (Y := Y), MeasurableSet s := by
  rintro _ ⟨F,rfl⟩
  exact (basisCell_open F).measurableSet

theorem basisFamily_neighborhoods (u : Set Y) (hu : IsOpen u) (y : Y) (hy : y ∈ u) :
    ∃ s ∈ basisFamily (Y := Y), s ∈ 𝓝 y ∧ s ⊆ u := by
  classical
  obtain ⟨s,hs,hys,hsu⟩ := (isBasis_countableBasis Y).exists_subset_of_mem_open hy hu
  exact ⟨s,⟨{⟨s,hs⟩},by simp [basisCell]⟩,
    (isOpen_of_mem_countableBasis hs).mem_nhds hys,hsu⟩

theorem weak_of_all_bounded_averages (P : Measure (ℕ → Y))
    (Λ : (ℕ → Y) → ProbabilityMeasure Y)
    (hav : ∀ (f : Y → ℝ), Measurable f → ∀ M : ℝ, 0 ≤ M →
      (∀ y, |f y| ≤ M) → ∀ᵐ w ∂P,
        Tendsto (fun n => (∑ t ∈ Finset.range (n+1), f (w t))/((n+1 : ℕ) : ℝ))
          atTop (𝓝 (∫ y, f y ∂(Λ w).toMeasure))) :
    ∀ᵐ w ∂P, Tendsto (fun n => empiricalOccupation w (n+1) (Nat.succ_pos n))
      atTop (𝓝 (Λ w)) := by
  classical
  let f : Finset (countableBasis Y) → Y → ℝ := fun F => (basisCell F).indicator (fun _ => 1)
  have hf (F : Finset (countableBasis Y)) : Measurable (f F) :=
    measurable_const.indicator (basisCell_open F).measurableSet
  have hb (F : Finset (countableBasis Y)) : ∀ y, |f F y| ≤ 1 := by
    intro y
    by_cases hy : y ∈ basisCell F <;> simp [f,hy]
  have hF (F : Finset (countableBasis Y)) := hav (f F) (hf F) 1 (by norm_num) (hb F)
  filter_upwards [ae_all_iff.mpr hF] with w hw
  apply basisFamily_pi.tendsto_probabilityMeasure_of_tendsto_of_mem
    basisFamily_measurable basisFamily_neighborhoods
  rintro _ ⟨F,rfl⟩
  apply NNReal.tendsto_coe.1
  have ht := hw F
  have he : (fun n => (∑ t ∈ Finset.range (n+1), f F (w t))/((n+1 : ℕ) : ℝ)) =
      fun n => ∫ y, f F y ∂(empiricalOccupation w (n+1) (Nat.succ_pos n)).toMeasure := by
    funext n
    exact (empirical_integral w n (f F) (hf F)).symm
  rw [he] at ht
  simpa only [f,integral_indicator_const (1 : ℝ) (basisCell_open F).measurableSet,
    smul_eq_mul,mul_one,ProbabilityMeasure.measureReal_eq_coe_coeFn] using ht

theorem empirical_continuous (n : ℕ) :
    Continuous (fun w : ℕ → Y => empiricalOccupation w (n+1) (Nat.succ_pos n)) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro f
  simp_rw [empirical_integral _ n f f.continuous.measurable,div_eq_inv_mul]
  exact continuous_const.mul (continuous_finsetSum _ fun t _ => f.continuous.comp (continuous_apply t))

end PermanssonResearch.MultipleLimit.CountableEmpirical
