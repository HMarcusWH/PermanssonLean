import PermanssonResearch.MultipleLimit.StationaryCanonicalShift
import PermanssonResearch.StrategicWorld.DeterministicOrbit
import PermanssonResearch.MultipleLimit.FiniteStateOccupation
import PermanssonResearch.MultipleLimit.FiniteUniformAverage
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Analysis.SpecificLimits.Basic

/-! The actual homogeneous successor kernel on the countably infinite
discrete state space. Its canonical law is the Dirac law of the clock,
and its empirical probabilities have no weak probability limit. -/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal
namespace PermanssonResearch.MultipleLimit.NonfiniteClock
open FiniteCanonicalPath FiniteStateOccupation StationaryCanonical
set_option autoImplicit false

theorem canonical_deterministic {Y : Type*} [MeasurableSpace Y]
    (K : Kernel Y Y) [IsMarkovKernel K] (f : Y → Y)
    (hK : ∀ y, K y = Measure.dirac (f y)) (y : Y) :
    canonicalPathLaw K (Measure.dirac y) = Measure.dirac (fun n => f^[n] y) := by
  apply measure_eq_of_prefix_maps
  apply prefix_maps_eq K
  · rw [canonical_prefix_zero, Measure.map_dirac' (Preorder.measurable_frestrictLe 0),
      Measure.map_dirac' (MeasurableEquiv.measurable _)]
    congr 1
    funext i
    have hi : i.1 = 0 := Nat.le_zero.mp (mem_Iic.mp i.2)
    simp [hi]
  · exact CanonicalKernelMarginals.canonical_transition_pair K (Measure.dirac y)
  · intro n
    rw [Measure.map_dirac' (Preorder.measurable_frestrictLe n),
      Measure.map_dirac' (by fun_prop),
      PermanssonResearch.StrategicWorld.dirac_compProd_eq_map]
    change (K (f^[n] y)).map _ = _
    rw [hK, Measure.map_dirac' measurable_prodMk_left]
    congr 1
    exact Prod.ext rfl (by simp [Function.iterate_succ_apply'])

noncomputable def clock : Kernel ℕ ℕ :=
  Kernel.deterministic Nat.succ (measurable_of_countable _)

instance clock_markov : IsMarkovKernel clock := by unfold clock; infer_instance

theorem clock_law : canonicalPathLaw clock (Measure.dirac 0) = Measure.dirac id := by
  have hi (n : ℕ) : Nat.succ^[n] 0 = n := by
    induction n with
    | zero => rfl
    | succ n ih => simp [Function.iterate_succ_apply',ih]
  simpa only [hi] using! canonical_deterministic clock Nat.succ
    (fun _ => rfl) 0

theorem empirical_integral {Y : Type*} [MeasurableSpace Y]
    (w : ℕ → Y) (n : ℕ) (f : Y → ℝ) (hf : Measurable f) :
    (∫ y, f y ∂(empiricalOccupation w (n+1) (Nat.succ_pos n)).toMeasure) =
      (∑ t ∈ range (n+1), f (w t))/((n+1 : ℕ) : ℝ) := by
  change (∫ y, f y ∂Measure.map (fun i : Fin (n+1) => w (i : ℕ))
    (PermanssonLean.RegimeSpecification.uniformFinProbability (n+1) (Nat.succ_pos n)).toMeasure) = _
  rw [integral_map (by fun_prop) hf.aestronglyMeasurable,
    FiniteUniformAverage.integral_uniformFin_eq_average,
    Fin.sum_univ_eq_sum_range (fun i : ℕ => f (w i))]
  rw [div_eq_mul_inv,mul_comm]

theorem clock_singleton_frequency (n k : ℕ) :
    ((empiricalOccupation id (n+1) (Nat.succ_pos n)) {k} : ℝ) =
      (if k < n+1 then 1 else 0)/((n+1 : ℕ) : ℝ) := by
  have he := empirical_integral id n (({k} : Set ℕ).indicator (fun _ => (1 : ℝ)))
    (measurable_const.indicator (measurableSet_singleton k))
  rw [integral_indicator_const _ (measurableSet_singleton k)] at he
  simpa [Finset.sum_ite_eq',Set.indicator,Set.mem_singleton_iff] using he

theorem clock_singletons_tendsto_zero (k : ℕ) :
    Tendsto (fun n => (empiricalOccupation id (n+1) (Nat.succ_pos n)) {k}) atTop (𝓝 0) := by
  apply NNReal.tendsto_coe.1
  have hb : Tendsto (fun n : ℕ => (1 : ℝ)/((n+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply squeeze_zero (fun n => by positivity) _ hb
  intro n
  rw [clock_singleton_frequency]
  split_ifs <;> simp <;> positivity

theorem clock_no_probability_weak_limit :
    ¬ ∃ π : ProbabilityMeasure ℕ,
      Tendsto (fun n => empiricalOccupation id (n+1) (Nat.succ_pos n)) atTop (𝓝 π) := by
  rintro ⟨π,hπ⟩
  have hz (k : ℕ) : (π : Measure ℕ) {k} = 0 := by
    apply (ProbabilityMeasure.null_iff_toMeasure_null π {k}).mp
    have hk := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hπ
      (show IsClopen ({k} : Set ℕ) from ⟨isClosed_discrete _,isOpen_discrete _⟩)
    exact tendsto_nhds_unique hk (clock_singletons_tendsto_zero k)
  have hu : (Set.univ : Set ℕ) = ⋃ k : ℕ, ({k} : Set ℕ) := by ext k; simp
  have hm : (π : Measure ℕ) Set.univ = 0 := by rw [hu]; exact measure_iUnion_null hz
  simpa using hm

theorem canonical_clock_no_weak_limit :
    ∀ᵐ w ∂canonicalPathLaw clock (Measure.dirac 0),
      ¬ ∃ π : ProbabilityMeasure ℕ,
        Tendsto (fun n => empiricalOccupation w (n+1) (Nat.succ_pos n)) atTop (𝓝 π) := by
  rw [clock_law]
  rw [ae_dirac_eq]
  exact clock_no_probability_weak_limit

end PermanssonResearch.MultipleLimit.NonfiniteClock
