import PermanssonResearch.MultipleLimit.StationaryConditionalLaw
import PermanssonResearch.MultipleLimit.CompactFellerDistance
import PermanssonResearch.MultipleLimit.CanonicalInitialAbsoluteContinuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-! Compact stationary random-law occupation: the actual empirical measures
converge to the conditional law of Y0 given the shift-invariant sigma-algebra.
Countable norm density is used only for compact C(Y,R). Feller continuity is
needed for invariance of that random law, not for stationary convergence.
Absolutely continuous initial laws inherit the same almost-sure statements. -/

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped Topology ENNReal

namespace PermanssonResearch.MultipleLimit.StationaryRandom

set_option autoImplicit false
noncomputable section
variable {Y : Type*} [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable [Nonempty Y]
open FiniteCanonicalPath FiniteStateOccupation StationaryConditional CompactFeller

theorem integral_difference_bound (μ : ProbabilityMeasure Y) (f g : C(Y,ℝ)) :
    |(∫ y, f y ∂μ.toMeasure)-(∫ y, g y ∂μ.toMeasure)| ≤ ‖f-g‖ := by
  rw [← integral_sub (continuousMap_integrable f μ) (continuousMap_integrable g μ)]
  exact integral_test_bound μ (f-g)

theorem integral_tendsto_of_dense (L : ℕ → ProbabilityMeasure Y) (ξ : ProbabilityMeasure Y)
    (d : ℕ → C(Y,ℝ)) (hd : DenseRange d)
    (h : ∀ k, Tendsto (fun n => ∫ y, d k y ∂(L n).toMeasure) atTop
      (𝓝 (∫ y, d k y ∂ξ.toMeasure))) (f : C(Y,ℝ)) :
    Tendsto (fun n => ∫ y, f y ∂(L n).toMeasure) atTop (𝓝 (∫ y, f y ∂ξ.toMeasure)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k,hk⟩ := hd.exists_dist_lt f (show 0 < ε/4 by positivity)
  have hkn : ‖f-d k‖ < ε/4 := by simpa only [dist_eq_norm] using hk
  obtain ⟨N,hN⟩ := (Metric.tendsto_atTop.mp (h k)) (ε/2) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hv : |(∫ y, d k y ∂(L n).toMeasure)-(∫ y, d k y ∂ξ.toMeasure)| < ε/2 := by
    simpa only [Real.dist_eq] using hN n hn
  have h1 := integral_difference_bound (L n) f (d k)
  have h2 := integral_difference_bound ξ (d k) f
  rw [norm_sub_rev] at h2
  have htri (a b c : ℝ) : |a+b+c| ≤ |a|+|b|+|c| :=
    (abs_add_le (a+b) c).trans (by linarith [abs_add_le a b])
  have ha : |(∫ y, f y ∂(L n).toMeasure)-(∫ y, f y ∂ξ.toMeasure)| ≤
      |(∫ y, f y ∂(L n).toMeasure)-(∫ y, d k y ∂(L n).toMeasure)| +
      |(∫ y, d k y ∂(L n).toMeasure)-(∫ y, d k y ∂ξ.toMeasure)| +
      |(∫ y, d k y ∂ξ.toMeasure)-(∫ y, f y ∂ξ.toMeasure)| := by
    calc
      _ = |((∫ y, f y ∂(L n).toMeasure)-(∫ y, d k y ∂(L n).toMeasure)) +
        ((∫ y, d k y ∂(L n).toMeasure)-(∫ y, d k y ∂ξ.toMeasure)) +
        ((∫ y, d k y ∂ξ.toMeasure)-(∫ y, f y ∂ξ.toMeasure))| := by congr 1; ring
      _ ≤ _ := htri _ _ _
  have ht : |(∫ y, f y ∂(L n).toMeasure)-(∫ y, f y ∂ξ.toMeasure)| < ε := by linarith
  simpa only [Real.dist_eq] using ht

theorem empirical_tendsto_randomLaw (K : Kernel Y Y) [IsMarkovKernel K]
    (π : ProbabilityMeasure Y) (hπ : K ∘ₘ π.toMeasure = π.toMeasure) :
    ∀ᵐ w ∂canonicalPathLaw K π.toMeasure,
      Tendsto (fun n => empiricalOccupation w (n+1) (Nat.succ_pos n)) atTop
        (𝓝 (randomLaw K π w)) := by
  have hc (k : ℕ) := state_average_tendsto K π hπ (denseSeq C(Y,ℝ) k)
    (denseSeq C(Y,ℝ) k).continuous.measurable ‖denseSeq C(Y,ℝ) k‖ (norm_nonneg _)
    (fun y => by simpa only [Real.norm_eq_abs] using (denseSeq C(Y,ℝ) k).norm_coe_le_norm y)
  filter_upwards [ae_all_iff.mpr hc] with w hw
  have hd (k : ℕ) :
      Tendsto (fun n => ∫ y, denseSeq C(Y,ℝ) k y ∂
        (empiricalOccupation w (n+1) (Nat.succ_pos n)).toMeasure) atTop
        (𝓝 (∫ y, denseSeq C(Y,ℝ) k y ∂(randomLaw K π w).toMeasure)) := by
    have he : (fun n => ∫ y, denseSeq C(Y,ℝ) k y ∂
        (empiricalOccupation w (n+1) (Nat.succ_pos n)).toMeasure) =
        (fun n => (∑ t ∈ Finset.range (n+1), denseSeq C(Y,ℝ) k (w t)) / ((n+1:ℕ):ℝ)) := by
      funext n
      rw [empirical_integral w n _ (denseSeq C(Y,ℝ) k).continuous.measurable]
      exact (div_eq_inv_mul _ _).symm
    rw [he]
    exact hw k
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  exact integral_tendsto_of_dense _ (randomLaw K π w) (denseSeq C(Y,ℝ))
    (denseRange_denseSeq _) hd ⟨f,f.continuous⟩

theorem randomLaw_invariant_ae (K : Kernel Y Y) [IsMarkovKernel K] (hF : IsFeller K)
    (π : ProbabilityMeasure Y) (hπ : K ∘ₘ π.toMeasure = π.toMeasure) :
    ∀ᵐ w ∂canonicalPathLaw K π.toMeasure,
      K ∘ₘ (randomLaw K π w).toMeasure = (randomLaw K π w).toMeasure := by
  filter_upwards [empirical_tendsto_randomLaw K π hπ,empirical_clusters_invariant_ae K hF π]
    with w hw hi
  exact hi (randomLaw K π w) hw.mapClusterPt

theorem empirical_continuous (n : ℕ) :
    Continuous (fun w : ℕ → Y => empiricalOccupation w (n+1) (Nat.succ_pos n)) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro f
  simp_rw [empirical_integral _ n f f.continuous.measurable]
  exact continuous_const.mul (continuous_finset_sum _ fun t _ => f.continuous.comp (continuous_apply t))

/-- Measurability for the Borel sigma-algebra of the actual weak topology,
in addition to the RCP's Giry measurability already proved separately. -/
theorem randomLaw_aemeasurable_weakBorel (K : Kernel Y Y) [IsMarkovKernel K]
    (π : ProbabilityMeasure Y) (hπ : K ∘ₘ π.toMeasure = π.toMeasure) :
    @AEMeasurable (ℕ → Y) (ProbabilityMeasure Y) (borel (ProbabilityMeasure Y)) inferInstance
      (randomLaw K π) (canonicalPathLaw K π.toMeasure) := by
  letI : MeasurableSpace (ProbabilityMeasure Y) := borel (ProbabilityMeasure Y)
  letI : BorelSpace (ProbabilityMeasure Y) := ⟨rfl⟩
  exact aemeasurable_of_tendsto_metrizable_ae' (fun n => (empirical_continuous n).measurable.aemeasurable)
    (empirical_tendsto_randomLaw K π hπ)

theorem measurable_weakBorel_version (K : Kernel Y Y) [IsMarkovKernel K]
    (π : ProbabilityMeasure Y) (hπ : K ∘ₘ π.toMeasure = π.toMeasure) :
    ∃ Λ : (ℕ → Y) → ProbabilityMeasure Y,
      @Measurable (ℕ → Y) (ProbabilityMeasure Y) inferInstance (borel (ProbabilityMeasure Y)) Λ ∧
      Λ =ᵐ[canonicalPathLaw K π.toMeasure] randomLaw K π := by
  letI : MeasurableSpace (ProbabilityMeasure Y) := borel (ProbabilityMeasure Y)
  letI : BorelSpace (ProbabilityMeasure Y) := ⟨rfl⟩
  have hm := randomLaw_aemeasurable_weakBorel K π hπ
  exact ⟨hm.mk _,hm.measurable_mk,hm.ae_eq_mk.symm⟩

theorem empirical_tendsto_randomLaw_of_initial_ac (K : Kernel Y Y) [IsMarkovKernel K]
    (μ π : ProbabilityMeasure Y) (hπ : K ∘ₘ π.toMeasure = π.toMeasure)
    (hμ : μ.toMeasure ≪ π.toMeasure) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n => empiricalOccupation w (n+1) (Nat.succ_pos n)) atTop
        (𝓝 (randomLaw K π w)) :=
  CanonicalInitial.pathLaw_ae_transfer K μ.toMeasure π.toMeasure hμ _
    (empirical_tendsto_randomLaw K π hπ)

/-- A weak-Borel measurable version of the actual conditional probability
simultaneously gives the empirical limit and an invariant law almost surely.
Its almost-sure identification with the RCP is part of the conclusion. -/
theorem exists_measurable_random_limit (K : Kernel Y Y) [IsMarkovKernel K] (hF : IsFeller K)
    (π : ProbabilityMeasure Y) (hπ : K ∘ₘ π.toMeasure = π.toMeasure) :
    ∃ Λ : (ℕ → Y) → ProbabilityMeasure Y,
      @Measurable (ℕ → Y) (ProbabilityMeasure Y) inferInstance (borel (ProbabilityMeasure Y)) Λ ∧
      (Λ =ᵐ[canonicalPathLaw K π.toMeasure] randomLaw K π) ∧
      ∀ᵐ w ∂canonicalPathLaw K π.toMeasure,
        Tendsto (fun n => empiricalOccupation w (n+1) (Nat.succ_pos n)) atTop (𝓝 (Λ w)) ∧
        K ∘ₘ (Λ w).toMeasure = (Λ w).toMeasure := by
  obtain ⟨Λ,hm,he⟩ := measurable_weakBorel_version K π hπ
  refine ⟨Λ,hm,he,?_⟩
  filter_upwards [he,empirical_tendsto_randomLaw K π hπ,randomLaw_invariant_ae K hF π hπ]
    with w hw hl hi
  rw [hw]
  exact ⟨hl,hi⟩

variable {H : Type*} [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]

theorem descriptor_random_family (K : Kernel Y Y) [IsMarkovKernel K] (hF : IsFeller K)
    (μ π : ProbabilityMeasure Y) (hπ : K ∘ₘ π.toMeasure = π.toMeasure)
    (hμ : μ.toMeasure ≪ π.toMeasure) (h : Y → H) (hh : Continuous h)
    (F : Set (ProbabilityMeasure H))
    (cover : ∀ ξ : ProbabilityMeasure Y, K ∘ₘ ξ.toMeasure = ξ.toMeasure → ξ.map h ∈ F) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      (randomLaw K π w).map h ∈ F ∧
      Tendsto (fun n => (empiricalOccupation w (n+1) (Nat.succ_pos n)).map h)
        atTop (𝓝 ((randomLaw K π w).map h)) := by
  apply CanonicalInitial.pathLaw_ae_transfer K μ.toMeasure π.toMeasure hμ
  filter_upwards [empirical_tendsto_randomLaw K π hπ,randomLaw_invariant_ae K hF π hπ]
    with w hw hi
  exact ⟨cover _ hi,(ProbabilityMeasure.continuous_map hh).continuousAt.tendsto.comp hw⟩

end
end PermanssonResearch.MultipleLimit.StationaryRandom
