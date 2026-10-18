import PermanssonResearch.MultipleLimit.StationaryConditionalLaw
import PermanssonResearch.MultipleLimit.CountableEmpiricalWeak
import PermanssonResearch.MultipleLimit.CanonicalInitialDensity
import PermanssonResearch.MultipleLimit.StationaryConditionalInvariant
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! Stationary random-law convergence on second-countable metrizable Borel
standard-Borel spaces, in particular all Polish Borel spaces. The countable
open-basis pi-system is a proved convergence-determining class. No compactness,
Feller continuity, tightness assumption, ergodicity or countable C_b supnorm
density is required. Invariance of the conditional law uses the separate
standard-Borel bounded-innovation and whole-kernel equality proof. -/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory

namespace PermanssonResearch.MultipleLimit.PolishStationaryRandom

set_option autoImplicit false
noncomputable section
variable {Y : Type*} [MetricSpace Y] [SecondCountableTopology Y]
variable [MeasurableSpace Y] [BorelSpace Y] [StandardBorelSpace Y] [Nonempty Y]
open FiniteCanonicalPath FiniteStateOccupation StationaryConditional

theorem empirical_tendsto_randomLaw (K : Kernel Y Y) [IsMarkovKernel K]
    (π : ProbabilityMeasure Y) (hπ : K ∘ₘ π.toMeasure = π.toMeasure) :
    ∀ᵐ w ∂canonicalPathLaw K π.toMeasure,
      Tendsto (fun n => empiricalOccupation w (n+1) (Nat.succ_pos n)) atTop
        (𝓝 (randomLaw K π w)) := by
  apply CountableEmpirical.weak_of_all_bounded_averages
  intro f hf B hB hb
  exact state_average_tendsto K π hπ f hf B hB hb

theorem randomLaw_aemeasurable_weakBorel (K : Kernel Y Y) [IsMarkovKernel K]
    (π : ProbabilityMeasure Y) (hπ : K ∘ₘ π.toMeasure = π.toMeasure) :
    @AEMeasurable (ℕ → Y) (ProbabilityMeasure Y) (borel (ProbabilityMeasure Y)) inferInstance
      (randomLaw K π) (canonicalPathLaw K π.toMeasure) := by
  letI : MeasurableSpace (ProbabilityMeasure Y) := borel (ProbabilityMeasure Y)
  letI : BorelSpace (ProbabilityMeasure Y) := ⟨rfl⟩
  exact aemeasurable_of_tendsto_metrizable_ae'
    (fun n => (CountableEmpirical.empirical_continuous n).measurable.aemeasurable)
    (empirical_tendsto_randomLaw K π hπ)

theorem exists_measurable_random_limit (K : Kernel Y Y) [IsMarkovKernel K]
    (μ π : ProbabilityMeasure Y) (hπ : K ∘ₘ π.toMeasure = π.toMeasure)
    (hμ : μ.toMeasure ≪ π.toMeasure) :
    ∃ Λ : (ℕ → Y) → ProbabilityMeasure Y,
      @Measurable (ℕ → Y) (ProbabilityMeasure Y) inferInstance (borel (ProbabilityMeasure Y)) Λ ∧
      (Λ =ᵐ[canonicalPathLaw K μ.toMeasure] randomLaw K π) ∧
      ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
        Tendsto (fun n => empiricalOccupation w (n+1) (Nat.succ_pos n)) atTop (𝓝 (Λ w)) ∧
        K ∘ₘ (Λ w).toMeasure = (Λ w).toMeasure := by
  letI : MeasurableSpace (ProbabilityMeasure Y) := borel (ProbabilityMeasure Y)
  letI : BorelSpace (ProbabilityMeasure Y) := ⟨rfl⟩
  have hm := randomLaw_aemeasurable_weakBorel K π hπ
  refine ⟨hm.mk _,hm.measurable_mk,?_,?_⟩
  · exact CanonicalInitial.pathLaw_ae_transfer K μ.toMeasure π.toMeasure hμ _ hm.ae_eq_mk.symm
  · apply CanonicalInitial.pathLaw_ae_transfer K μ.toMeasure π.toMeasure hμ
    filter_upwards [hm.ae_eq_mk,empirical_tendsto_randomLaw K π hπ,
      StationaryConditionalInvariant.randomLaw_invariant_ae K π hπ] with w he hw hi
    rw [← he]
    exact ⟨hw,hi⟩

theorem empirical_tendsto_randomLaw_of_initial_ac (K : Kernel Y Y) [IsMarkovKernel K]
    (μ π : ProbabilityMeasure Y) (hπ : K ∘ₘ π.toMeasure = π.toMeasure)
    (hμ : μ.toMeasure ≪ π.toMeasure) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n => empiricalOccupation w (n+1) (Nat.succ_pos n)) atTop
        (𝓝 (randomLaw K π w)) :=
  CanonicalInitial.pathLaw_ae_transfer K μ.toMeasure π.toMeasure hμ _
    (empirical_tendsto_randomLaw K π hπ)

variable {H : Type*} [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]

theorem descriptor_random_limit (K : Kernel Y Y) [IsMarkovKernel K]
    (μ π : ProbabilityMeasure Y) (hπ : K ∘ₘ π.toMeasure = π.toMeasure)
    (hμ : μ.toMeasure ≪ π.toMeasure) (h : Y → H) (hh : Continuous h) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n => (empiricalOccupation w (n+1) (Nat.succ_pos n)).map h) atTop
        (𝓝 ((randomLaw K π w).map h)) := by
  filter_upwards [empirical_tendsto_randomLaw_of_initial_ac K μ π hπ hμ] with w hw
  exact (ProbabilityMeasure.continuous_map hh).continuousAt.tendsto.comp hw

theorem descriptor_random_family (K : Kernel Y Y) [IsMarkovKernel K]
    (μ π : ProbabilityMeasure Y) (hπ : K ∘ₘ π.toMeasure = π.toMeasure)
    (hμ : μ.toMeasure ≪ π.toMeasure) (h : Y → H) (hh : Continuous h)
    (F : Set (ProbabilityMeasure H))
    (cover : ∀ ξ : ProbabilityMeasure Y, K ∘ₘ ξ.toMeasure = ξ.toMeasure → ξ.map h ∈ F) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      (randomLaw K π w).map h ∈ F ∧
      Tendsto (fun n => (empiricalOccupation w (n+1) (Nat.succ_pos n)).map h) atTop
        (𝓝 ((randomLaw K π w).map h)) := by
  apply CanonicalInitial.pathLaw_ae_transfer K μ.toMeasure π.toMeasure hμ
  filter_upwards [empirical_tendsto_randomLaw K π hπ,
    StationaryConditionalInvariant.randomLaw_invariant_ae K π hπ] with w hw hi
  exact ⟨cover _ hi,(ProbabilityMeasure.continuous_map hh).continuousAt.tendsto.comp hw⟩

end
end PermanssonResearch.MultipleLimit.PolishStationaryRandom
