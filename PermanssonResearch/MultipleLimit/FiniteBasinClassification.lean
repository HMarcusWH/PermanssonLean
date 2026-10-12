import PermanssonResearch.MultipleLimit.FiniteOccupationRandomLaw
import PermanssonResearch.MultipleLimit.BasinFamily
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic

/-!
# C53-08 — frozen nonvacuous basin-family occupation certification

This finite-state multiple-target layer is intentionally separate from
the frozen single-target v0.1.8 RegimeSpecification. A class belongs to
the frozen family ONLY if an admitted basin point can select it with
strictly positive probability in the genuine infinite canonical chain.

An arbitrary initial law supported on that basin cannot secretly reach
a class outside the registered family. A further PREDECLARED common
observed class law therefore gives the genuine almost-sure deterministic
observed occupation limit for every admitted initial law.

The family result does not automatically certify an Exact GR: that still
requires all original Assumption 4.1, exact region and typed model gates.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteBasinClassification

open FiniteCanonicalPath
open CanonicalClassSelector
open CanonicalClassWeights
open KernelCommunication
open BasinFamily
open ClassDescriptorSelectionLaw
open FiniteOccupationRandomLaw
open FiniteStateOccupation

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [Nonempty Y] [DecidableEq Y]
variable [TopologicalSpace Y] [DiscreteTopology Y]
variable [OpensMeasurableSpace Y] [StandardBorelSpace Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]
variable {H : Type*} [MeasurableSpace H] [TopologicalSpace H]
variable [BorelSpace H]
variable (F : FrozenBasinFamily K H)

/-- Under an arbitrary initial probability measure supported on the
frozen basin, any recurrent class absent from the REGISTERED reachable
family has zero actual infinite-path selection probability. -/
theorem unreachable_class_mass_zero
    (μ : ProbabilityMeasure Y)
    (hμ : μ.toMeasure F.basin = 1)
    (i : Y) (hi : i ∈ recurrentRepresentatives K)
    (hnot : i ∉ reachableRepresentatives K H F) :
    (canonicalPathLaw K μ.toMeasure)
      ((selectedRepresentative K) ⁻¹' {i}) = 0 := by
  have hbmeas : MeasurableSet F.basin :=
    (Set.toFinite F.basin).measurableSet
  have hcomplement : μ.toMeasure F.basinᶜ = 0 := by
    rw [prob_compl_eq_one_sub hbmeas, hμ]
    simp
  rw [class_selection_weight_initial_mixture K μ i]
  apply Finset.sum_eq_zero
  intro y hy
  by_cases hby : y ∈ F.basin
  · rw [unreachable_probability_zero K H F y hby i hi hnot]
    simp
  · have hsubset : ({y} : Set Y) ⊆ F.basinᶜ := by
      intro q hq
      simpa [Set.mem_singleton_iff] using (show q ∉ F.basin from by
        simpa only [Set.mem_singleton_iff] using
          (show q = y → q ∉ F.basin from fun h => h ▸ hby) (by simpa using hq))
    have hzero : μ.toMeasure ({y} : Set Y) = 0 :=
      measure_mono_null hsubset hcomplement
    rw [hzero]
    simp

/-- Non-post-hoc family restriction: the selected recurrent class is
in the frozen positive-probability family almost surely, for EVERY
initial measure on the declared basin. -/
theorem selected_reachable_family_ae
    (μ : ProbabilityMeasure Y)
    (hμ : μ.toMeasure F.basin = 1) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      selectedRepresentative K w ∈ reachableRepresentatives K H F := by
  classical
  let P := canonicalPathLaw K μ.toMeasure
  let f := selectedRepresentative K
  let s : Finset Y := (recurrentRepresentatives K).filter
    (fun i => i ∉ reachableRepresentatives K H F)
  have hset :
      {w : ℕ → Y | f w ∉ reachableRepresentatives K H F} =
        f ⁻¹' (↑s : Set Y) := by
    ext w
    simp [s, f, selectedRepresentative_mem K w]
  have hsum :
      (∑ i ∈ s, P (f ⁻¹' ({i} : Set Y))) =
        P (f ⁻¹' (↑s : Set Y)) :=
    sum_measure_preimage_singleton (μ := P) s
      (fun i hi =>
        (measurableSet_singleton i).preimage
          (selectedRepresentative_measurable K))
  have hnull : P (f ⁻¹' (↑s : Set Y)) = 0 := by
    rw [← hsum]
    apply Finset.sum_eq_zero
    intro i hi
    have hii : i ∈ recurrentRepresentatives K :=
      (Finset.mem_filter.mp hi).1
    have hnot : i ∉ reachableRepresentatives K H F :=
      (Finset.mem_filter.mp hi).2
    exact unreachable_class_mass_zero K F μ hμ i hii hnot
  rw [ae_iff]
  simpa only [not_mem_setOf_iff, hset] using hnull

/-- A frozen common descriptor target assigned to ALL and ONLY
basin-reachable recurrent classes. This is separate from the original
RegimeSpecification.target, which is left unchanged. -/
structure CommonObservedCertificate where
  target : ProbabilityMeasure H
  common : ∀ i ∈ reachableRepresentatives K H F,
    observedStationaryForClass K F.descriptor i = target

/-- A nonempty frozen class family with an ex-ante common observed law
genuinely determines the empirical descriptor limit a.s. for every
initial law supported on its frozen basin. -/
theorem canonical_family_observed_ae_limit
    (C : CommonObservedCertificate K F)
    (μ : ProbabilityMeasure Y)
    (hμ : μ.toMeasure F.basin = 1) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto
        (fun n : ℕ =>
          (empiricalOccupation w (n+1)
            (Nat.succ_pos n)).map F.descriptor)
        atTop (𝓝 C.target) := by
  filter_upwards
    [selected_reachable_family_ae K F μ hμ,
     observedOccupationLimit_ae_correct K μ F.descriptor]
    with w hclass hlimit
  have heq : observedOccupationLimit K F.descriptor w =
      C.target := by
    change observedStationaryForClass K F.descriptor
      (selectedRepresentative K w) = C.target
    exact C.common _ hclass
  rwa [heq] at hlimit

end FiniteBasinClassification
end MultipleLimit
end PermanssonResearch
