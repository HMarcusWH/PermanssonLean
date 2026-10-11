import PermanssonResearch.MultipleLimit.TypedObservedLimit
import PermanssonLean.Regime.GeneratedRegime
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Tactic

/-!
# Lane C1 — conservative recovery of a full Exact Generated Regime

The genuine alpha/P/U model with physical multiple terminal absorbers is
an Exact GR under a nonconstant ex-ante observation descriptor mapping
both absorbers to true. We retain the frozen Assumption 4.1 gates, exact
one-step invariance, canonical process uniqueness and original
almost-sure weak convergence mode. No frozen core definitions change.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace TypedObservedExactGR

open TypedStrategicWitness TypedObservedLimit
open PermanssonLean PermanssonLean.RegimeSpecification

noncomputable section

def observedSpec : RegimeSpecification Y Bool where
  region := Set.univ
  region_measurable := MeasurableSet.univ
  basin := Set.univ
  basin_measurable := MeasurableSet.univ
  basin_subset_region := Set.subset_univ _
  descriptor := nonconstantAbsorptionDescriptor
  descriptor_measurable := Measurable.of_discrete
  target := diracProba true
  convergenceMode := ConvergenceMode.almostSureWeak Y Bool

def observedReference : Measure Y := Measure.count

theorem observedAssumption41 :
    Assumption41 model observedSpec observedReference := by
  refine ⟨⟨t, by simp [observedSpec]⟩, ?_, ?_, ?_⟩
  · right
    change 0 < observedReference Set.univ
    simp [observedReference]
  · refine ⟨t, by simp [observedSpec], a, by simp [observedSpec], ?_⟩
    change (false : Bool) ≠ true
    decide
  · apply two_states_implies_basinPathLawNontrivial model observedSpec
    exact ⟨t, by simp [observedSpec], a, by simp [observedSpec], by decide⟩

theorem observedInvariant :
    IsExactlyInvariant model observedSpec := by
  intro y _
  letI : IsMarkovKernel model.inducedKernel :=
    StrategicWorldModel.inducedKernel_isMarkov model
  change model.inducedKernel y Set.univ = 1
  exact measure_univ

/-- The ex-ante descriptor occupation is exactly the pushforward of the
identity-descriptor occupation on every finite canonical history. -/
theorem observedEmpirical_eq_map (w : ℕ → Y) (T : ℕ) (hT : 0 < T) :
    empiricalOccupation observedSpec w T hT =
      (empiricalOccupation PermanssonLean.PeriodicExactGR.spec w T hT).map
        nonconstantAbsorptionDescriptor := by
  apply ProbabilityMeasure.toMeasure_injective
  change
    Measure.map
      (fun i : Fin T => nonconstantAbsorptionDescriptor (w (i : ℕ)))
      (ProbabilityTheory.uniformOn (Set.univ : Set (Fin T))) =
    Measure.map nonconstantAbsorptionDescriptor
      (Measure.map (fun i : Fin T => w (i : ℕ))
        (ProbabilityTheory.uniformOn (Set.univ : Set (Fin T))))
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- All the original Exact GR gates are proved for the typed witness's
nonconstant observed regime, despite random distinct PHYSICAL limits. -/
theorem observedExactGeneratedRegime :
    IsExactGeneratedRegime model observedSpec observedReference := by
  refine ⟨canonicalProcessWellPosed model, observedAssumption41,
    observedInvariant, ?_⟩
  intro μ _
  unfold IsLimitingOccupationLaw
  change ∀ᵐ w ∂model.pathLaw μ.toMeasure,
    Tendsto (fun n : ℕ =>
      empiricalOccupation observedSpec w (n+1) (Nat.succ_pos n))
      atTop (𝓝 (diracProba true))
  filter_upwards [canonical_observed_weak_limit μ] with w hw
  simpa only [observedEmpirical_eq_map] using hw

end
end TypedObservedExactGR
end MultipleLimit
end PermanssonResearch
