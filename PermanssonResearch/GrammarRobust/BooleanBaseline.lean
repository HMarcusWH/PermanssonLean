import PermanssonResearch.GrammarRobust.BooleanModel
import PermanssonLean.Regime.GeneratedRegime
import PermanssonLean.Regime.PolishDescriptor
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Tactic

/-!
# Lane B — non-vacuous baseline regime gates for the Boolean witness

This module proves canonical induced-kernel dynamics, actual invariant
region, comparison-basin nontriviality, and Assumption 4.1 using the
original frozen-core definitions.  The full almost-sure occupation law
must be proved separately before claiming Exact GR.
-/

open Filter MeasureTheory ProbabilityTheory Set
namespace PermanssonResearch
namespace GrammarRobust
namespace BooleanBaseline

open PermanssonLean PermanssonLean.RegimeSpecification BooleanModel

def q0 : Y := (true, true)
def q1 : Y := (true, false)
def forbidden : Y := (false, false)
def region : Set Y := {y | y ≠ forbidden}
def basin : Set Y := {q0, q1}

/-- This exact equality comes from the actual canonical α → P → U integral. -/
theorem inducedKernel_dirac (y : Y) :
    baseline.inducedKernel y = Measure.dirac q0 := by
  ext E hE
  rw [StrategicWorldModel.inducedKernel_apply baseline y hE]
  simp [baseline, actionTrue, updateTrue, worldCopy, q0,
    Kernel.deterministic_apply, Measure.dirac_apply]
  by_cases hmem : (true, true) ∈ E <;> simp [hmem]

noncomputable def target : ProbabilityMeasure Y :=
  ⟨Measure.dirac q0, inferInstance⟩

noncomputable def spec : RegimeSpecification Y Y where
  region := region
  region_measurable := MeasurableSet.of_discrete
  basin := basin
  basin_measurable := MeasurableSet.of_discrete
  basin_subset_region := by
    intro y hy
    simp [basin, region, q0, q1, forbidden] at hy ⊢
    rcases hy with rfl | rfl <;> decide
  descriptor := id
  descriptor_measurable := measurable_id
  target := target
  convergenceMode := ConvergenceMode.almostSureWeak Y Y

noncomputable def referenceMeasure : Measure Y := Measure.count

theorem exactlyInvariant :
    IsExactlyInvariant baseline spec := by
  intro y hy
  rw [inducedKernel_dirac]
  rw [Measure.dirac_apply_of_mem]
  exact (show q0 ∈ region by simp [region, forbidden, q0])

theorem basinHasTwoStates :
    BasinHasTwoStates spec := by
  refine ⟨q0, ?_, q1, ?_, ?_⟩
  · simp [spec, basin]
  · simp [spec, basin]
  · decide

theorem assumption41 :
    Assumption41 baseline spec referenceMeasure := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨q0, by simp [spec, basin]⟩
  · right
    change 0 < referenceMeasure region
    calc
      0 < Measure.count ({q0} : Set Y) := by simp
      _ ≤ referenceMeasure region := by
        exact measure_mono (by simp [region, q0, forbidden])
  · refine ⟨q0, ?_, q1, ?_, ?_⟩
    · simp [spec, region, q0, forbidden]
    · simp [spec, region, q1, forbidden]
    · decide
  · exact two_states_implies_basinPathLawNontrivial
      baseline spec basinHasTwoStates

noncomputable def comparison : ConstitutiveComparisonSet baseline spec where
  states := basin
  states_measurable := MeasurableSet.of_discrete
  states_subset_basin := by intro y hy; exact hy
  pathLawNontrivial := by
    exact assumption41.2.2.2

end BooleanBaseline
end GrammarRobust
end PermanssonResearch
