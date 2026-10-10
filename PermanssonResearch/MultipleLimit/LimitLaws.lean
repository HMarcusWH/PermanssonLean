import PermanssonResearch.MultipleLimit.RandomLimit
import Mathlib.Tactic

/-!
# Lane C1 — law of a random limiting Dirac measure

For any *already established* distribution of the absorbing endpoint,
the measure-valued random limit has the exact pushforward law. This
separates the random object and its distribution from an averaged state
occupation measure. A kernel-to-hitting-distribution proof is needed to
instantiate a particular endpoint distribution.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit

open PermanssonLean.PeriodicExactGR

/-- The measure-valued law of the terminal Dirac distribution, given
a probability distribution on the absorbing endpoints. -/
noncomputable def randomLimitLaw (endpointLaw : ProbabilityMeasure Y) :
    ProbabilityMeasure (ProbabilityMeasure Y) :=
  endpointLaw.map terminalLaw

/-- The random measure law assigns any measurable set exactly its
preimage mass under the terminal-state-to-Dirac map. -/
theorem randomLimitLaw_apply
    (endpointLaw : ProbabilityMeasure Y)
    (E : Set (ProbabilityMeasure Y)) (hE : MeasurableSet E) :
    (randomLimitLaw endpointLaw).toMeasure E =
      endpointLaw.toMeasure (terminalLaw ⁻¹' E) := by
  change (Measure.map terminalLaw endpointLaw.toMeasure) E =
    endpointLaw.toMeasure (terminalLaw ⁻¹' E)
  exact Measure.map_apply (Measurable.of_discrete _) hE

/-- Distinct terminal states produce distinct measure-valued limits,
so the mapping does not silently average incompatible outcomes. -/
theorem terminalLaw_injective : Function.Injective terminalLaw := by
  intro a b h
  have hh : diracProba a = diracProba b := h
  exact injective_diracProba hh

/-- Exact event weight for any measurable singleton in the random
measure space. -/
theorem randomLimitLaw_singleton_weight
    (endpointLaw : ProbabilityMeasure Y) (a : Y)
    (ha : MeasurableSet ({terminalLaw a} : Set (ProbabilityMeasure Y))) :
    (randomLimitLaw endpointLaw).toMeasure {terminalLaw a} =
      endpointLaw.toMeasure {a} := by
  rw [randomLimitLaw_apply endpointLaw _ ha]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  exact terminalLaw_injective.eq_iff

end MultipleLimit
end PermanssonResearch
