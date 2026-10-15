import PermanssonResearch.RegimeExit.ExitRouting
import PermanssonLean.Regime.Persistence
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Tactic

/-!
# C-Exit — law-started indefinite survival as a decreasing limit

The frozen core supplies finite-horizon survival for an arbitrary initial
probability law but only point-started survival forever. The research-only
law-started API introduced in ExitRouting is characterized here by the
actual decreasing measurable path events; no limiting equality is assumed.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory Topology

namespace PermanssonResearch.RegimeExit

universe uS uX uA uH
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]
open PermanssonLean PermanssonLean.RegimeSpecification

/-- The law-initialized forever survival is the exact infimum of its
finite-horizon survival probabilities, not a numerical approximation. -/
theorem survivalForeverProbabilityFromLaw_eq_iInf_survival
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X)) :
    survivalForeverProbabilityFromLaw M spec μ =
      ⨅ n : ℕ, survivalProbabilityFromLaw M spec μ n := by
  let P := M.pathLaw μ.toMeasure
  have hmeas : ∀ n : ℕ, NullMeasurableSet (survivesThroughSet spec n) P :=
    fun n => (measurableSet_survivesThroughSet spec n).nullMeasurableSet
  have hfinite : ∃ n : ℕ, P (survivesThroughSet spec n) ≠ ⊤ :=
    ⟨0, measure_ne_top P _⟩
  have h := (survivesThroughSet_antitone spec).measure_iInter
    (μ := P) hmeas hfinite
  change (M.pathLaw μ.toMeasure) (⋂ n, survivesThroughSet spec n) =
    ⨅ n, (M.pathLaw μ.toMeasure) (survivesThroughSet spec n) at h
  simpa only [survivalForeverProbabilityFromLaw, survivalProbabilityFromLaw,
    survivesForeverSet_eq_iInter] using h

/-- Continuity from above gives a genuine probabilistic horizon limit
for every starting probability law, without all-state exit assumptions. -/
theorem survivalProbabilityFromLaw_tendsto_forever
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X)) :
    Tendsto (fun n : ℕ => survivalProbabilityFromLaw M spec μ n)
      atTop (𝓝 (survivalForeverProbabilityFromLaw M spec μ)) := by
  let P := M.pathLaw μ.toMeasure
  have hmeas : ∀ n : ℕ, NullMeasurableSet (survivesThroughSet spec n) P :=
    fun n => (measurableSet_survivesThroughSet spec n).nullMeasurableSet
  have hfinite : ∃ n : ℕ, P (survivesThroughSet spec n) ≠ ⊤ :=
    ⟨0, measure_ne_top P _⟩
  have h := tendsto_measure_iInter_atTop
    (μ := P) hmeas (survivesThroughSet_antitone spec) hfinite
  change Tendsto
    (fun n : ℕ => (M.pathLaw μ.toMeasure) (survivesThroughSet spec n))
    atTop
    (𝓝 ((M.pathLaw μ.toMeasure) (⋂ n, survivesThroughSet spec n))) at h
  simpa only [survivalForeverProbabilityFromLaw, survivalProbabilityFromLaw,
    survivesForeverSet_eq_iInter] using h

end PermanssonResearch.RegimeExit
