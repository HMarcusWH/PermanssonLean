import PermanssonResearch.RegimeExit.StoppedFutureSubmeasure
import PermanssonResearch.RegimeExit.SwitchRestart
import Mathlib.Tactic

/-!
# C-Exit C — the actual first-exit history endpoint submeasure

This bridges the prefix-restricted history distribution used by the
new future-path factorization to the pre-existing PR66 first-exit step
submeasure. This does NOT assume or assert that the full future
depends only on the endpoint; that is the outstanding stationary
Markov restart theorem.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit

set_option autoImplicit false
open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA uH
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X]
variable [MeasurableSpace A] [MeasurableSpace H]

/-- Push forward the GENUINE first-exit restricted prefix through
its last-state coordinate. This is the original first-exit step
measure, not a normalized arrival probability. -/
theorem firstExitHistory_endpointMeasure_eq_step
    (N : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) {y : JointState S X} (hy : y ∈ spec.region)
    (D : Set (JointState S X)) (hD : MeasurableSet D) :
    (((N.pathLaw (Measure.dirac y)).map
        (Preorder.frestrictLe (n+1))).restrict
        (firstExitHistoryAt spec n D)).map
          (fun h : (i : Finset.Iic (n+1)) → JointState S X =>
            h ⟨n+1, Finset.mem_Iic.mpr le_rfl⟩) =
      firstExitStepMeasure N spec n y := by
  let P := N.pathLaw (Measure.dirac y)
  let prefix : (ℕ → JointState S X) →
      ((i : Finset.Iic (n+1)) → JointState S X) :=
    Preorder.frestrictLe (n+1)
  let Hn := firstExitHistoryAt spec n D
  let endpoint : ((i : Finset.Iic (n+1)) → JointState S X) →
      JointState S X :=
    fun h => h ⟨n+1, Finset.mem_Iic.mpr le_rfl⟩
  have hHn : MeasurableSet Hn :=
    firstExitHistoryAt_measurable spec n D hD
  have hPref : Measurable prefix := by fun_prop
  have hEnd : Measurable endpoint := by fun_prop
  have hevent : prefix ⁻¹' Hn =
      firstExitAtDestination spec n D := by
    exact (firstExitAt_eq_history_preimage spec n D).symm
  change ((P.map prefix).restrict Hn).map endpoint =
      firstExitStepMeasure N spec n y
  calc
    ((P.map prefix).restrict Hn).map endpoint =
        ((P.restrict (prefix ⁻¹' Hn)).map prefix).map endpoint := by
      rw [Measure.restrict_map hPref hHn]
    _ = (P.restrict (prefix ⁻¹' Hn)).map (endpoint ∘ prefix) := by
      rw [Measure.map_map hEnd hPref]
    _ = (P.restrict (firstExitAtDestination spec n D)).map
          (fun w : ℕ → JointState S X => w (n+1)) := by
      rw [hevent]
      rfl
    _ = firstExitStepMeasure N spec n y := by
      exact firstExitArrivalEndpointMeasure_eq_step N spec n hy

end PermanssonResearch.RegimeExit
