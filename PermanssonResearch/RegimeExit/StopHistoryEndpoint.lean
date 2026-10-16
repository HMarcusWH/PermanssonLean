import PermanssonResearch.RegimeExit.StoppedFutureSubmeasure
import PermanssonResearch.RegimeExit.SwitchRestart
import Mathlib.Tactic

/-!
# C-Exit C — the actual first-exit history endpoint submeasure

This bridges the prefFn-restricted history distribution used by the
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

/-- Push forward the GENUINE first-exit restricted prefFn through
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
      (firstExitStepMeasure N spec n y).restrict D := by
  let P := N.pathLaw (Measure.dirac y)
  let prefFn : (ℕ → JointState S X) →
      ((i : Finset.Iic (n+1)) → JointState S X) :=
    Preorder.frestrictLe (n+1)
  let Hn := firstExitHistoryAt spec n D
  let endpoint : ((i : Finset.Iic (n+1)) → JointState S X) →
      JointState S X :=
    fun h => h ⟨n+1, Finset.mem_Iic.mpr le_rfl⟩
  have hHn : MeasurableSet Hn :=
    firstExitHistoryAt_measurable spec n D hD
  have hPref : Measurable prefFn := by fun_prop
  have hEnd : Measurable endpoint := by fun_prop
  have hevent : prefFn ⁻¹' Hn =
      firstExitAtDestination spec n D := by
    exact (firstExitAt_eq_history_preimage spec n D).symm
  change ((P.map prefFn).restrict Hn).map endpoint =
      (firstExitStepMeasure N spec n y).restrict D
  calc
    ((P.map prefFn).restrict Hn).map endpoint =
        ((P.restrict (prefFn ⁻¹' Hn)).map prefFn).map endpoint := by
      rw [Measure.restrict_map hPref hHn]
    _ = (P.restrict (prefFn ⁻¹' Hn)).map (endpoint ∘ prefFn) := by
      rw [Measure.map_map hEnd hPref]
    _ = (P.restrict (firstExitAtDestination spec n D)).map
          (fun w : ℕ → JointState S X => w (n+1)) := by
      rw [hevent]
      rfl
    _ = (firstExitStepMeasure N spec n y).restrict D := by
      ext C hC
      rw [Measure.map_apply (measurable_pi_apply (n+1)) hC,
        Measure.restrict_apply
          (hC.preimage (measurable_pi_apply (n+1))),
        Measure.restrict_apply hC]
      have hIntersection :
          ((fun w : ℕ → JointState S X => w (n+1)) ⁻¹' C) ∩
              firstExitAtDestination spec n D =
            firstExitAtDestination spec n (D ∩ C) := by
        ext w
        simp only [firstExitAtDestination, Set.mem_inter_iff,
          Set.mem_preimage, Set.mem_diff, Set.mem_setOf_eq]
        tauto
      rw [hIntersection, Set.inter_comm C D]
      exact firstExitStep_eq_pathEvent
        N spec n hy (D ∩ C) (hD.inter hC)

end PermanssonResearch.RegimeExit
