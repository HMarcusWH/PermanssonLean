import PermanssonResearch.RegimeExit.ExitConservation
import PermanssonResearch.RegimeExit.QSDDestination
import PermanssonResearch.RegimeExit.ExitModels
import Mathlib.Tactic

/-!
# C-Exit adversaries — actual typed alpha -> P -> U witnesses

Only genuine induced kernels and previously constructed routing measures
are evaluated. These negative controls reject a claimed regime switch from
mere destination arrival. The independent Fraction suite has 22 cases.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit.ExitAdversaries

open PermanssonLean PermanssonLean.RegimeSpecification
open PermanssonResearch.ReverseSolver.FiniteStrategicRealization
open ExitModels

theorem f1_zero_horizon :
    exitRoutingFinite f1Model f1Spec 0 (decode (0 : Fin 3))
      (encode ⁻¹' ({1} : Set (Fin 3))) = 0 :=
  exitRoutingFinite_zero f1Model f1Spec (decode 0) _

theorem f1_one_step_to_a :
    exitRoutingFinite f1Model f1Spec 1 (decode (0 : Fin 3))
      (encode ⁻¹' ({1} : Set (Fin 3))) =
      ENNReal.ofReal (1/3 : ℝ) := by
  let D : Set Y3 := encode ⁻¹' ({1} : Set (Fin 3))
  have hD : MeasurableSet D := MeasurableSet.of_discrete
  have hOutside : D \ f1Spec.region = D := by
    ext y
    simp [D, f1Spec, encode]
    intro h
    simp [h]
  calc
    exitRoutingFinite f1Model f1Spec 1 (decode 0) D =
        firstExitStepMass f1Model f1Spec 0 (decode 0) D := by
      simpa [exitRoutingFinite_zero] using
        (exitRoutingFinite_succ f1Model f1Spec 0 (decode 0) D hD)
    _ = f1Model.inducedKernel (decode 0) D := by
      change (firstExitStepMeasure f1Model f1Spec 0 (decode 0)) D =
        f1Model.inducedKernel (decode 0) D
      rw [firstExitStepMeasure_zero, exitSubkernel_apply f1Model f1Spec
        (decode 0) hD, hOutside]
    _ = ENNReal.ofReal (1/3 : ℝ) := f1_kernel_b_to_a

theorem f4_arrival_without_invariance :
    f4Model.inducedKernel (decode (1 : Fin 4))
        (encode ⁻¹' ({2} : Set (Fin 4))) = 1 ∧
    f4Model.inducedKernel (decode (2 : Fin 4))
        (encode ⁻¹' ({2} : Set (Fin 4))) = 0 := by
  constructor
  · exact f4_kernel_d_to_a
  · change (realizedModel f4Matrix).inducedKernel (decode 2)
      (encode ⁻¹' ({2} : Set (Fin 4))) = 0
    rw [inducedKernel_encodedEntry f4Matrix 2 2]
    norm_num [f4Matrix]

/-- Full probability of landing in a is NOT an invariance certificate for a:
the world/action/update model exits a to c in the following transition. -/
theorem f4_destination_arrival_not_exact_persistence :
    f4Model.inducedKernel (decode (1 : Fin 4))
        (encode ⁻¹' ({2} : Set (Fin 4))) = 1 ∧
    f4Model.inducedKernel (decode (2 : Fin 4))
        (encode ⁻¹' ({3} : Set (Fin 4))) = 1 :=
  ⟨f4_kernel_d_to_a, f4_kernel_a_to_c⟩

end PermanssonResearch.RegimeExit.ExitAdversaries
