import PermanssonResearch.RegimeExit.ExitAdversaries
import PermanssonResearch.ConstitutiveQuasi.TrajectoryHelpers
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Tactic

/-!
# C-Exit — exact two-step destination witness on real typed alpha/P/U kernel

The generic routing theorems are already independent of finite matrices.
Here we compute F1's second transition using the actual *killed* kernel:
from b, killed K is (1/2) dirac b. The second exit contribution is
(1/2)*(1/3)=1/6, so R^2(b,{a})=1/3+1/6=1/2.
No unverified numeric four-corner table is admitted as a proof.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit.ExitFiniteWitness

open PermanssonLean PermanssonLean.RegimeSpecification
open PermanssonResearch.RegimeExit.ExitModels
open PermanssonResearch.RegimeExit.ExitAdversaries
open PermanssonResearch.ReverseSolver
open PermanssonResearch.ReverseSolver.FiniteStrategicRealization

def b : Y3 := decode (0 : Fin 3)
def destinationA : Set Y3 := encode ⁻¹' ({1} : Set (Fin 3))

theorem f1_region_eq_singleton :
    f1Spec.region = ({b} : Set Y3) := by
  ext y
  rcases y with ⟨s,x⟩
  cases s
  simp [f1Spec, b, decode]

theorem f1_destinationA_outside :
    destinationA \ f1Spec.region = destinationA := by
  ext y
  constructor
  · intro hy
    exact hy.1
  · intro hy
    refine ⟨hy, ?_⟩
    have h : y.2 = (1 : Fin 3) := by
      simpa [destinationA, encode] using hy
    change y.2 ≠ (0 : Fin 3)
    simp [h]

/-- The genuine state-space kernel has probability 1/2 to remain in b. -/
theorem f1_kernel_b_to_b :
    f1Model.inducedKernel b ({b} : Set Y3) = (1/2 : ℝ≥0∞) := by
  have hB : ({b} : Set Y3) =
      encode ⁻¹' ({0} : Set (Fin 3)) := by
    ext y
    rcases y with ⟨s,x⟩
    cases s
    simp [b, decode, encode]
  rw [hB]
  change (realizedModel f1Matrix).inducedKernel (decode 0)
    (encode ⁻¹' ({0} : Set (Fin 3))) = _
  rw [inducedKernel_encodedEntry f1Matrix 0 0]
  norm_num [f1Matrix]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- The actual output-restricted kernel at b has one Dirac atom, mass 1/2. -/
theorem f1_killed_b_eq_half_dirac :
    killedKernel f1Model f1Spec b =
      (1/2 : ℝ≥0∞) • Measure.dirac b := by
  rw [killedKernel, Kernel.restrict_apply,
    f1_region_eq_singleton, Measure.restrict_singleton]
  rw [f1_kernel_b_to_b]

/-- This is a genuine second-transition path-law contribution, not the
postulated transition-matrix recursion alone. -/
theorem f1_second_step_to_a :
    firstExitStepMass f1Model f1Spec 1 b destinationA =
      (1/6 : ℝ≥0∞) := by
  have hD : MeasurableSet destinationA := MeasurableSet.of_discrete
  change (exitSubkernel f1Model f1Spec ∘ₘ
      ((killedKernel f1Model f1Spec) ^ 1) b) destinationA = _
  rw [pow_one, f1_killed_b_eq_half_dirac, Measure.comp_smul,
    Measure.smul_apply, smul_eq_mul]
  have hDirac : exitSubkernel f1Model f1Spec ∘ₘ Measure.dirac b =
      exitSubkernel f1Model f1Spec b :=
    PermanssonResearch.ConstitutiveQuasi.kernel_comp_dirac
      (exitSubkernel f1Model f1Spec) b
  rw [hDirac, exitSubkernel_apply f1Model f1Spec b hD,
    f1_destinationA_outside]
  change (1/2 : ℝ≥0∞) *
      f1Model.inducedKernel (decode (0 : Fin 3))
        (encode ⁻¹' ({1} : Set (Fin 3))) = 1/6
  rw [f1_kernel_b_to_a]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
  norm_num only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat, one_div]
  rw [← ENNReal.mul_inv
    (a := (2 : ℝ≥0∞)) (b := (3 : ℝ≥0∞))
    (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  norm_num

/-- Two-transition first-exit destination probability is exactly 1/2. -/
theorem f1_two_step_to_a :
    exitRoutingFinite f1Model f1Spec 2 b destinationA =
      (1/2 : ℝ≥0∞) := by
  have hD : MeasurableSet destinationA := MeasurableSet.of_discrete
  have hstep := exitRoutingFinite_succ f1Model f1Spec 1 b destinationA hD
  change exitRoutingFinite f1Model f1Spec 2 b destinationA =
    exitRoutingFinite f1Model f1Spec 1 b destinationA +
      firstExitStepMass f1Model f1Spec 1 b destinationA at hstep
  rw [hstep]
  change exitRoutingFinite f1Model f1Spec 1 (decode (0 : Fin 3))
      (encode ⁻¹' ({1} : Set (Fin 3))) +
      firstExitStepMass f1Model f1Spec 1 b destinationA = 1/2
  rw [f1_one_step_to_a, f1_second_step_to_a]
  have h6 : (1/6 : ℝ≥0∞) = ENNReal.ofReal (1/6 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 6)]
    norm_num
  have h2 : (1/2 : ℝ≥0∞) = ENNReal.ofReal (1/2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [h6, h2, ← ENNReal.ofReal_add
    (by norm_num : 0 ≤ (1/3 : ℝ))
    (by norm_num : 0 ≤ (1/6 : ℝ))]
  norm_num

end PermanssonResearch.RegimeExit.ExitFiniteWitness
