import PermanssonResearch.ReverseSolver.NonlinearPolicyClassComparison
import PermanssonResearch.StrategicWorld.DeterministicOrbit
import PermanssonResearch.MultipleLimit.FiniteOccupationRandomLaw
import Mathlib.Tactic

/-!
NEXT-06.2: actual original infinite path law is Dirac at the native typed
Fin 3 × Bool orbit. This uses frozen model path-law uniqueness and the
proved all-six-state alpha-P-U kernel bridge, not simulated orbit values.
The nonlinear expectation reduces to the occupation functional evaluated
on this exact realized trajectory; identifying its physical stationary
mass still requires a separate class-specific proof.
-/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch.ReverseSolver.NonlinearPeriodThree
open PermanssonLean
open PermanssonResearch.StrategicWorld
open PermanssonResearch.MultipleLimit.FiniteOccupationRandomLaw
set_option autoImplicit false

/-- The recursive phase-state orbit is exactly the generic iterator used
in the existing deterministic canonical-path theorem. -/
theorem nativeOrbit_eq_detOrbit (policy : State → Bool) (n : ℕ) :
    nativeOrbit policy n =
      detOrbit (nextState policy) start n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [nativeOrbit, detOrbit_succ, ih]

/-- A genuine path probability identity, for any native deterministic
policy, on the original infinite path space, not only its finite marginals. -/
theorem native_pathLaw_dirac (policy : State → Bool) :
    (typedModel policy).pathLaw (Measure.dirac start) =
      Measure.dirac (nativeOrbit policy) := by
  have hK : ∀ y : State,
      (typedModel policy).inducedKernel y = Measure.dirac (nextState policy y) := by
    intro y
    rw [native_inducedKernel_eq_deterministic]
    rfl
  have h := pathLaw_dirac_of_deterministic
    (typedModel policy) (nextState policy) hK start
  rw [h]
  congr 1
  funext n
  exact (nativeOrbit_eq_detOrbit policy n).symm

/-- The fixed nonlinear property evaluated on a native pathwise actual
empirical occupation limit selected by the genuine finite-state kernel. -/
noncomputable def nativeNonlinearPathScore
    (policy : State → Bool) (w : ℕ → State) : ℝ :=
  booleanProbabilityScore
    ((physicalOccupationLimit (typedModel policy).inducedKernel w).map Prod.snd)

/-- Expected nonlinear score of the true ORIGINAL entire infinite canonical
path law, not of the barycenter of the class stationary measures. -/
noncomputable def nativeExpectedNonlinearScore (policy : State → Bool) : ℝ :=
  ∫ w, nativeNonlinearPathScore policy w ∂
    (typedModel policy).pathLaw (Measure.dirac start)

/-- Exact model-to-orbit equality on the actual path probability:
the only remaining mathematical identification is the true occupation
law of the deterministic reached class (not a numerical simulation). -/
theorem native_expected_score_eq_actual_orbit (policy : State → Bool) :
    nativeExpectedNonlinearScore policy =
      nativeNonlinearPathScore policy (nativeOrbit policy) := by
  unfold nativeExpectedNonlinearScore
  rw [native_pathLaw_dirac policy]
  simp

end PermanssonResearch.ReverseSolver.NonlinearPeriodThree
