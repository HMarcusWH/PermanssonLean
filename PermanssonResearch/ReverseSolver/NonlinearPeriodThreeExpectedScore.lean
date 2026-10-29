import PermanssonResearch.ReverseSolver.NonlinearPeriodThreeClassGeometry
import PermanssonResearch.ReverseSolver.NonlinearBooleanClassFunctional
import Mathlib.Tactic

/-!
Actual infinite-path nonlinear-score conditional bridge. Neither the
true stationary class nor the four policy-specific class identifications
is asserted from finite-orbit arithmetic; those must be discharged.
-/
open MeasureTheory ProbabilityTheory
namespace PermanssonResearch.ReverseSolver.NonlinearPeriodThree
open PermanssonResearch.MultipleLimit.FiniteOccupationRandomLaw
attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

theorem actual_phase_aware_score_one_of_canonical_true_mass
    (htrue :
      (((physicalOccupationLimit
        (typedModel phaseAwarePolicy).inducedKernel
          (nativeOrbit phaseAwarePolicy)).map Prod.snd).toMeasure {true}).toReal =
            (2/3 : ℝ)) :
    nativeExpectedNonlinearScore phaseAwarePolicy = 1 := by
  rw [native_expected_score_eq_actual_orbit]
  exact boolean_probability_score_of_true_mass _ htrue

theorem actual_phase_blind_score_le_of_class_identification
    (policy : Bool → Bool)
    (hclass :
      nativeNonlinearPathScore (phaseBlindPolicy policy)
        (nativeOrbit (phaseBlindPolicy policy)) =
          (booleanRationalScore (nativePhaseBlindTailShare policy) : ℝ)) :
    nativeExpectedNonlinearScore (phaseBlindPolicy policy) ≤ 5/6 := by
  rw [native_expected_score_eq_actual_orbit, hclass]
  have hbound : booleanRationalScore (nativePhaseBlindTailShare policy) ≤ (5/6 : ℚ) :=
    native_phase_blind_tail_score_le_five_sixths policy
  have hr : ((booleanRationalScore (nativePhaseBlindTailShare policy) : ℚ) : ℝ) ≤
      (((5/6 : ℚ) : ℝ)) := by
    exact_mod_cast hbound
  simpa only [show (((5/6 : ℚ) : ℝ)) = (5/6 : ℝ) by norm_num] using hr

theorem actual_restricted_gap_of_identified_classes
    (htrue :
      (((physicalOccupationLimit
        (typedModel phaseAwarePolicy).inducedKernel
          (nativeOrbit phaseAwarePolicy)).map Prod.snd).toMeasure {true}).toReal =
            (2/3 : ℝ))
    (hclasses : ∀ policy : Bool → Bool,
      nativeNonlinearPathScore (phaseBlindPolicy policy)
        (nativeOrbit (phaseBlindPolicy policy)) =
          (booleanRationalScore (nativePhaseBlindTailShare policy) : ℝ))
    (policy : Bool → Bool) :
    nativeExpectedNonlinearScore (phaseBlindPolicy policy) <
      nativeExpectedNonlinearScore phaseAwarePolicy := by
  rw [actual_phase_aware_score_one_of_canonical_true_mass htrue]
  have hb := actual_phase_blind_score_le_of_class_identification policy (hclasses policy)
  linarith

theorem native_phase_aware_actual_score_one :
    nativeExpectedNonlinearScore phaseAwarePolicy = 1 :=
  actual_phase_aware_score_one_of_canonical_true_mass
    native_phase_aware_actual_true_mass


end PermanssonResearch.ReverseSolver.NonlinearPeriodThree
