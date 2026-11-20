import PermanssonResearch.ReverseSolver.CommittedVsRectangularPathFixture
import PermanssonResearch.ReverseSolver.RectangularGameLaw

/-!
# Original D-05: the explicit two-stage example as a rectangular game

This additive verification source preserves all earlier providers and decisions.
It instantiates the existing actual-law saddle theorem with one controller
action, two model rows, two physical states, and horizon two. State zero is
absorbing failure; state one is survival. At time zero the original false stage
flag is used, and at every later time the true flag is used. Only horizon two
is asserted here.

The bridge preserves the original "both stages survived" event expectation.
The absorbing-state trace omits a raw second Bernoulli outcome after failure,
so no equality of differently typed full path laws is claimed. Behavioral
nature still ranges over arbitrary admitted real weights on complete histories.
-/

namespace PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum

open FiniteMonitor CommittedVsRectangular RectangularFiniteGame

def timeFlag (t : ℕ) : Bool := if t = 0 then false else true

theorem stageSuccess_nonnegative (θ second : Bool) :
    0 ≤ stageSuccess θ second := by
  cases θ <;> cases second <;> norm_num [stageSuccess]

theorem stageSuccess_le_one (θ second : Bool) :
    stageSuccess θ second ≤ 1 := by
  cases θ <;> cases second <;> norm_num [stageSuccess]

/-- Failure is absorbing. From survival, the original chosen row is sampled. -/
def stageMatrix (t : ℕ) (θ : Bool) : RationalMarkovMatrix 2 where
  entry y z := if y = 0 then (if z = 0 then 1 else 0)
    else if z = 0 then 1 - stageSuccess θ (timeFlag t)
    else stageSuccess θ (timeFlag t)
  entry_nonneg y z := by
    fin_cases y <;> fin_cases z
    · norm_num
    · norm_num
    · simpa using sub_nonneg.mpr (stageSuccess_le_one θ (timeFlag t))
    · simpa using stageSuccess_nonnegative θ (timeFlag t)
  row_sum_one y := by
    fin_cases y <;> simp [Fin.sum_univ_two]

def twoStageGame : Game Unit Bool 2 where
  states_nonempty := by decide
  options _ := Finset.univ
  options_nonempty _ := Finset.univ_nonempty
  natureOptions _ _ _ := Finset.univ
  nature_nonempty _ _ _ := Finset.univ_nonempty
  matrix t _ θ := stageMatrix t θ

def terminalAliveReward (y : Fin 2) : ℚ := if y = 1 then 1 else 0

/-- There is one action, so the existing maximizing controller is the sole
deterministic control. Its behavioral weight is identically one. -/
noncomputable def soleController : Controller twoStageGame :=
  maximizingController twoStageGame terminalAliveReward 2

theorem soleController_weight_one (t : ℕ) (h : History Unit Bool 2)
    (y : Fin 2) (c : Unit) : soleController.weight t h y c = 1 := by
  simp [soleController, maximizingController]

theorem every_controller_weight_one (σ : Controller twoStageGame) (t : ℕ)
    (h : History Unit Bool 2) (y : Fin 2) (c : Unit) : σ.weight t h y c = 1 := by
  simpa using σ.normalized t h y

theorem every_controller_eq_sole (σ : Controller twoStageGame) : σ = soleController := by
  have hw : σ.weight = soleController.weight := by
    funext t h y c
    rw [every_controller_weight_one, soleController_weight_one]
  have ext : ∀ a b : Controller twoStageGame, a.weight = b.weight → a = b := by
    intro a b hh
    cases a
    cases b
    cases hh
    rfl
  exact ext σ soleController hw

/-- Fix the first and second model selections in advance. The later extension
keeps the second model, but only the two-stage payoff is used below. -/
noncomputable def stageNature (θ₀ θ₁ : Bool) : Nature twoStageGame where
  weight t _ _ _ θ := if θ = (if t = 0 then θ₀ else θ₁) then 1 else 0
  nonnegative _ _ _ _ _ := by split_ifs <;> norm_num
  normalized _ _ _ _ := by simp
  supported _ _ _ _ θ hθ := False.elim (hθ (Finset.mem_univ θ))

theorem maximizingControl_eq_unit (v : Fin 2 → ℚ) (t : ℕ) (y : Fin 2) :
    maximizingControl twoStageGame v t y = () := Subsingleton.elim _ _

/-- Concrete two-row minimum, independent of the implementation's choice of
an argmin when the scores tie. -/
theorem minScore_eq_min (v : Fin 2 → ℚ) (t : ℕ) (y : Fin 2) :
    minScore twoStageGame v t y () =
      min (rowScore twoStageGame v t y () false)
          (rowScore twoStageGame v t y () true) := by
  apply le_antisymm
  · exact le_min
      (minScore_le_row twoStageGame v t y () false (Finset.mem_univ _))
      (minScore_le_row twoStageGame v t y () true (Finset.mem_univ _))
  · unfold minScore
    cases minimizingRow twoStageGame v t y ()
    · exact min_le_left _ _
    · exact min_le_right _ _

/-- The original event and the absorbing-state game's terminal survival have
equal expectations for every one of the four fixed row-pair selections. -/
theorem path_event_eq_game_payoff (θ₀ θ₁ : Bool) :
    (pathLaw θ₀ θ₁).expectation survivesBoth =
      lawPayoff twoStageGame terminalAliveReward soleController
        (stageNature θ₀ θ₁) 2 1 := by
  rw [lawPayoff, gameLaw_expectation, gameExpectation_eq_continuation]
  cases θ₀ <;> cases θ₁ <;>
    norm_num [FiniteProbabilityLaw.expectation, pathLaw, pathAtom, stageSuccess,
      survivesBoth, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_two,
      continuation, soleController_weight_one, stageNature, twoStageGame,
      stageMatrix, terminalAliveReward, timeFlag]

theorem committed_game_payoff (θ : Bool) :
    lawPayoff twoStageGame terminalAliveReward soleController
      (stageNature θ θ) 2 1 = 9 / 100 := by
  rw [← path_event_eq_game_payoff]
  cases θ
  · exact committed_false_actual_success
  · exact committed_true_actual_success

/-- Bellman's value of the complete admitted rectangular strategy class. -/
theorem rectangular_game_value :
    RectangularFiniteGame.value twoStageGame terminalAliveReward 2 0 1 = 1 / 100 := by
  simp only [RectangularFiniteGame.value, maximizingControl_eq_unit, minScore_eq_min]
  norm_num [rowScore, twoStageGame, stageMatrix, terminalAliveReward, timeFlag,
    stageSuccess, Fin.sum_univ_two]

/-- The lower bound quantifies over all admitted real behavioral, full-history
nature strategies, not only the four deterministic row pairs. -/
theorem rectangular_nature_payoff_lower (η : Nature twoStageGame) :
    (1 / 100 : ℝ) ≤
      lawPayoff twoStageGame terminalAliveReward soleController η 2 1 := by
  have h := (rectangular_game_law_saddle twoStageGame terminalAliveReward 2 1).2.1 η
  rw [rectangular_game_value] at h
  simpa [soleController] using h

/-- The specified false-then-true nature attains the universal lower bound. -/
theorem switching_nature_payoff :
    lawPayoff twoStageGame terminalAliveReward soleController
      (stageNature false true) 2 1 = 1 / 100 := by
  rw [← path_event_eq_game_payoff]
  exact rectangular_actual_success

/-- Every behavioral controller is the same one-action controller. This packages
the actual universal lower bound and its deterministic rectangular attainer. -/
theorem rectangular_actual_minimum :
    (∀ (σ : Controller twoStageGame) (η : Nature twoStageGame),
      (1 / 100 : ℝ) ≤ lawPayoff twoStageGame terminalAliveReward σ η 2 1) ∧
    (∀ σ : Controller twoStageGame,
      lawPayoff twoStageGame terminalAliveReward σ (stageNature false true) 2 1 =
        1 / 100) := by
  constructor
  · intro σ η
    rw [every_controller_eq_sole σ]
    exact rectangular_nature_payoff_lower η
  · intro σ
    rw [every_controller_eq_sole σ]
    exact switching_nature_payoff

theorem committed_game_minimum :
    min (lawPayoff twoStageGame terminalAliveReward soleController
          (stageNature false false) 2 1)
        (lawPayoff twoStageGame terminalAliveReward soleController
          (stageNature true true) 2 1) = 9 / 100 := by
  rw [committed_game_payoff, committed_game_payoff]
  exact min_self _

/-- Equality of the success-event values does not identify whole path laws. -/
theorem committed_false_off_event_atom :
    (pathLaw false false).atom (false, true) = 81 / 100 := by
  norm_num [pathLaw, pathAtom, stageSuccess]

theorem committed_true_off_event_atom :
    (pathLaw true true).atom (false, true) = 1 / 100 := by
  norm_num [pathLaw, pathAtom, stageSuccess]

theorem committed_path_laws_differ : pathLaw false false ≠ pathLaw true true := by
  intro h
  have he := congrArg (fun law : FiniteProbabilityLaw (Bool × Bool) =>
    law.atom (false, true)) h
  rw [committed_false_off_event_atom, committed_true_off_event_atom] at he
  norm_num at he

end PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum

-- Existing original criterion, path law, and rectangular actual-law providers.
#check PermanssonResearch.ReverseSolver.FiniteMonitor.FiniteProbabilityLaw
#print axioms PermanssonResearch.ReverseSolver.FiniteMonitor.FiniteProbabilityLaw
#check PermanssonResearch.ReverseSolver.FiniteMonitor.FiniteProbabilityLaw.expectation
#print axioms PermanssonResearch.ReverseSolver.FiniteMonitor.FiniteProbabilityLaw.expectation
#check PermanssonResearch.ReverseSolver.SolverBoundaryWitnesses.whole_model_commitment_strictly_exceeds_rectangular
#print axioms PermanssonResearch.ReverseSolver.SolverBoundaryWitnesses.whole_model_commitment_strictly_exceeds_rectangular
#check PermanssonResearch.ReverseSolver.CommittedVsRectangular.stageSuccess
#print axioms PermanssonResearch.ReverseSolver.CommittedVsRectangular.stageSuccess
#check PermanssonResearch.ReverseSolver.CommittedVsRectangular.pathAtom
#print axioms PermanssonResearch.ReverseSolver.CommittedVsRectangular.pathAtom
#check PermanssonResearch.ReverseSolver.CommittedVsRectangular.pathLaw
#print axioms PermanssonResearch.ReverseSolver.CommittedVsRectangular.pathLaw
#check PermanssonResearch.ReverseSolver.CommittedVsRectangular.survivesBoth
#print axioms PermanssonResearch.ReverseSolver.CommittedVsRectangular.survivesBoth
#check PermanssonResearch.ReverseSolver.CommittedVsRectangular.committed_false_actual_success
#print axioms PermanssonResearch.ReverseSolver.CommittedVsRectangular.committed_false_actual_success
#check PermanssonResearch.ReverseSolver.CommittedVsRectangular.committed_true_actual_success
#print axioms PermanssonResearch.ReverseSolver.CommittedVsRectangular.committed_true_actual_success
#check PermanssonResearch.ReverseSolver.CommittedVsRectangular.rectangular_actual_success
#print axioms PermanssonResearch.ReverseSolver.CommittedVsRectangular.rectangular_actual_success
#check PermanssonResearch.ReverseSolver.CommittedVsRectangular.committed_vs_rectangular_separate_on_path_laws
#print axioms PermanssonResearch.ReverseSolver.CommittedVsRectangular.committed_vs_rectangular_separate_on_path_laws
#check PermanssonResearch.ReverseSolver.RectangularFiniteGame.Game
#print axioms PermanssonResearch.ReverseSolver.RectangularFiniteGame.Game
#check PermanssonResearch.ReverseSolver.RectangularFiniteGame.Controller
#print axioms PermanssonResearch.ReverseSolver.RectangularFiniteGame.Controller
#check PermanssonResearch.ReverseSolver.RectangularFiniteGame.Nature
#print axioms PermanssonResearch.ReverseSolver.RectangularFiniteGame.Nature
#check PermanssonResearch.ReverseSolver.RectangularFiniteGame.value
#print axioms PermanssonResearch.ReverseSolver.RectangularFiniteGame.value
#check PermanssonResearch.ReverseSolver.RectangularFiniteGame.gameMass
#print axioms PermanssonResearch.ReverseSolver.RectangularFiniteGame.gameMass
#check PermanssonResearch.ReverseSolver.RectangularFiniteGame.gameLaw
#print axioms PermanssonResearch.ReverseSolver.RectangularFiniteGame.gameLaw
#check PermanssonResearch.ReverseSolver.RectangularFiniteGame.lawPayoff
#print axioms PermanssonResearch.ReverseSolver.RectangularFiniteGame.lawPayoff
#check PermanssonResearch.ReverseSolver.RectangularFiniteGame.gameMass_nonnegative
#print axioms PermanssonResearch.ReverseSolver.RectangularFiniteGame.gameMass_nonnegative
#check PermanssonResearch.ReverseSolver.RectangularFiniteGame.gameMass_total_one
#print axioms PermanssonResearch.ReverseSolver.RectangularFiniteGame.gameMass_total_one
#check PermanssonResearch.ReverseSolver.RectangularFiniteGame.gameExpectation_eq_continuation
#print axioms PermanssonResearch.ReverseSolver.RectangularFiniteGame.gameExpectation_eq_continuation
#check PermanssonResearch.ReverseSolver.RectangularFiniteGame.gameLaw_expectation
#print axioms PermanssonResearch.ReverseSolver.RectangularFiniteGame.gameLaw_expectation
#check PermanssonResearch.ReverseSolver.RectangularFiniteGame.rectangular_game_actual_saddle
#print axioms PermanssonResearch.ReverseSolver.RectangularFiniteGame.rectangular_game_actual_saddle
#check PermanssonResearch.ReverseSolver.RectangularFiniteGame.rectangular_game_law_saddle
#print axioms PermanssonResearch.ReverseSolver.RectangularFiniteGame.rectangular_game_law_saddle

-- Complete additive concrete-game construction and theorem coverage.
#check PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.timeFlag
#print axioms PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.timeFlag
#check PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.stageSuccess_nonnegative
#print axioms PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.stageSuccess_nonnegative
#check PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.stageSuccess_le_one
#print axioms PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.stageSuccess_le_one
#check PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.stageMatrix
#print axioms PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.stageMatrix
#check PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.twoStageGame
#print axioms PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.twoStageGame
#check PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.terminalAliveReward
#print axioms PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.terminalAliveReward
#check PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.soleController
#print axioms PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.soleController
#check PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.soleController_weight_one
#print axioms PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.soleController_weight_one
#check PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.every_controller_weight_one
#print axioms PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.every_controller_weight_one
#check PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.every_controller_eq_sole
#print axioms PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.every_controller_eq_sole
#check PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.stageNature
#print axioms PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.stageNature
#check PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.maximizingControl_eq_unit
#print axioms PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.maximizingControl_eq_unit
#check PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.minScore_eq_min
#print axioms PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.minScore_eq_min
#check PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.path_event_eq_game_payoff
#print axioms PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.path_event_eq_game_payoff
#check PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.committed_game_payoff
#print axioms PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.committed_game_payoff
#check PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.rectangular_game_value
#print axioms PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.rectangular_game_value
#check PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.rectangular_nature_payoff_lower
#print axioms PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.rectangular_nature_payoff_lower
#check PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.switching_nature_payoff
#print axioms PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.switching_nature_payoff
#check PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.rectangular_actual_minimum
#print axioms PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.rectangular_actual_minimum
#check PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.committed_game_minimum
#print axioms PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.committed_game_minimum
#check PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.committed_false_off_event_atom
#print axioms PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.committed_false_off_event_atom
#check PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.committed_true_off_event_atom
#print axioms PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.committed_true_off_event_atom
#check PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.committed_path_laws_differ
#print axioms PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum.committed_path_laws_differ
