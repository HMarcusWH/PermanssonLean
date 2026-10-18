import PermanssonResearch.ReverseSolver.StationaryOccupationObjective
import PermanssonResearch.ReverseSolver.ControlledKernel
import Mathlib.Data.List.Lex
import Mathlib.Data.List.OfFn

/-!
# Total exact optimization over all admissible deterministic stationary policies

The finite product enumerates one admissible control per physical state.
Scores use the actual induced feedback matrix, its own computed bottom
classes, C10 absorption, and the certified exact class functional evaluator.
Lexicographic control-list order resolves ties. The final theorem compares
expectations under the actual infinite path laws of all stationary policies.
-/

namespace PermanssonResearch.ReverseSolver.StationaryOccupation

open ControlledKernel

variable {C : Type*} [Fintype C] [DecidableEq C] [LinearOrder C]
variable {n : ℕ} [NeZero n]
variable {H : Type*} [MeasurableSpace H] [TopologicalSpace H] [BorelSpace H]

abbrev StationaryChoice (sys : FiniteControlSystem C n) :=
  {f : Fin n → C // ∀ y, f y ∈ sys.options y}

instance stationaryChoice_nonempty (sys : FiniteControlSystem C n) :
    Nonempty (StationaryChoice sys) :=
  ⟨⟨fun y => (sys.options y).min' (sys.options_nonempty y),
    fun y => Finset.min'_mem _ _⟩⟩

instance stationaryChoice_linearOrder (sys : FiniteControlSystem C n) :
    LinearOrder (StationaryChoice sys) :=
  LinearOrder.lift' (fun π : StationaryChoice sys => List.ofFn π.val)
    (fun _ _ he => Subtype.ext (List.ofFn_injective he))

def StationaryChoice.toFeedback {sys : FiniteControlSystem C n}
    (π : StationaryChoice sys) : StateFeedback sys where
  choose := π.val
  permitted := π.property

def feedbackToChoice {sys : FiniteControlSystem C n}
    (π : StateFeedback sys) : StationaryChoice sys := ⟨π.choose,π.permitted⟩

def stationaryScore (F : ExactClassFunctional n H) (sys : FiniteControlSystem C n)
    (y : Fin n) (π : StationaryChoice sys) : ℚ :=
  rationalObjective F (feedbackMatrix sys π.toFeedback) y

def stationaryMaximum (F : ExactClassFunctional n H) (sys : FiniteControlSystem C n)
    (y : Fin n) : ℚ :=
  ((Finset.univ : Finset (StationaryChoice sys)).image (stationaryScore F sys y)).max'
    (Finset.univ_nonempty.image _)

def maximizingStationaryChoices (F : ExactClassFunctional n H)
    (sys : FiniteControlSystem C n) (y : Fin n) : Finset (StationaryChoice sys) :=
  Finset.univ.filter (fun π => stationaryScore F sys y π=stationaryMaximum F sys y)

theorem maximizingStationaryChoices_nonempty (F : ExactClassFunctional n H)
    (sys : FiniteControlSystem C n) (y : Fin n) :
    (maximizingStationaryChoices F sys y).Nonempty := by
  have hm := Finset.max'_mem
    ((Finset.univ : Finset (StationaryChoice sys)).image (stationaryScore F sys y))
    (Finset.univ_nonempty.image _)
  obtain ⟨π,hπ,he⟩ := Finset.mem_image.mp hm
  exact ⟨π,Finset.mem_filter.mpr ⟨hπ,he⟩⟩

def computedStationaryChoice (F : ExactClassFunctional n H)
    (sys : FiniteControlSystem C n) (y : Fin n) : StationaryChoice sys :=
  (maximizingStationaryChoices F sys y).min'
    (maximizingStationaryChoices_nonempty F sys y)

def computedStationaryPolicy (F : ExactClassFunctional n H)
    (sys : FiniteControlSystem C n) (y : Fin n) : StateFeedback sys :=
  (computedStationaryChoice F sys y).toFeedback

theorem computedStationaryChoice_attains (F : ExactClassFunctional n H)
    (sys : FiniteControlSystem C n) (y : Fin n) :
    stationaryScore F sys y (computedStationaryChoice F sys y)=stationaryMaximum F sys y := by
  have hm := Finset.min'_mem (maximizingStationaryChoices F sys y)
    (maximizingStationaryChoices_nonempty F sys y)
  exact (Finset.mem_filter.mp hm).2

theorem stationaryScore_le_maximum (F : ExactClassFunctional n H)
    (sys : FiniteControlSystem C n) (y : Fin n) (π : StationaryChoice sys) :
    stationaryScore F sys y π≤stationaryMaximum F sys y :=
  Finset.le_max' _ _ (Finset.mem_image.mpr ⟨π,Finset.mem_univ _,rfl⟩)

/-- The generated policy maximizes the exact expected functional of the
actual random descriptor occupation limit over the entire declared product
of deterministic stationary admissible policies. -/
theorem stationary_menu_actual_optimal_and_attained (F : ExactClassFunctional n H)
    (sys : FiniteControlSystem C n) (y : Fin n) :
    (∀ π : StateFeedback sys,
      actualObjective F (feedbackMatrix sys π) y≤
        actualObjective F (feedbackMatrix sys (computedStationaryPolicy F sys y)) y) ∧
    actualObjective F (feedbackMatrix sys (computedStationaryPolicy F sys y)) y=
      (stationaryMaximum F sys y : ℝ) := by
  have hattain : rationalObjective F
      (feedbackMatrix sys (computedStationaryPolicy F sys y)) y=stationaryMaximum F sys y :=
    computedStationaryChoice_attains F sys y
  constructor
  · intro π
    rw [← rationalObjective_eq_actual,← rationalObjective_eq_actual,hattain]
    exact_mod_cast stationaryScore_le_maximum F sys y (feedbackToChoice π)
  · rw [← rationalObjective_eq_actual,hattain]

end PermanssonResearch.ReverseSolver.StationaryOccupation
