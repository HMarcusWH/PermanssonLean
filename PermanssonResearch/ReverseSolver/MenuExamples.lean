import PermanssonResearch.ReverseSolver.FrozenMenu
import PermanssonLean.Examples.ConstitutiveNoninvariance

/-!
# D0: a concrete two-entry *typed* fixed strategic menu

The two entries choose either the original always-true action kernel or
the existing always-false admissible intervention. Their shared world
primitive is exactly modelB.world. This is a typed example, independent
of the exact-rational three-state executable fixture.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace PermanssonResearch
namespace ReverseSolver
namespace FrozenMenuExamples

open PermanssonLean
open PermanssonLean.Section7ConstitutiveNoninvariance

noncomputable section

def trueActionReplacement :
    InterventionReplacement Bool Bool Bool .actionSelection :=
  ⟨actionTrue, by unfold actionTrue; infer_instance⟩

def typedTrueAction : TypedIntervention familyB where
  component := ()
  replacement := trueActionReplacement

def trueActionIntervention : AdmissibleStrategicIntervention familyB where
  intervention := typedTrueAction
  accepted := by trivial
  strategic := by
    simp [TypedIntervention.IsStrategic, typedTrueAction, familyB]

/-- Two explicit entries; the unmodified baseline is included only because
the true-action replacement was deliberately put in the menu. -/
def twoChoiceMenu : FrozenMenu modelB familyB Bool where
  indices := Finset.univ
  nonempty := ⟨true, Finset.mem_univ _⟩
  choice := fun b => if b then interventionB else trueActionIntervention

/-- Reach world-bit true, without any forbidden states. -/
def reachTrue : FrozenHittingTarget (JointState Bool Bool) where
  goal := {y | y.2 = true}
  forbidden := ∅
  goal_measurable := by
    exact (measurable_snd : Measurable fun y : JointState Bool Bool => y.2)
      (measurableSet_singleton true)
  forbidden_measurable := MeasurableSet.empty
  disjoint := by simp

/-- The mathematical optimizer selects a member of the *declared*
two-element menu, not of an implicit universe of strategies. -/
theorem selected_in_twoChoiceMenu (y : JointState Bool Bool) (T : ℕ) :
    optimalMember twoChoiceMenu reachTrue y T ∈ twoChoiceMenu.indices :=
  optimalMember_mem twoChoiceMenu reachTrue y T

theorem selected_preserves_original_world (y : JointState Bool Bool) (T : ℕ) :
    (twoChoiceMenu.choice (optimalMember twoChoiceMenu reachTrue y T))
      .intervention.apply.world = modelB.world :=
  optimalMember_world_eq twoChoiceMenu reachTrue y T

end
end FrozenMenuExamples
end ReverseSolver
end PermanssonResearch
