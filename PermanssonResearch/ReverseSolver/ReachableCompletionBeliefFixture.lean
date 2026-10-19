import PermanssonResearch.ReverseSolver.BeliefChronology
import Mathlib.Tactic

/-!
# NEXT-06 / D-06 — different reachable augmented beliefs under one prior

One initial pure belief in the hidden completed flag is fixed before a fair
behavioral controller chooses either legal action. The hidden flag becomes
the actually realized action, but the physical observation is ALWAYS Unit.
Both distinct action/observation histories therefore occur with probability
1/2 in the SAME actual chronological law and produce different posteriors.
The controller observes its own chosen action, not the hidden state.
-/

open MeasureTheory
open scoped Classical

namespace PermanssonResearch.ReverseSolver.ReachableCompletionBelief
open PermanssonResearch.ReverseSolver.Belief

noncomputable section

/-- The hidden completion flag is updated by a legal observed action; the
only physical readout is a constant, uninformative Unit value. -/
def model : Model Bool Bool Unit where
  transition _ _ c := Distribution.pure c
  observation _ _ _ := Distribution.pure ()
  default := Distribution.pure false

/-- This is the SINGLE fixed initial law for both reachable histories. -/
def initial : Distribution Bool := Distribution.pure false

/-- A fair observation-admissible real behavioral policy, chosen without
access to the hidden flag. -/
def fairActions : Distribution Bool where
  weight _ := 1 / 2
  nonneg _ := by norm_num
  sum_one := by norm_num [Fintype.sum_bool]

def policy : ObservationPolicy Bool Unit where
  choose _ _ := fairActions

/-- Conditional on choosing either action, the next observable Unit readout
has probability one. Actual historical mass also includes the 1/2 action. -/
theorem both_observable_words_positive :
    (Model.actionWeight policy 0 [] [(false, ())] *
        model.likelihood 0 initial [(false, ())] = 1 / 2) ∧
    (Model.actionWeight policy 0 [] [(true, ())] *
        model.likelihood 0 initial [(true, ())] = 1 / 2) := by
  constructor <;>
    norm_num [Model.actionWeight, Model.likelihood, Model.branchMass,
      Model.numerator, policy, fairActions, model, initial,
      Distribution.pure, Fintype.sum_bool]

/-- Two events in ONE actual one-step chronological PMF have positive mass,
not two counterfactual initial priors or impossible posterior branches. -/
theorem both_histories_reachable_in_one_law :
    (∫ q, (if Samples.observable 1 q.2 = [(false, ())] then (1 : ℝ) else 0)
      ∂(model.chronologicalLaw 1 0 initial (policy.unfold 1 0 [])).pmf.toMeasure) =
        1 / 2 ∧
    (∫ q, (if Samples.observable 1 q.2 = [(true, ())] then (1 : ℝ) else 0)
      ∂(model.chronologicalLaw 1 0 initial (policy.unfold 1 0 [])).pmf.toMeasure) =
        1 / 2 := by
  constructor
  · calc
      _ = Model.actionWeight policy 0 [] [(false, ())] *
            model.likelihood 0 initial [(false, ())] := by
        simpa only [List.length_singleton] using
          (model.chronological_word_integral policy 0 [] initial [(false, ())])
      _ = 1 / 2 := both_observable_words_positive.1
  · calc
      _ = Model.actionWeight policy 0 [] [(true, ())] *
            model.likelihood 0 initial [(true, ())] := by
        simpa only [List.length_singleton] using
          (model.chronological_word_integral policy 0 [] initial [(true, ())])
      _ = 1 / 2 := both_observable_words_positive.2

/-- Same physical observation and fixed initial law, but different hidden
completed-flag beliefs. Both posteriors are conditional on POSITIVE events. -/
theorem reachable_posteriors_disagree :
    (model.filter 0 initial [(false, ())]).weight true = 0 ∧
    (model.filter 0 initial [(true, ())]).weight true = 1 := by
  constructor <;>
    norm_num [Model.filter, Model.posterior, Model.branchMass,
      Model.numerator, model, initial, Distribution.pure, Fintype.sum_bool]

theorem readout_cannot_reveal_completion (z₀ z₁ : Bool) (c : Bool) :
    model.observation 0 z₀ c = model.observation 0 z₁ c := rfl

end
end PermanssonResearch.ReverseSolver.ReachableCompletionBelief
