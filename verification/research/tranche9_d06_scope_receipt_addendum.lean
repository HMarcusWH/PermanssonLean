import PermanssonResearch.ReverseSolver.ReachableCompletionBeliefFixture
import verification.research.BeliefObservationWitness

/-!
# D-06 augmented-belief and reachable-history receipt addendum

The original finite belief model samples the chosen action, hidden successor,
and successor observation in that order. Its controller sees its own past
actions and observations, not the hidden augmented state. All controls belong
to the declared finite common menu; the monitored specialization proves that
each selected control is legal at every hidden physical state.

The new value bridge below uses the ONE original prior and the two positive
one-step histories in ReachableCompletionBeliefFixture. It evaluates immediate
terminal completion after those histories. A current Unit readout alone cannot
represent both values, whereas the full observed action/history filter can.
This is separate from the older remembered fixture's two different priors.

Generic filtering, actual finite chronological correspondence, observation-
admissible attainment, and the original monitor adapter are audited below
with their actual finite-space, finite-horizon and legal-menu hypotheses.
No infinite-horizon or arbitrary measurable-state sufficiency is claimed.
No independent certification acceptance decision is changed.
-/

open MeasureTheory
open scoped Classical

namespace PermanssonResearch.ReverseSolver.D06ScopeReceiptAddendum

open PermanssonResearch.ReverseSolver.Belief
open PermanssonResearch.ReverseSolver.BeliefTests

noncomputable section

/-- Exact named receipt for the original anonymous readout equality. -/
theorem original_remembered_same_physical_observation :
    remembered.observation 0 true () = remembered.observation 0 false () := rfl

/-- The older two-prior fixture is retained explicitly as its own statement. -/
theorem original_remembered_completion_values :
    remembered.value flagReward 0 0 (Distribution.pure true) = 1 ∧
    remembered.value flagReward 0 0 (Distribution.pure false) = 0 := by
  simp [Model.value, Distribution.dot, Distribution.pure, flagReward,
    Fintype.sum_bool]

/-- Every real behavioral observation tree in the original one-step guessing
fixture remains below its observation-admissible value. -/
theorem original_observation_policy_dominated (π : Behavioral Bool Bool 1) :
    (∫ q, reward (Model.terminal 1 q.1 q.2)
      ∂(guessing.chronologicalLaw 1 0 prior π).pmf.toMeasure) ≤ 1/2 := by
  have h := guessing.behavioralChronological_dominated reward 1 0 prior π
  simpa only [observation_optimum] using h

theorem original_observation_tree_attained :
    (∫ q, reward (Model.terminal 1 q.1 q.2)
      ∂(guessing.chronologicalLaw 1 0 prior
        ((guessing.optimalTree reward 1 0 prior).behavioral 1)).pmf.toMeasure) =
      1/2 := by
  simpa only [observation_optimum] using guessing.observationTree_attains reward 1 0 prior

/-- The hidden-state peek computes a different information-class value. -/
theorem original_illegal_hidden_peek_gap :
    (∑ z, prior.weight z * reward (z.1,z.1)) = 1 ∧ (1/2 : ℝ) < 1 := by
  constructor
  · norm_num [prior, reward, Fintype.sum_prod_type, Fintype.sum_bool]
  · norm_num

theorem original_zero_likelihood_default :
    guessing.posterior 0 prior false true = guessing.default :=
  guessing.posterior_zero 0 prior false true impossible_observation

theorem original_zero_branch_contribution :
    guessing.branchMass 0 prior false true *
      (guessing.posterior 0 prior false true).dot reward = 0 := by
  rw [impossible_observation, zero_mul]

/-- The observation reads the new hidden state after the transition. -/
theorem original_successor_readout_order :
    successorReadout.branchMass 0 (Distribution.pure false) true true = 1 ∧
    successorReadout.branchMass 0 (Distribution.pure false) true false = 0 := by
  norm_num [Model.branchMass, Model.numerator, successorReadout,
    Distribution.pure, Fintype.sum_bool]

/-- Immediate terminal-completion value after the actual observed one-step
history, using the original model and its single fixed initial law. -/
def reachableCompletionValue (a : Bool) : ℝ :=
  ReachableCompletionBelief.model.value flagReward 0 1
    (ReachableCompletionBelief.model.filter 0 ReachableCompletionBelief.initial [(a, ())])

theorem one_prior_reachable_completion_values :
    reachableCompletionValue false = 0 ∧ reachableCompletionValue true = 1 := by
  constructor
  · simpa [reachableCompletionValue, Model.value, Distribution.dot,
      flagReward, Fintype.sum_bool] using
        ReachableCompletionBelief.reachable_posteriors_disagree.1
  · simpa [reachableCompletionValue, Model.value, Distribution.dot,
      flagReward, Fintype.sum_bool] using
        ReachableCompletionBelief.reachable_posteriors_disagree.2

/-- The identical current physical readout cannot encode both distinct
reachable values. The histories include the controller's own chosen actions. -/
theorem no_readout_only_reachable_completion_value :
    ¬ ∃ v : Unit → ℝ, ∀ a : Bool, v () = reachableCompletionValue a := by
  rintro ⟨v, hv⟩
  have hfalse := hv false
  have htrue := hv true
  rw [one_prior_reachable_completion_values.1] at hfalse
  rw [one_prior_reachable_completion_values.2] at htrue
  linarith

end
end PermanssonResearch.ReverseSolver.D06ScopeReceiptAddendum

-- new_original_fixture_and_reachable_value_facts
#check PermanssonResearch.ReverseSolver.D06ScopeReceiptAddendum.original_remembered_same_physical_observation
#print axioms PermanssonResearch.ReverseSolver.D06ScopeReceiptAddendum.original_remembered_same_physical_observation
#check PermanssonResearch.ReverseSolver.D06ScopeReceiptAddendum.original_remembered_completion_values
#print axioms PermanssonResearch.ReverseSolver.D06ScopeReceiptAddendum.original_remembered_completion_values
#check PermanssonResearch.ReverseSolver.D06ScopeReceiptAddendum.original_observation_policy_dominated
#print axioms PermanssonResearch.ReverseSolver.D06ScopeReceiptAddendum.original_observation_policy_dominated
#check PermanssonResearch.ReverseSolver.D06ScopeReceiptAddendum.original_observation_tree_attained
#print axioms PermanssonResearch.ReverseSolver.D06ScopeReceiptAddendum.original_observation_tree_attained
#check PermanssonResearch.ReverseSolver.D06ScopeReceiptAddendum.original_illegal_hidden_peek_gap
#print axioms PermanssonResearch.ReverseSolver.D06ScopeReceiptAddendum.original_illegal_hidden_peek_gap
#check PermanssonResearch.ReverseSolver.D06ScopeReceiptAddendum.original_zero_likelihood_default
#print axioms PermanssonResearch.ReverseSolver.D06ScopeReceiptAddendum.original_zero_likelihood_default
#check PermanssonResearch.ReverseSolver.D06ScopeReceiptAddendum.original_zero_branch_contribution
#print axioms PermanssonResearch.ReverseSolver.D06ScopeReceiptAddendum.original_zero_branch_contribution
#check PermanssonResearch.ReverseSolver.D06ScopeReceiptAddendum.original_successor_readout_order
#print axioms PermanssonResearch.ReverseSolver.D06ScopeReceiptAddendum.original_successor_readout_order
#check PermanssonResearch.ReverseSolver.D06ScopeReceiptAddendum.one_prior_reachable_completion_values
#print axioms PermanssonResearch.ReverseSolver.D06ScopeReceiptAddendum.one_prior_reachable_completion_values
#check PermanssonResearch.ReverseSolver.D06ScopeReceiptAddendum.no_readout_only_reachable_completion_value
#print axioms PermanssonResearch.ReverseSolver.D06ScopeReceiptAddendum.no_readout_only_reachable_completion_value

-- bayes_and_actual_observable_history
#check PermanssonResearch.ReverseSolver.Belief.Model.posterior_formula
#print axioms PermanssonResearch.ReverseSolver.Belief.Model.posterior_formula
#check PermanssonResearch.ReverseSolver.Belief.Model.posterior_zero
#print axioms PermanssonResearch.ReverseSolver.Belief.Model.posterior_zero
#check PermanssonResearch.ReverseSolver.Belief.Model.posterior_cancel
#print axioms PermanssonResearch.ReverseSolver.Belief.Model.posterior_cancel
#check PermanssonResearch.ReverseSolver.Belief.Model.filtered_conditional
#print axioms PermanssonResearch.ReverseSolver.Belief.Model.filtered_conditional
#check PermanssonResearch.ReverseSolver.Belief.Model.observed_filter_law
#print axioms PermanssonResearch.ReverseSolver.Belief.Model.observed_filter_law
#check PermanssonResearch.ReverseSolver.Belief.Model.chronological_filtered_endpoint
#print axioms PermanssonResearch.ReverseSolver.Belief.Model.chronological_filtered_endpoint
#check PermanssonResearch.ReverseSolver.Belief.Model.chronological_word_integral
#print axioms PermanssonResearch.ReverseSolver.Belief.Model.chronological_word_integral
#check PermanssonResearch.ReverseSolver.Belief.Model.actual_history_conditional
#print axioms PermanssonResearch.ReverseSolver.Belief.Model.actual_history_conditional

-- finite_observation_policy_sufficiency
#check PermanssonResearch.ReverseSolver.Belief.Model.alpha_envelope
#print axioms PermanssonResearch.ReverseSolver.Belief.Model.alpha_envelope
#check PermanssonResearch.ReverseSolver.Belief.Model.expected_le_value
#print axioms PermanssonResearch.ReverseSolver.Belief.Model.expected_le_value
#check PermanssonResearch.ReverseSolver.Belief.Model.chronologicalIntegral_eq_expected
#print axioms PermanssonResearch.ReverseSolver.Belief.Model.chronologicalIntegral_eq_expected
#check PermanssonResearch.ReverseSolver.Belief.Model.behavioralChronological_dominated
#print axioms PermanssonResearch.ReverseSolver.Belief.Model.behavioralChronological_dominated
#check PermanssonResearch.ReverseSolver.Belief.Model.observationTree_attains
#print axioms PermanssonResearch.ReverseSolver.Belief.Model.observationTree_attains

-- actual_monitored_original_control_adapter
#check PermanssonResearch.ReverseSolver.Belief.monitored_physical_atom
#print axioms PermanssonResearch.ReverseSolver.Belief.monitored_physical_atom
#check PermanssonResearch.ReverseSolver.Belief.monitored_control_permitted
#print axioms PermanssonResearch.ReverseSolver.Belief.monitored_control_permitted
#check PermanssonResearch.ReverseSolver.Belief.monitored_control_world_fixed
#print axioms PermanssonResearch.ReverseSolver.Belief.monitored_control_world_fixed
#check PermanssonResearch.ReverseSolver.Belief.monitored_control_update_fixed
#print axioms PermanssonResearch.ReverseSolver.Belief.monitored_control_update_fixed
#check PermanssonResearch.ReverseSolver.Belief.monitoredInitial_support
#print axioms PermanssonResearch.ReverseSolver.Belief.monitoredInitial_support
#check PermanssonResearch.ReverseSolver.Belief.monitor_run_on_support
#print axioms PermanssonResearch.ReverseSolver.Belief.monitor_run_on_support
#check PermanssonResearch.ReverseSolver.Belief.monitored_initial_integral_eq_history
#print axioms PermanssonResearch.ReverseSolver.Belief.monitored_initial_integral_eq_history
#check PermanssonResearch.ReverseSolver.Belief.monitored_history_dominated
#print axioms PermanssonResearch.ReverseSolver.Belief.monitored_history_dominated
#check PermanssonResearch.ReverseSolver.Belief.monitored_history_attained
#print axioms PermanssonResearch.ReverseSolver.Belief.monitored_history_attained

-- one_prior_positive_history_fixture
#check PermanssonResearch.ReverseSolver.ReachableCompletionBelief.both_observable_words_positive
#print axioms PermanssonResearch.ReverseSolver.ReachableCompletionBelief.both_observable_words_positive
#check PermanssonResearch.ReverseSolver.ReachableCompletionBelief.both_histories_reachable_in_one_law
#print axioms PermanssonResearch.ReverseSolver.ReachableCompletionBelief.both_histories_reachable_in_one_law
#check PermanssonResearch.ReverseSolver.ReachableCompletionBelief.reachable_posteriors_disagree
#print axioms PermanssonResearch.ReverseSolver.ReachableCompletionBelief.reachable_posteriors_disagree
#check PermanssonResearch.ReverseSolver.ReachableCompletionBelief.readout_cannot_reveal_completion
#print axioms PermanssonResearch.ReverseSolver.ReachableCompletionBelief.readout_cannot_reveal_completion

-- original_observation_information_gap_fixture
#check PermanssonResearch.ReverseSolver.BeliefTests.action_value
#print axioms PermanssonResearch.ReverseSolver.BeliefTests.action_value
#check PermanssonResearch.ReverseSolver.BeliefTests.observation_optimum
#print axioms PermanssonResearch.ReverseSolver.BeliefTests.observation_optimum
#check PermanssonResearch.ReverseSolver.BeliefTests.impossible_observation
#print axioms PermanssonResearch.ReverseSolver.BeliefTests.impossible_observation
