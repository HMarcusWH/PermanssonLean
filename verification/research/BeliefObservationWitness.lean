import PermanssonResearch.ReverseSolver.BeliefMonitor

open MeasureTheory
open PermanssonResearch.ReverseSolver.Belief

namespace PermanssonResearch.ReverseSolver.BeliefTests

noncomputable section

/-- Hidden bit and the most recent guess. The observation is always false,
so the controller cannot read the bit. -/
def guessing : Model (Bool × Bool) Bool Bool where
  transition _ z c := Distribution.pure (z.1,c)
  observation _ _ _ := Distribution.pure false
  default := Distribution.pure (false,false)

def prior : Distribution (Bool × Bool) where
  weight z := if z.2 = false then 1/2 else 0
  nonneg z := by split_ifs <;> norm_num
  sum_one := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

def reward (z : Bool × Bool) : ℝ := if z.1 = z.2 then 1 else 0

theorem action_value (c : Bool) :
    guessing.score 0 (guessing.value reward 0 1) prior c = 1/2 := by
  change (∑ o, guessing.branchMass 0 prior c o * (guessing.posterior 0 prior c o).dot reward) = _
  rw [← guessing.dot_step 0 prior c (fun _ => reward)]
  cases c <;> norm_num [Distribution.dot, Model.step, guessing, Distribution.pure,
    prior, reward, Fintype.sum_prod_type, Fintype.sum_bool] <;> decide

theorem observation_optimum : guessing.value reward 1 0 prior = 1/2 := by
  change finiteMax (fun c : Bool => guessing.score 0 (guessing.value reward 0 1) prior c) = _
  simp_rw [action_value]
  rfl

/-- Every real behavioral observation policy has value at most one half. -/
example (π : Behavioral Bool Bool 1) :
    (∫ q, reward (Model.terminal 1 q.1 q.2)
      ∂(guessing.chronologicalLaw 1 0 prior π).pmf.toMeasure) ≤ 1/2 := by
  have h := guessing.behavioralChronological_dominated reward 1 0 prior π
  simpa only [observation_optimum] using h

/-- A finite observation tree attains that bound under the actual word law. -/
example :
    (∫ q, reward (Model.terminal 1 q.1 q.2)
      ∂(guessing.chronologicalLaw 1 0 prior
        ((guessing.optimalTree reward 1 0 prior).behavioral 1)).pmf.toMeasure) = 1/2 := by
  simpa only [observation_optimum] using guessing.observationTree_attains reward 1 0 prior

/-- Illegally exposing the hidden state would give one: a strict information
gap guards against silently allowing hidden-state controls. -/
example : (∑ z, prior.weight z * reward (z.1,z.1)) = 1 ∧ (1/2 : ℝ) < 1 := by
  constructor
  · norm_num [prior, reward, Fintype.sum_prod_type, Fintype.sum_bool]
  · norm_num

theorem impossible_observation : guessing.branchMass 0 prior false true = 0 := by
  simp [Model.branchMass, Model.numerator, guessing, Distribution.pure]

/-- The declared default is actually selected at a zero-denominator branch. -/
example : guessing.posterior 0 prior false true = guessing.default :=
  guessing.posterior_zero 0 prior false true impossible_observation

example : guessing.branchMass 0 prior false true *
    (guessing.posterior 0 prior false true).dot reward = 0 := by
  rw [impossible_observation, zero_mul]

def fixedFalse : ObservationPolicy Bool Bool := ⟨fun _ _ => Distribution.pure false⟩

open scoped Classical

/-- The impossible observed word has zero probability under the actual
chronological PMF, as well as zero Bayes branch weight. -/
example :
    (∫ q, (if Samples.observable 1 q.2 = [(false,true)] then (1 : ℝ) else 0)
      ∂(guessing.chronologicalLaw 1 0 prior (fixedFalse.unfold 1 0 [])).pmf.toMeasure) = 0 := by
  calc
    _ = Model.actionWeight fixedFalse 0 [] [(false,true)] *
        guessing.likelihood 0 prior [(false,true)] := by
      convert guessing.chronological_word_integral fixedFalse 0 [] prior [(false,true)] using 1
      apply integral_congr_ae
      filter_upwards [] with q
      by_cases hp : Samples.observable 1 q.2 = [(false,true)] <;> simp [hp]
    _ = 0 := by simp [Model.likelihood, Model.actionWeight, impossible_observation]

example :
    (∫ q, (if Samples.observable 1 q.2 = [(false,false)] ∧
        Model.terminal 1 q.1 q.2 = (false,false) then (1 : ℝ) else 0)
      ∂(guessing.chronologicalLaw 1 0 prior (fixedFalse.unfold 1 0 [])).pmf.toMeasure) = 1/2 := by
  calc
    _ = (Model.actionWeight fixedFalse 0 [] [(false,false)] *
        guessing.likelihood 0 prior [(false,false)]) *
        (guessing.filter 0 prior [(false,false)]).weight (false,false) := by
      convert guessing.chronological_filtered_endpoint fixedFalse 0 [] prior [(false,false)] (false,false) using 1
      apply integral_congr_ae
      filter_upwards [] with q
      by_cases hp : Samples.observable 1 q.2 = [(false,false)] ∧
        Model.terminal 1 q.1 q.2 = (false,false) <;> simp [hp]
    _ = 1/2 := by
      norm_num [Model.actionWeight, Model.likelihood, Model.filter, Model.posterior,
        Model.branchMass, Model.numerator, fixedFalse, guessing, Distribution.pure,
        prior, Fintype.sum_prod_type, Fintype.sum_bool]

/-- Readout occurs after the physical transition: a new true state is
observed even though the old state was false. -/
def successorReadout : Model Bool Bool Bool where
  transition _ _ c := Distribution.pure c
  observation _ z _ := Distribution.pure z
  default := Distribution.pure false

example : successorReadout.branchMass 0 (Distribution.pure false) true true = 1 ∧
    successorReadout.branchMass 0 (Distribution.pure false) true false = 0 := by
  norm_num [Model.branchMass, Model.numerator, successorReadout, Distribution.pure,
    Fintype.sum_bool]

/-- A hidden completed-success flag must be part of the belief even though
the physical observation is constant. -/
def remembered : Model Bool Unit Unit where
  transition _ z _ := Distribution.pure z
  observation _ _ _ := Distribution.pure ()
  default := Distribution.pure false

def flagReward (b : Bool) : ℝ := if b then 1 else 0

example : remembered.observation 0 true () = remembered.observation 0 false () := rfl

example : remembered.value flagReward 0 0 (Distribution.pure true) = 1 ∧
    remembered.value flagReward 0 0 (Distribution.pure false) = 0 := by
  simp [Model.value, Distribution.dot, Distribution.pure, flagReward, Fintype.sum_bool]

end
end PermanssonResearch.ReverseSolver.BeliefTests
