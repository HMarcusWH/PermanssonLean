import PermanssonResearch.MultiAgent.FiniteMediation
import Mathlib.Tactic

/-!
NEXT-03/F-05: a finite structural causal model with strictly positive
observed treatment/mediator cells. This is a *constructed* mathematical
example, not identification of an actual-world causal process.
The intervened potential outcomes use the same explicit structural noises.
-/

namespace PermanssonResearch.MultiAgent.PositiveMediationWitness

open PermanssonResearch.MultiAgent.FiniteMediation
open FiniteMediation

noncomputable def exampleSCM : SCM Unit Bool Bool Bool Unit where
  covariate _ := 1
  covariate_nonneg _ := by norm_num
  covariate_sum := by simp
  assignment _ _ := 1 / 2
  assignment_nonneg _ _ := by norm_num
  assignment_sum _ := by norm_num [Fintype.sum_bool]
  mediatorNoise _ u := if u then 2 / 3 else 1 / 3
  mediatorNoise_nonneg _ u := by cases u <;> norm_num
  mediatorNoise_sum _ := by norm_num [Fintype.sum_bool]
  outcomeNoise _ _ := 1
  outcomeNoise_nonneg _ _ := by norm_num
  outcomeNoise_sum _ := by simp
  mediator t _ u := if t then !u else u
  outcome t m _ _ := if t then (if m then 4 else 2) else (if m then 3 else 1)

/-- Actual observed cells are strictly supported. No zero divisor is hidden
in either observational conditional used by the generic identification theorem. -/
theorem observationalMass_pos (t m : Bool) :
    0 < exampleSCM.observationalMass () t m := by
  cases t <;> cases m <;>
    norm_num [SCM.observationalMass, SCM.observationalAtom,
      exampleSCM, Fintype.sum_bool]

theorem treatment_support (t : Bool) :
    exampleSCM.covariate () * exampleSCM.assignment () t = 1 / 2 := by
  norm_num [exampleSCM]

/-- This instance invokes the original SCM positivity-dependent
identification theorem instead of postulating the observational formula. -/
theorem identified_for_every_treatment (t t' : Bool) :
    exampleSCM.nestedExpectation t t' =
      ∑ c, exampleSCM.covariate c *
        ∑ m, exampleSCM.conditionalOutcome c t m *
          exampleSCM.conditionalMediator c t' m := by
  apply SCM.mediation_identification exampleSCM t t'
  · intro c m
    cases c
    exact ne_of_gt (observationalMass_pos t m)
  · intro c
    cases c
    rw [treatment_support]
    norm_num

/-- Four nonidentical joint intervention expectations, evaluated with exact
rational coefficients represented in the real-number SCM. -/
theorem four_intervention_values :
    exampleSCM.nestedExpectation false false = 7 / 3 ∧
    exampleSCM.nestedExpectation false true = 5 / 3 ∧
    exampleSCM.nestedExpectation true false = 10 / 3 ∧
    exampleSCM.nestedExpectation true true = 8 / 3 := by
  norm_num [SCM.nestedExpectation, exampleSCM, Fintype.sum_bool]

/-- The mediator is treatment-dependent. Ignoring the treatment-specific
mediator law would change the nested result in this positive-support SCM. -/
theorem mediator_shift_nonzero :
    exampleSCM.nestedExpectation true false ≠
      exampleSCM.nestedExpectation true true := by
  obtain ⟨_, _, h₁, h₂⟩ := four_intervention_values
  rw [h₁, h₂]
  norm_num

end PermanssonResearch.MultiAgent.PositiveMediationWitness
