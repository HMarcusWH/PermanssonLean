import Mathlib.Tactic

/-! Finite one-mediator identification in an explicit structural causal model.
Conditional on the pretreatment covariate, assignment and the two noises have
the declared product law. The same structural maps and noises define all
potentials. Positivity is required at every observational conditional used.
No causal interpretation of a protocol-distance inequality is assumed. -/

namespace PermanssonResearch.MultiAgent.FiniteMediation

noncomputable section

variable {C T M U V : Type*} [Fintype C] [Fintype T] [Fintype M] [Fintype U] [Fintype V]
  [DecidableEq M]

structure SCM (C T M U V : Type*) [Fintype C] [Fintype T] [Fintype M] [Fintype U] [Fintype V] where
  covariate : C → ℝ
  covariate_nonneg : ∀ c, 0 ≤ covariate c
  covariate_sum : ∑ c, covariate c = 1
  assignment : C → T → ℝ
  assignment_nonneg : ∀ c t, 0 ≤ assignment c t
  assignment_sum : ∀ c, ∑ t, assignment c t = 1
  mediatorNoise : C → U → ℝ
  mediatorNoise_nonneg : ∀ c u, 0 ≤ mediatorNoise c u
  mediatorNoise_sum : ∀ c, ∑ u, mediatorNoise c u = 1
  outcomeNoise : C → V → ℝ
  outcomeNoise_nonneg : ∀ c v, 0 ≤ outcomeNoise c v
  outcomeNoise_sum : ∀ c, ∑ v, outcomeNoise c v = 1
  mediator : T → C → U → M
  outcome : T → M → C → V → ℝ

namespace SCM

variable (S : SCM C T M U V)

/-- Conditional product noise/assignment atom. -/
def observationalAtom (c : C) (t : T) (u : U) (v : V) : ℝ :=
  S.covariate c * S.assignment c t * S.mediatorNoise c u * S.outcomeNoise c v

def mediatorMass (c : C) (t : T) (m : M) : ℝ :=
  ∑ u, if S.mediator t c u = m then S.mediatorNoise c u else 0

def response (c : C) (t : T) (m : M) : ℝ :=
  ∑ v, S.outcomeNoise c v * S.outcome t m c v

def observationalMass (c : C) (t : T) (m : M) : ℝ :=
  ∑ u, ∑ v, if S.mediator t c u = m then S.observationalAtom c t u v else 0

def observationalNumerator (c : C) (t : T) (m : M) : ℝ :=
  ∑ u, ∑ v, if S.mediator t c u = m then
    S.observationalAtom c t u v * S.outcome t m c v else 0

def observationalOutcomeMass (c : C) (t : T) (m : M) (y : ℝ) : ℝ :=
  ∑ u, ∑ v, if S.mediator t c u = m ∧ S.outcome t m c v = y then
    S.observationalAtom c t u v else 0

def conditionalOutcome (c : C) (t : T) (m : M) : ℝ :=
  S.observationalNumerator c t m / S.observationalMass c t m

def conditionalMediator (c : C) (t : T) (m : M) : ℝ :=
  S.observationalMass c t m / (S.covariate c * S.assignment c t)

theorem observationalMass_factor (c : C) (t : T) (m : M) :
    S.observationalMass c t m =
      S.covariate c * S.assignment c t * S.mediatorMass c t m := by
  simp only [observationalMass, observationalAtom]
  calc
    _ = ∑ u, if S.mediator t c u = m then
        S.covariate c * S.assignment c t * S.mediatorNoise c u else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases h : S.mediator t c u = m
      · simp only [if_pos h]
        rw [← Finset.mul_sum, S.outcomeNoise_sum, mul_one]
      · simp [h]
    _ = _ := by simp [mediatorMass, Finset.mul_sum, mul_ite]

theorem observationalNumerator_factor (c : C) (t : T) (m : M) :
    S.observationalNumerator c t m =
      S.observationalMass c t m * S.response c t m := by
  rw [S.observationalMass_factor]
  have hinner (u : U) :
      (∑ v, if S.mediator t c u = m then
        S.observationalAtom c t u v * S.outcome t m c v else 0) =
      (if S.mediator t c u = m then S.mediatorNoise c u else 0) *
        (S.covariate c * S.assignment c t * S.response c t m) := by
    by_cases h : S.mediator t c u = m
    · simp only [if_pos h, observationalAtom, response, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    · simp [h]
  unfold observationalNumerator
  simp_rw [hinner]
  rw [← Finset.sum_mul]
  unfold mediatorMass
  ring

theorem conditionalOutcome_eq_response (c : C) (t : T) (m : M)
    (hpositive : S.observationalMass c t m ≠ 0) :
    S.conditionalOutcome c t m = S.response c t m := by
  rw [conditionalOutcome, S.observationalNumerator_factor]
  exact mul_div_cancel_left₀ _ hpositive

theorem conditionalMediator_eq_mass (c : C) (t : T) (m : M)
    (hpositive : S.covariate c * S.assignment c t ≠ 0) :
    S.conditionalMediator c t m = S.mediatorMass c t m := by
  rw [conditionalMediator, S.observationalMass_factor]
  exact mul_div_cancel_left₀ _ hpositive

/-- Potential outcome expectation on the same declared pair of noises. -/
def nestedExpectation (t t' : T) : ℝ :=
  ∑ c, S.covariate c * ∑ u, S.mediatorNoise c u *
    ∑ v, S.outcomeNoise c v * S.outcome t (S.mediator t' c u) c v

theorem nestedExpectation_grouped (t t' : T) :
    S.nestedExpectation t t' =
      ∑ c, S.covariate c * ∑ m, S.mediatorMass c t' m * S.response c t m := by
  simp only [nestedExpectation]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  simp only [mediatorMass, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [response, ite_mul]

/-- Observational mediation formula. All treatment and mediator cells used by
the formula have positive mass; no division at an unsupported cell is hidden. -/
theorem mediation_identification (t t' : T)
    (houtcome : ∀ c m, S.observationalMass c t m ≠ 0)
    (hassignment : ∀ c, S.covariate c * S.assignment c t' ≠ 0) :
    S.nestedExpectation t t' =
      ∑ c, S.covariate c * ∑ m,
        S.conditionalOutcome c t m * S.conditionalMediator c t' m := by
  rw [S.nestedExpectation_grouped]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  rw [S.conditionalOutcome_eq_response c t m (houtcome c m),
    S.conditionalMediator_eq_mass c t' m (hassignment c)]
  exact mul_comm _ _

theorem signed_effect_decomposition (t₁ t₀ : T) :
    S.nestedExpectation t₁ t₁ - S.nestedExpectation t₀ t₀ =
      (S.nestedExpectation t₁ t₀ - S.nestedExpectation t₀ t₀) +
      (S.nestedExpectation t₁ t₁ - S.nestedExpectation t₁ t₀) := by ring

/-- Zero-weight covariates and unused mediator cells need no positivity. -/
theorem mediation_identification_on_support (t t' : T)
    (houtcome : ∀ c, S.covariate c ≠ 0 → ∀ m,
      S.mediatorMass c t' m ≠ 0 → S.observationalMass c t m ≠ 0)
    (hassignment : ∀ c, S.covariate c ≠ 0 → S.assignment c t' ≠ 0) :
    S.nestedExpectation t t' =
      ∑ c, S.covariate c * ∑ m,
        S.conditionalOutcome c t m * S.conditionalMediator c t' m := by
  rw [S.nestedExpectation_grouped]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : S.covariate c = 0
  · simp [hc]
  · congr 1
    apply Finset.sum_congr rfl
    intro m _
    rw [S.conditionalMediator_eq_mass c t' m (mul_ne_zero hc (hassignment c hc))]
    by_cases hm : S.mediatorMass c t' m = 0
    · simp [hm]
    · rw [S.conditionalOutcome_eq_response c t m (houtcome c hc m hm)]
      exact mul_comm _ _

theorem observationalAtom_sum :
    (∑ c, ∑ t, ∑ u, ∑ v, S.observationalAtom c t u v) = 1 := by
  simp [observationalAtom, ← Finset.mul_sum, S.outcomeNoise_sum,
    S.mediatorNoise_sum, S.assignment_sum, S.covariate_sum]

end SCM

/-- Two modular structural outcome maps agree at every observed (T,M=T)
atom, yet disagree under the joint intervention do(T=true,M=false). -/
def mediatedOutcome (_t m : Bool) : ℝ := if m then 1 else 0
def directOutcome (t _m : Bool) : ℝ := if t then 1 else 0

theorem same_observed_structural_outcome (t : Bool) :
    mediatedOutcome t t = directOutcome t t := rfl

theorem same_fair_observational_law (t m : Bool) (y : ℝ) :
    (if m = t ∧ y = mediatedOutcome t m then (1/2 : ℝ) else 0) =
    (if m = t ∧ y = directOutcome t m then (1/2 : ℝ) else 0) := by
  by_cases h : m = t
  · subst m; rfl
  · simp [h]

theorem different_joint_intervention :
    mediatedOutcome true false = 0 ∧ directOutcome true false = 1 := by
  norm_num [mediatedOutcome, directOutcome]

theorem counterexample_missing_positivity :
    (if (false : Bool) = true then (1/2 : ℝ) else 0) = 0 := by simp

/-- Two complete finite SCM records; treatment is fair and M=T. Their
observational equality persists despite a different modular outcome map. -/
def nonidentificationSCM (useDirect : Bool) : SCM Unit Bool Bool Unit Unit where
  covariate _ := 1
  covariate_nonneg _ := by norm_num
  covariate_sum := by simp
  assignment _ _ := 1/2
  assignment_nonneg _ _ := by norm_num
  assignment_sum _ := by norm_num [Fintype.sum_bool]
  mediatorNoise _ _ := 1
  mediatorNoise_nonneg _ _ := by norm_num
  mediatorNoise_sum _ := by simp
  outcomeNoise _ _ := 1
  outcomeNoise_nonneg _ _ := by norm_num
  outcomeNoise_sum _ := by simp
  mediator t _ _ := t
  outcome t m _ _ := if useDirect then directOutcome t m else mediatedOutcome t m

theorem two_SCMs_same_observational_law (c : Unit) (t m : Bool) (y : ℝ) :
    (nonidentificationSCM false).observationalOutcomeMass c t m y =
      (nonidentificationSCM true).observationalOutcomeMass c t m y := by
  by_cases h : t = m
  · subst m
    simp [SCM.observationalOutcomeMass, SCM.observationalAtom, nonidentificationSCM,
      mediatedOutcome, directOutcome]
  · simp [SCM.observationalOutcomeMass, nonidentificationSCM, h]

theorem two_SCMs_different_joint_do :
    (nonidentificationSCM false).response () true false = 0 ∧
      (nonidentificationSCM true).response () true false = 1 := by
  norm_num [SCM.response, nonidentificationSCM, mediatedOutcome, directOutcome]

theorem two_SCMs_positivity_failure :
    (nonidentificationSCM false).observationalMass () true false = 0 := by
  simp [SCM.observationalMass, nonidentificationSCM]

end

end PermanssonResearch.MultiAgent.FiniteMediation
