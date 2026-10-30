import PermanssonResearch.ApplicationBridge.ExitReceipt
import Mathlib.Tactic

/-!
# ApplicationBridge — exact strongly lumpable typed quotients

A quotient receipt maps fine joint states to coarse joint states (`proj`),
reports a coarse matrix `Q` for the baseline and for every declared
intervention, a region that is a union of fibers, and finite-horizon
survival (or exit) values on comparison states for both levels.

`Lumpable K Q proj` is complete strong lumpability: every fine state sends
exactly `Q (proj x) c` mass into fiber `c`. Under it, the rational hitting
recursion for leaving the lifted region coincides with the coarse one at
every horizon (`lumped_exit_value`), so the actual fine and coarse
region-survival probabilities agree (`quotient_survival_actual`). This is an
exact finite-horizon transport of the induced Markov law; it does not infer a
coarse α/P/U decomposition, approximate bisimulation, GR/PR status or a
causal identification.
-/

open MeasureTheory

namespace PermanssonResearch.ApplicationBridge.QuotientReceipt

open PermanssonLean
open PermanssonResearch.ReverseSolver
open PermanssonResearch.ReverseSolver.FiniteStrategicRealization
open PermanssonResearch.ApplicationBridge.MenuReceipt
open PermanssonResearch.ApplicationBridge.ExitReceipt

set_option autoImplicit false

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

variable {n m : ℕ}

/-- The fine region of all states whose coarse image lies in `R`. -/
def liftRegion (proj : Fin n → Fin m) (R : Finset (Fin m)) : Finset (Fin n) :=
  Finset.univ.filter (fun x => proj x ∈ R)

/-- Complete strong lumpability of `K` onto `Q` along `proj`. -/
def Lumpable (K : RationalMarkovMatrix n) (Q : RationalMarkovMatrix m)
    (proj : Fin n → Fin m) : Prop :=
  ∀ x : Fin n, ∀ c : Fin m,
    (∑ z ∈ Finset.univ.filter (fun z => proj z = c), K.entry x z) = Q.entry (proj x) c

instance (K : RationalMarkovMatrix n) (Q : RationalMarkovMatrix m) (proj : Fin n → Fin m) :
    Decidable (Lumpable K Q proj) := by
  unfold Lumpable
  infer_instance

/-- Leaving the lifted region is the same rational recursion as leaving `R`. -/
theorem lumped_exit_value (K : RationalMarkovMatrix n) (Q : RationalMarkovMatrix m)
    (proj : Fin n → Fin m) (hl : Lumpable K Q proj) (R : Finset (Fin m)) :
    ∀ t x, rationalHittingValue K (exitTarget (liftRegion proj R)) t x =
      rationalHittingValue Q (exitTarget R) t (proj x) := by
  intro t
  induction t with
  | zero => intro x; simp [exitTarget, liftRegion]
  | succ t ih =>
    intro x
    rw [rationalHittingValue_succ, rationalHittingValue_succ]
    by_cases hx : proj x ∈ R
    · have h1 : x ∉ (exitTarget (liftRegion proj R)).goal := by simp [exitTarget, liftRegion, hx]
      have h2 : proj x ∉ (exitTarget R).goal := by simp [exitTarget, hx]
      have h3 : x ∉ (exitTarget (liftRegion proj R)).forbidden := by simp [exitTarget]
      have h4 : proj x ∉ (exitTarget R).forbidden := by simp [exitTarget]
      simp only [h1, h2, h3, h4, ite_false]
      simp_rw [ih]
      rw [← Finset.sum_fiberwise Finset.univ proj]
      apply Finset.sum_congr rfl
      intro c _
      rw [← hl x c, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z hz
      rw [(Finset.mem_filter.mp hz).2]
    · have h1 : x ∈ (exitTarget (liftRegion proj R)).goal := by simp [exitTarget, liftRegion, hx]
      have h2 : proj x ∈ (exitTarget R).goal := by simp [exitTarget, hx]
      simp [h1, h2]

/-- Fine and coarse actual region-survival probabilities agree. -/
theorem quotient_survival_actual (K : RationalMarkovMatrix n) (Q : RationalMarkovMatrix m)
    (proj : Fin n → Fin m) (hl : Lumpable K Q proj) (R : Finset (Fin m)) (x : Fin n) (T : ℕ) :
    ((realizedModel K).pathLaw (Measure.dirac (decode x))).real
        (staysThrough (liftRegion proj R) T) =
      ((realizedModel Q).pathLaw (Measure.dirac (decode (proj x)))).real (staysThrough R T) := by
  rw [survival_actual, survival_actual, lumped_exit_value K Q proj hl R T x]

/-! ## Receipt checks -/

/-- Strong lumpability, the region as a union of fibers, and the exact fine
    and coarse objective values on the comparison states. -/
def QuotientChecks (K : RationalMarkovMatrix n) (Q : RationalMarkovMatrix m)
    (proj : Fin n → Fin m) (region : Finset (Fin n)) (R : Finset (Fin m)) (horizon : ℕ)
    (survival : Bool) (comparison : Finset (Fin n)) (fine : Fin n → ℚ) (coarse : Fin m → ℚ) :
    Prop :=
  Lumpable K Q proj ∧ region = liftRegion proj R ∧
  (∀ x ∈ comparison, fine x = menuObjective survival K region horizon x) ∧
  (∀ x ∈ comparison, coarse (proj x) = menuObjective survival Q R horizon (proj x))

instance (K : RationalMarkovMatrix n) (Q : RationalMarkovMatrix m)
    (proj : Fin n → Fin m) (region : Finset (Fin n)) (R : Finset (Fin m)) (horizon : ℕ)
    (survival : Bool) (comparison : Finset (Fin n)) (fine : Fin n → ℚ) (coarse : Fin m → ℚ) :
    Decidable (QuotientChecks K Q proj region R horizon survival comparison fine coarse) := by
  unfold QuotientChecks
  infer_instance

def checkQuotientProfile (K : RationalMarkovMatrix n) (Q : RationalMarkovMatrix m)
    (proj : Fin n → Fin m) (region : Finset (Fin n)) (R : Finset (Fin m)) (horizon : ℕ)
    (survival : Bool) (comparison : Finset (Fin n)) (fine : Fin n → ℚ) (coarse : Fin m → ℚ) :
    Bool :=
  decide (QuotientChecks K Q proj region R horizon survival comparison fine coarse)

theorem checkQuotientProfile_sound (K : RationalMarkovMatrix n) (Q : RationalMarkovMatrix m)
    (proj : Fin n → Fin m) (region : Finset (Fin n)) (R : Finset (Fin m)) (horizon : ℕ)
    (survival : Bool) (comparison : Finset (Fin n)) (fine : Fin n → ℚ) (coarse : Fin m → ℚ)
    (h : checkQuotientProfile K Q proj region R horizon survival comparison fine coarse = true) :
    QuotientChecks K Q proj region R horizon survival comparison fine coarse := by
  unfold checkQuotientProfile at h
  exact of_decide_eq_true h

/-- The survival (or exit) objective as an actual path-law probability. -/
theorem menuObjective_actual (K : RationalMarkovMatrix n) (B : Finset (Fin n)) (survival : Bool)
    (horizon : ℕ) (x : Fin n) :
    (menuObjective survival K B horizon x : ℝ) =
      if survival then
        ((realizedModel K).pathLaw (Measure.dirac (decode x))).real (staysThrough B horizon)
      else
        1 - ((realizedModel K).pathLaw (Measure.dirac (decode x))).real (staysThrough B horizon) := by
  rw [survival_actual]
  unfold menuObjective
  cases survival <;> simp

section Receipt

variable (K : RationalMarkovMatrix n) (Q : RationalMarkovMatrix m)
  (proj : Fin n → Fin m) (region : Finset (Fin n)) (R : Finset (Fin m)) (horizon : ℕ)
  (survival : Bool) (comparison : Finset (Fin n)) (fine : Fin n → ℚ) (coarse : Fin m → ℚ)
  (h : checkQuotientProfile K Q proj region R horizon survival comparison fine coarse = true)
include h

/-- Every checked fine value is the actual fine-chain objective. -/
theorem checked_fine_value_actual (x : Fin n) (hx : x ∈ comparison) :
    (fine x : ℝ) =
      if survival then
        ((realizedModel K).pathLaw (Measure.dirac (decode x))).real (staysThrough region horizon)
      else
        1 - ((realizedModel K).pathLaw (Measure.dirac (decode x))).real
          (staysThrough region horizon) := by
  rw [(checkQuotientProfile_sound K Q proj region R horizon survival comparison fine coarse h).2.2.1
    x hx, menuObjective_actual]

/-- Every checked coarse value is the actual coarse-chain objective. -/
theorem checked_coarse_value_actual (x : Fin n) (hx : x ∈ comparison) :
    (coarse (proj x) : ℝ) =
      if survival then
        ((realizedModel Q).pathLaw (Measure.dirac (decode (proj x)))).real (staysThrough R horizon)
      else
        1 - ((realizedModel Q).pathLaw (Measure.dirac (decode (proj x)))).real
          (staysThrough R horizon) := by
  rw [(checkQuotientProfile_sound K Q proj region R horizon survival comparison fine coarse h).2.2.2
    x hx, menuObjective_actual]

/-- Exact finite-event intertwining: the fine value at `x` equals the coarse
    value at `proj x`, and the two actual path-law probabilities agree. -/
theorem checked_quotient_transport (x : Fin n) :
    ((realizedModel K).pathLaw (Measure.dirac (decode x))).real (staysThrough region horizon) =
      ((realizedModel Q).pathLaw (Measure.dirac (decode (proj x)))).real
        (staysThrough R horizon) := by
  obtain ⟨hl, hreg, -, -⟩ :=
    checkQuotientProfile_sound K Q proj region R horizon survival comparison fine coarse h
  rw [hreg]
  exact quotient_survival_actual K Q proj hl R x horizon

theorem checked_fine_eq_coarse (x : Fin n) (hx : x ∈ comparison) :
    fine x = coarse (proj x) := by
  have hf := checked_fine_value_actual K Q proj region R horizon survival comparison fine coarse h x hx
  have hc := checked_coarse_value_actual K Q proj region R horizon survival comparison fine coarse h x hx
  have ht := checked_quotient_transport K Q proj region R horizon survival comparison fine coarse h x
  rw [ht] at hf
  exact_mod_cast hf.trans hc.symm

end Receipt

end PermanssonResearch.ApplicationBridge.QuotientReceipt
