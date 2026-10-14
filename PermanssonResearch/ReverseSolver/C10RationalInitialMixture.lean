import PermanssonResearch.ReverseSolver.CheckedRationalEventValue
import PermanssonResearch.MultipleLimit.FiniteCanonicalPath
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# C10 — finite rational initial laws and exact eventual-event mixtures

The original constitutive margin continues to minimize point-start
effects on the complete frozen B₁. A separate initial-law query is a
probability evaluation, NOT a menu optimizer or an automatic PR witness.

The finite probability measure used below is built from the exact
rational initial weights. Its mass and singleton weights are proven,
not asserted by an external JSON status field.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false
open FiniteStrategicRealization
open PermanssonResearch.MultipleLimit.FiniteCanonicalPath
open PermanssonResearch.MultipleLimit.FrozenObservedEvent

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- A checked, nonnegative, exactly normalized rational law on Fin n.
For n=0 there is no such structure, since the sum cannot equal one. -/
structure RationalInitialLaw (n : ℕ) where
  weight : Fin n → ℚ
  nonneg : ∀ x, 0 ≤ weight x
  sum_one : (∑ x : Fin n, weight x) = 1

/-- Accept an untrusted rational weight vector only after exact checks.
This validation reflects *typed rationals*, not external JSON decoding. -/
def validateInitialLaw {n : ℕ} (w : Fin n → ℚ) :
    Option (RationalInitialLaw n) :=
  if hn : ∀ x : Fin n, 0 ≤ w x then
    if hs : (∑ x : Fin n, w x) = 1 then
      some ⟨w, hn, hs⟩
    else none
  else none

/-- Total exact rational initial-mixture event evaluation. -/
def rationalMixedEventValue {n : ℕ}
    (cert : DirichletCertificate n) (h : Fin n → Bool)
    (initial : RationalInitialLaw n) : ℚ :=
  ∑ x : Fin n, initial.weight x * eventValue cert h x

/-- The rational mixing law does NOT replace the frozen original B₁ margin. -/
def rationalMixedDifference {n : ℕ}
    (baseline member : DirichletCertificate n) (h : Fin n → Bool)
    (initial : RationalInitialLaw n) : ℚ :=
  |rationalMixedEventValue baseline h initial -
    rationalMixedEventValue member h initial|

noncomputable section

/-- Genuine finite probability mass function over the D0 physical world.
The exact rational weights are converted to nonnegative real masses. -/
def rationalInitialPMF {n : ℕ} (initial : RationalInitialLaw n) :
    PMF (PermanssonLean.JointState Unit (Fin n)) := by
  classical
  let f : PermanssonLean.JointState Unit (Fin n) → ℝ≥0∞ :=
    fun y => ENNReal.ofReal (initial.weight (encode y) : ℝ)
  have hn (x : Fin n) : (0 : ℝ) ≤ (initial.weight x : ℝ) := by
    exact_mod_cast initial.nonneg x
  have htotal : (∑ x : Fin n, (initial.weight x : ℝ)) = 1 := by
    exact_mod_cast initial.sum_one
  have hs : (∑ x : Fin n,
      ENNReal.ofReal (initial.weight x : ℝ)) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hn x)]
    rw [htotal]
    norm_num
  have hfull :
      (∑ y : PermanssonLean.JointState Unit (Fin n), f y) = 1 := by
    simpa [f, encode, Fintype.sum_prod_type] using hs
  exact PMF.ofFintype f hfull

/-- Construct a real probability measure rather than assuming a serialized
baseline-certification flag or an arbitrary external model adapter. -/
def rationalInitialProbability {n : ℕ}
    (initial : RationalInitialLaw n) :
    ProbabilityMeasure (PermanssonLean.JointState Unit (Fin n)) :=
  ⟨(rationalInitialPMF initial).toMeasure, inferInstance⟩

/-- Every finite D0 singleton has precisely its encoded rational mass. -/
theorem rationalInitialProbability_singleton {n : ℕ}
    (initial : RationalInitialLaw n) (x : Fin n) :
    (rationalInitialProbability initial).toMeasure {decode x} =
      ENNReal.ofReal (initial.weight x : ℝ) := by
  change (rationalInitialPMF initial).toMeasure {decode x} = _
  rw [PMF.toMeasure_apply_singleton (rationalInitialPMF initial)
    (decode x) (measurableSet_singleton (decode x))]
  simp [rationalInitialPMF, PMF.ofFintype_apply, encode_decode]

/-- A checked finite rational initial-law event value is exactly the true
original D0 typed infinite-path eventual-true probability for that law.
No original Exact GR is needed and no mixture changes the B₁ optimizer. -/
theorem checked_rationalMixedEventValue_eq_actual_path
    {n : ℕ} [NeZero n]
    (K : RationalMarkovMatrix n)
    (cert : DirichletCertificate n)
    (hc : checkDirichlet K cert = true)
    (h : Fin n → Bool)
    (initial : RationalInitialLaw n) :
    ((realizedModel K).pathLaw
      (rationalInitialProbability initial).toMeasure).real
      (eventuallyObserved (fun y => h (encode y)) true) =
      (rationalMixedEventValue cert h initial : ℝ) := by
  classical
  let M := realizedModel K
  let ν := rationalInitialProbability initial
  let E := eventuallyObserved (fun y => h (encode y)) true
  have hE : MeasurableSet E :=
    eventuallyObserved_measurable _ true Measurable.of_discrete
  have hpath : M.pathLaw ν.toMeasure =
      canonicalPathLaw M.inducedKernel ν.toMeasure :=
    typed_pathLaw_eq_canonical M ν.toMeasure
  have hmixture := canonicalPathLaw_event_initial_mixture
    M.inducedKernel ν E hE
  have hpoint (x : Fin n) :
      (canonicalPathLaw M.inducedKernel (Measure.dirac (decode x)) E).toReal =
        (eventValue cert h x : ℝ) := by
    have hp := checked_eventValue_eq_actual_path K cert hc h x
    rw [typed_pathLaw_eq_canonical] at hp
    simpa only [M, E, Measure.real] using hp
  have hn (x : Fin n) : (0 : ℝ) ≤ (initial.weight x : ℝ) := by
    exact_mod_cast initial.nonneg x
  calc
    ((realizedModel K).pathLaw ν.toMeasure).real E =
        (∑ y : PermanssonLean.JointState Unit (Fin n),
          ν.toMeasure {y} *
            canonicalPathLaw M.inducedKernel (Measure.dirac y) E).toReal := by
      rw [Measure.real, hpath, hmixture]
    _ = ∑ y : PermanssonLean.JointState Unit (Fin n),
          (ν.toMeasure {y}).toReal *
            (canonicalPathLaw M.inducedKernel (Measure.dirac y) E).toReal := by
      rw [ENNReal.toReal_sum (by finiteness)]
      congr 1
      funext y
      rw [ENNReal.toReal_mul]
    _ = ∑ x : Fin n,
          (initial.weight x : ℝ) * (eventValue cert h x : ℝ) := by
      change (∑ y : Unit × Fin n,
        (ν.toMeasure {y}).toReal *
          (canonicalPathLaw M.inducedKernel (Measure.dirac y) E).toReal) = _
      simp only [Fintype.sum_prod_type, Fintype.sum_unique]
      apply Finset.sum_congr rfl
      intro x _
      change (ν.toMeasure {decode x}).toReal *
        (canonicalPathLaw M.inducedKernel (Measure.dirac (decode x)) E).toReal =
          (initial.weight x : ℝ) * (eventValue cert h x : ℝ)
      have hw : (ν.toMeasure {decode x}).toReal =
          (initial.weight x : ℝ) := by
        change ((rationalInitialProbability initial).toMeasure
          {decode x}).toReal = _
        rw [rationalInitialProbability_singleton]
        exact ENNReal.toReal_ofReal (hn x)
      rw [hw, hpoint x]
    _ = (rationalMixedEventValue cert h initial : ℝ) := by
      simp only [rationalMixedEventValue, Rat.cast_sum, Rat.cast_mul]

end
end C10
end ReverseSolver
end PermanssonResearch
