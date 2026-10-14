import PermanssonResearch.ReverseSolver.TypedObservedCramerCorrespondence
import PermanssonResearch.ReverseSolver.RationalCramerCertification
import PermanssonResearch.ReverseSolver.RationalCertificateUniqueness
import PermanssonResearch.ReverseSolver.RationalConstitutiveMargin
import Mathlib.Tactic

/-!
# C10 — checked rational event values transport to actual infinite paths

No unverified `exact_values` field is supplied. The Dirichlet checker
certifies exact boundary/harmonic equations; universal Cramer acceptance
and uniqueness identify every accepted table with the genuine rational
reference. The separately proved path-law theorem identifies that value
with the fixed eventual-true infinite-path probability.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false
open FiniteStrategicRealization
open PermanssonResearch.MultipleLimit.FrozenObservedEvent

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

/-- An arbitrary accepted exact rational Dirichlet receipt has the
*actual* eventually-observed event probability, not merely a harmonic
score or another externally supplied probability vector. -/
theorem checked_eventValue_eq_actual_path {n : ℕ} [NeZero n]
    (K : RationalMarkovMatrix n)
    (cert : DirichletCertificate n)
    (hc : checkDirichlet K cert = true)
    (h : Fin n → Bool) (x : Fin n) :
    ((realizedModel K).pathLaw (Measure.dirac (decode x))).real
      (eventuallyObserved (fun y => h (encode y)) true) =
      (eventValue cert h x : ℝ) := by
  have hConditions := checkDirichlet_sound K cert hc
  have hReference := referenceDirichlet_check_true K
  calc
    ((realizedModel K).pathLaw (Measure.dirac (decode x))).real
        (eventuallyObserved (fun y => h (encode y)) true) =
      (∑ C ∈ (bottomClasses K).filter (GoodClass h),
        (cramerWeight K C x : ℝ)) :=
          cramer_eventValue_eq_canonical_probability K h x
    _ = (eventValue cert h x : ℝ) := by
      unfold eventValue
      rw [hConditions.1]
      push_cast
      apply Finset.sum_congr rfl
      intro C hC
      have hb : C ∈ bottomClasses K := (Finset.mem_filter.mp hC).1
      have heq := checked_class_column_unique K cert
        (referenceDirichletCertificate K) hc hReference C hb x
      simpa only [referenceDirichletCertificate] using
        congrArg (fun q : ℚ => (q : ℝ)) heq.symm

end
end C10
end ReverseSolver
end PermanssonResearch