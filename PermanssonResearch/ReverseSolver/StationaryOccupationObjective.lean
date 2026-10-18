import PermanssonResearch.ReverseSolver.C11ReferenceTypedBridge
import PermanssonResearch.ReverseSolver.TypedObservedCramerCorrespondence
import PermanssonResearch.MultipleLimit.FiniteOccupationRandomLaw
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Exact expectation of a functional of the actual random occupation limit

The descriptor and bounded functional are fixed before a policy is selected.
The exact evaluator is certified only on the Cramer-constructed rational class
laws. The connection with the actual infinite-path occupation limit is proved
here using the genuine C2 selector and the genuine C10 absorption weights.
Distinct physical bottom classes remain distinct summands.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch.ReverseSolver.StationaryOccupation

open FiniteStrategicRealization C10 C11
open PermanssonResearch.MultipleLimit.KernelCommunication
open PermanssonResearch.MultipleLimit.CanonicalClassSelector
open PermanssonResearch.MultipleLimit.ClassStationarySelectionLaw
open PermanssonResearch.MultipleLimit.FiniteOccupationRandomLaw

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

variable {n : ℕ} [NeZero n]
variable {H : Type*} [MeasurableSpace H] [TopologicalSpace H] [BorelSpace H]

/-- A predeclared functional, together with exact rational evaluation of its
values on the actual constructed rational class probabilities. -/
structure ExactClassFunctional (n : ℕ) [NeZero n] (H : Type*)
    [MeasurableSpace H] [TopologicalSpace H] [BorelSpace H] where
  descriptor : PermanssonLean.JointState Unit (Fin n) → H
  functional : ProbabilityMeasure H → ℝ
  bounded : ∃ M : ℝ, ∀ ν, |functional ν|≤M
  evaluate : RationalMarkovMatrix n → Finset (Fin n) → ℚ
  evaluate_exact : ∀ (L : RationalMarkovMatrix n) (C : Finset (Fin n))
    (hC : C ∈ bottomClasses L),
    functional ((certifiedProbability L (referenceClassCandidate L C)
      (referenceClassCandidate_check L C hC)).map descriptor) = (evaluate L C : ℝ)

noncomputable def nativeObservedClass (L : RationalMarkovMatrix n)
    (h : PermanssonLean.JointState Unit (Fin n) → H) (C : Finset (Fin n)) :
    ProbabilityMeasure H :=
  (stationaryForSet (realizedModel L).inducedKernel (decodedClass C)).map h

theorem exact_native_class (F : ExactClassFunctional n H)
    (L : RationalMarkovMatrix n) (C : Finset (Fin n)) (hC : C ∈ bottomClasses L) :
    F.functional (nativeObservedClass L F.descriptor C) = (F.evaluate L C : ℝ) := by
  have he := F.evaluate_exact L C hC
  rw [referenceClassCandidate_eq_native L L C hC] at he
  simpa only [rationalStrategicIntervention_applied,nativeObservedClass] using he

/-- Whole observed-law equality on each actual path, including the canonical
recurrent fallback on the exceptional set. -/
theorem occupationLimit_eq_selected_class (L : RationalMarkovMatrix n)
    (h : PermanssonLean.JointState Unit (Fin n) → H)
    (w : ℕ → PermanssonLean.JointState Unit (Fin n)) :
    observedOccupationLimit (realizedModel L).inducedKernel h w =
      nativeObservedClass L h (selectedRationalClass L w) := by
  have he := decodedClass_component_eq_native L L
    (encode (selectedRepresentative (realizedModel L).inducedKernel w))
  simp only [rationalStrategicIntervention_applied,decode_encode] at he
  simp only [observedOccupationLimit,physicalOccupationLimit,nativeObservedClass,
    selectedRationalClass,he]

def rationalObjective (F : ExactClassFunctional n H) (L : RationalMarkovMatrix n)
    (y : Fin n) : ℚ :=
  ∑ C ∈ bottomClasses L, cramerWeight L C y*F.evaluate L C

noncomputable def actualObjective (F : ExactClassFunctional n H)
    (L : RationalMarkovMatrix n) (y : Fin n) : ℝ :=
  ∫ w, F.functional (observedOccupationLimit (realizedModel L).inducedKernel
    F.descriptor w) ∂(realizedModel L).pathLaw (Measure.dirac (decode y))

private theorem functional_path_decomposition (F : ExactClassFunctional n H)
    (L : RationalMarkovMatrix n)
    (w : ℕ → PermanssonLean.JointState Unit (Fin n)) :
    F.functional (observedOccupationLimit (realizedModel L).inducedKernel F.descriptor w) =
      ∑ C ∈ bottomClasses L,
        (selectedRationalClass L ⁻¹' ({C} : Set (Finset (Fin n)))).indicator
          (fun _ => (F.evaluate L C : ℝ)) w := by
  classical
  have hs := selectedRationalClass_mem L w
  rw [occupationLimit_eq_selected_class,exact_native_class F L _ hs]
  symm
  rw [Finset.sum_eq_single (selectedRationalClass L w)]
  · simp
  · intro C _ hC
    simp [hC,Ne.symm hC]
  · exact fun h => (h hs).elim

/-- The occupation-functional random variable is integrable under the true
infinite canonical path law. No measurability of an arbitrary functional on
the entire space of laws is needed: on this model its range is finite. -/
theorem occupation_functional_integrable (F : ExactClassFunctional n H)
    (L : RationalMarkovMatrix n) (y : Fin n) :
    Integrable (fun w => F.functional (observedOccupationLimit
      (realizedModel L).inducedKernel F.descriptor w))
      ((realizedModel L).pathLaw (Measure.dirac (decode y))) := by
  classical
  simp_rw [functional_path_decomposition]
  apply integrable_finsetSum
  intro C _
  exact (integrable_const _).indicator
    ((measurableSet_singleton C).preimage (selectedRationalClass_measurable L))

/-- C10 absorption and C11 stationary laws give the exact expectation of the
functional of the genuine a.s. empirical occupation limit. -/
theorem rationalObjective_eq_actual (F : ExactClassFunctional n H)
    (L : RationalMarkovMatrix n) (y : Fin n) :
    (rationalObjective F L y : ℝ)=actualObjective F L y := by
  classical
  unfold actualObjective rationalObjective
  simp_rw [functional_path_decomposition]
  rw [integral_finsetSum]
  · push_cast
    apply Finset.sum_congr rfl
    intro C hC
    rw [integral_indicator_const _
      ((measurableSet_singleton C).preimage (selectedRationalClass_measurable L))]
    have hset : selectedRationalClass L ⁻¹' ({C} : Set (Finset (Fin n))) =
        (selectedRepresentative (realizedModel L).inducedKernel) ⁻¹' decodedClass C := by
      ext w
      simpa using selectedRationalClass_eq_iff_selected_mem L C hC w
    rw [hset]
    exact congrArg (fun q : ℝ => q*(F.evaluate L C : ℝ))
      (cramerWeight_eq_canonical_selected_class L C hC y)
  · intro C _
    exact (integrable_const _).indicator
      ((measurableSet_singleton C).preimage (selectedRationalClass_measurable L))

/-- Identical descriptor class laws receive identical functional values.
This never merges their physical state sets or their absorption weights. -/
theorem equal_descriptor_laws_equal_values (F : ExactClassFunctional n H)
    (L : RationalMarkovMatrix n) (C D : Finset (Fin n))
    (hC : C ∈ bottomClasses L) (hD : D ∈ bottomClasses L)
    (he : nativeObservedClass L F.descriptor C=nativeObservedClass L F.descriptor D) :
    F.evaluate L C=F.evaluate L D := by
  have hc := exact_native_class F L C hC
  have hd := exact_native_class F L D hD
  rw [he] at hc
  exact_mod_cast hc.symm.trans hd

end PermanssonResearch.ReverseSolver.StationaryOccupation
