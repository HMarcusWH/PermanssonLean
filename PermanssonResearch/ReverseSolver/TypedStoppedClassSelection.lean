import PermanssonResearch.ReverseSolver.TypedStoppedClassAbsorption
import PermanssonResearch.ReverseSolver.RationalBSCCPartition
import PermanssonResearch.ReverseSolver.CanonicalClosedClassHitting
import PermanssonResearch.MultipleLimit.CanonicalRecurrentResidence
import Mathlib.Tactic

/-!
# C10 — actual selected recurrent-class weights from rational Cramer computation

Under the genuine alpha/P/U path law, once a bottom recurrent class is
entered, the chain never leaves it almost surely. Thus a stopped first
entry into a selected class before any other recurrent class coincides
a.s. with eventual selection of that class. This bridges exact rational
Cramer class weights to the canonical selector, without an assumed
`exact_values` field or reusing a selector from the baseline kernel.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

open FiniteStrategicRealization
open PermanssonResearch.MultipleLimit.FiniteCanonicalPath
open PermanssonResearch.MultipleLimit.KernelCommunication
open PermanssonResearch.MultipleLimit.RecurrentClassDecomposition
open PermanssonResearch.MultipleLimit.CanonicalRecurrentResidence
open PermanssonResearch.MultipleLimit.CanonicalClassSelector

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

/-- Stopped first-entry into C and ever visiting C are equivalent on a
probability-one subset of the actual path law. The proof explicitly rules
out exits after entry into any other closed bottom class. -/
theorem typedStopped_iff_everHit_ae {n : ℕ} [NeZero n]
    (L : RationalMarkovMatrix n)
    (C : Finset (Fin n)) (hC : C ∈ bottomClasses L)
    (μ : ProbabilityMeasure (PermanssonLean.JointState Unit (Fin n))) :
    ∀ᵐ w ∂(realizedModel L).pathLaw μ.toMeasure,
      (w ∈ (⋃ T : ℕ, typedStoppedClassEvent L C T) ↔
        ∃ t : ℕ, encode (w t) ∈ C) := by
  let K := (realizedModel L).inducedKernel
  have hstay := all_closed_classes_stay_ae K μ
  change ∀ᵐ w ∂(realizedModel L).pathLaw μ.toMeasure,
      ∀ D : Set (PermanssonLean.JointState Unit (Fin n)),
        ClosedSubset K D → ∀ t : ℕ, w t ∈ D →
          ∀ u : ℕ, t ≤ u → w u ∈ D at hstay
  filter_upwards [hstay] with w hwstay
  rw [typedStoppedClassEvent_iUnion L C]
  constructor
  · rintro ⟨t, htC, _⟩
    exact ⟨t, htC⟩
  · rintro ⟨t, htC⟩
    refine ⟨t, htC, ?_⟩
    intro s hs hsR
    obtain ⟨hsUnion, hsNotC⟩ := Finset.mem_sdiff.mp hsR
    obtain ⟨D, hD, hsD⟩ := Finset.mem_biUnion.mp hsUnion
    have hDnative : decodedClass D ∈ RecurrentClasses K := by
      have h := (bottomClasses_native_iff L L D).mp hD
      simpa [K, rationalStrategicIntervention_applied] using h
    have hDclosed : ClosedSubset K (decodedClass D) :=
      recurrentClasses_closed K hDnative
    have hsNative : w s ∈ decodedClass D := by
      simpa [decodedClass] using hsD
    have htNative : w t ∈ decodedClass D :=
      hwstay (decodedClass D) hDclosed s hsNative t (Nat.le_of_lt hs)
    have htD : encode (w t) ∈ D := by
      simpa [decodedClass] using htNative
    have hEq := bottomClasses_common_member_eq
      L D C hD hC (encode (w t)) htD htC
    exact hsNotC (by rw [← hEq]; exact hsD)

/-- Exact equality of true infinite-path probabilities, not merely an
a.e. statement about a custom numerical trajectory. -/
theorem typedStopped_mass_eq_everHit {n : ℕ} [NeZero n]
    (L : RationalMarkovMatrix n)
    (C : Finset (Fin n)) (hC : C ∈ bottomClasses L) (x : Fin n) :
    (realizedModel L).pathLaw (Measure.dirac (decode x))
      (⋃ T : ℕ, typedStoppedClassEvent L C T) =
    (realizedModel L).pathLaw (Measure.dirac (decode x))
      {w : ℕ → PermanssonLean.JointState Unit (Fin n) |
        ∃ t : ℕ, encode (w t) ∈ C} := by
  have hAE := typedStopped_iff_everHit_ae L C hC (diracProba (decode x))
  change ∀ᵐ w ∂(realizedModel L).pathLaw (Measure.dirac (decode x)),
      (_ ↔ _) at hAE
  exact measure_congr (by
    filter_upwards [hAE] with w hw
    exact propext hw)

/-- The genuinely canonical infinite-path selected class mass equals the
computed rational Cramer weight for every source matrix and state.
The target class is always derived from L's own kernel. -/
theorem cramerWeight_eq_canonical_selected_class {n : ℕ} [NeZero n]
    (L : RationalMarkovMatrix n)
    (C : Finset (Fin n)) (hC : C ∈ bottomClasses L) (x : Fin n) :
    (cramerWeight L C x : ℝ) =
      ((realizedModel L).pathLaw (Measure.dirac (decode x))
        ((selectedRepresentative (realizedModel L).inducedKernel) ⁻¹'
          decodedClass C)).toReal := by
  let K := (realizedModel L).inducedKernel
  have hNative : decodedClass C ∈ RecurrentClasses K := by
    have h := (bottomClasses_native_iff L L C).mp hC
    simpa [K, rationalStrategicIntervention_applied] using h
  have hclosed : ClosedSubset K (decodedClass C) :=
    recurrentClasses_closed K hNative
  have hEver := canonical_selected_closed_mass_eq_ever_hit
    K (decodedClass C) hclosed (decode x)
  change (realizedModel L).pathLaw (Measure.dirac (decode x))
      ((selectedRepresentative K) ⁻¹' decodedClass C) =
    (realizedModel L).pathLaw (Measure.dirac (decode x))
      {w : ℕ → PermanssonLean.JointState Unit (Fin n) |
        ∃ t : ℕ, w t ∈ decodedClass C} at hEver
  calc
    (cramerWeight L C x : ℝ) =
        ((realizedModel L).pathLaw (Measure.dirac (decode x))).real
          (⋃ T : ℕ, typedStoppedClassEvent L C T) :=
      (cramerWeight_eq_typedStoppedClass_probability L C hC x).symm
    _ = ((realizedModel L).pathLaw (Measure.dirac (decode x))).real
          {w : ℕ → PermanssonLean.JointState Unit (Fin n) |
            ∃ t : ℕ, encode (w t) ∈ C} := by
      exact congrArg ENNReal.toReal (typedStopped_mass_eq_everHit L C hC x)
    _ = (((realizedModel L).pathLaw (Measure.dirac (decode x)))
          ((selectedRepresentative K) ⁻¹' decodedClass C)).toReal := by
      have hEq :
          {w : ℕ → PermanssonLean.JointState Unit (Fin n) |
             ∃ t : ℕ, encode (w t) ∈ C} =
          {w : ℕ → PermanssonLean.JointState Unit (Fin n) |
             ∃ t : ℕ, w t ∈ decodedClass C} := by
        ext w
        simp [decodedClass]
      rw [hEq, ← hEver]
      rfl

end
end C10
end ReverseSolver
end PermanssonResearch