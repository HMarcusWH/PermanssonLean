import PermanssonResearch.ReverseSolver.TypedStoppedClassSelection
import PermanssonResearch.ReverseSolver.RationalEventuallyObserved
import PermanssonResearch.MultipleLimit.FiniteObservedEventMass
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# C10 — computed Cramer event mass equals the true canonical infinite event

For every nonempty finite rational Markov matrix realized as a genuine
D0 action-selection strategic-world model, the computed good-bottom-class
weight sum is EXACTLY the measure of the same predeclared eventual-true
Boolean event under the original infinite Ionescu–Tulcea path law.
This is neither a sampled finite-horizon approximation nor an assumed
probability-value adapter. The descriptor is fixed on every state.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

open FiniteStrategicRealization
open PermanssonResearch.MultipleLimit.FiniteCanonicalPath
open PermanssonResearch.MultipleLimit.FiniteObservedClassSupport
open PermanssonResearch.MultipleLimit.FiniteObservedEventMass
open PermanssonResearch.MultipleLimit.FrozenObservedEvent
open PermanssonResearch.MultipleLimit.CanonicalClassSelector
open PermanssonResearch.MultipleLimit.KernelCommunication
open PermanssonResearch.MultipleLimit.RecurrentClassDecomposition

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

/-- The native selected recurrent representative is assigned its complete,
normalized exact-rational bottom component. -/
def selectedRationalClass {n : ℕ} [NeZero n]
    (L : RationalMarkovMatrix n)
    (w : ℕ → PermanssonLean.JointState Unit (Fin n)) : Finset (Fin n) :=
  component L (encode (selectedRepresentative (realizedModel L).inducedKernel w))

/-- The chosen bottom class is genuinely recurrent, on ALL paths including
exceptional paths where the canonical selector uses its fallback state. -/
theorem selectedRationalClass_mem {n : ℕ} [NeZero n]
    (L : RationalMarkovMatrix n)
    (w : ℕ → PermanssonLean.JointState Unit (Fin n)) :
    selectedRationalClass L w ∈ bottomClasses L := by
  let K := (realizedModel L).inducedKernel
  let s := selectedRepresentative K w
  have hs0 : IsRecurrentState K s := by
    exact selectedRepresentative_recurrent K w
  have hs : IsRecurrentState
      (rationalStrategicIntervention L L).intervention.apply.inducedKernel
      (decode (encode s)) := by
    simpa [K, s, rationalStrategicIntervention_applied, decode_encode] using hs0
  exact (bottom_component_iff_native_recurrent L L (encode s)).mpr hs

/-- Each path has exactly one computed class label: membership in a
specified bottom class is equivalent to equality of its chosen index. -/
theorem selectedRationalClass_eq_iff_selected_mem {n : ℕ} [NeZero n]
    (L : RationalMarkovMatrix n)
    (C : Finset (Fin n)) (hC : C ∈ bottomClasses L)
    (w : ℕ → PermanssonLean.JointState Unit (Fin n)) :
    selectedRationalClass L w = C ↔
      selectedRepresentative (realizedModel L).inducedKernel w ∈ decodedClass C := by
  let K := (realizedModel L).inducedKernel
  let s := selectedRepresentative K w
  have hsSelf : s ∈ decodedClass (component L (encode s)) := by
    have hp := (component_native_iff L L (encode s) (encode s)).mpr
      (by simpa [K, rationalStrategicIntervention_applied, decode_encode]
        using (mem_communicatingClass K s))
    simpa [decodedClass, encode_decode] using hp
  constructor
  · intro hEq
    have hComp : component L (encode s) = C := by
      simpa [selectedRationalClass, s, K] using hEq
    rw [hComp] at hsSelf
    simpa only [s, K] using hsSelf
  · intro hsC
    have hNative : decodedClass C ∈ RecurrentClasses K := by
      have h := (bottomClasses_native_iff L L C).mp hC
      simpa [K, rationalStrategicIntervention_applied] using h
    obtain ⟨i, _, hi⟩ := (recurrentClasses_mem_iff K _).mp hNative
    have hsi : s ∈ CommunicatingClass K i := by
      rw [hi]
      exact hsC
    have hClass : CommunicatingClass K s = decodedClass C :=
      (communicatingClass_eq_of_communicates K
        (communicates_symm K hsi)).trans hi
    have hOwn : decodedClass (component L (encode s)) =
        CommunicatingClass K s := by
      simpa [K, rationalStrategicIntervention_applied, decode_encode] using
        (decodedClass_component_eq_native L L (encode s))
    have hComp : component L (encode s) = C :=
      decodedClass_injective (hOwn.trans hClass)
    exact hComp

/-- A selected bottom component has the globally frozen all-true label
iff the genuine selected physical recurrent communicating class does. -/
theorem good_selectedRationalClass_iff_native {n : ℕ} [NeZero n]
    (L : RationalMarkovMatrix n) (h : Fin n → Bool)
    (w : ℕ → PermanssonLean.JointState Unit (Fin n)) :
    GoodClass h (selectedRationalClass L w) ↔
      AllTrueClass (realizedModel L).inducedKernel
        (fun y => h (encode y))
        (selectedRepresentative (realizedModel L).inducedKernel w) := by
  let K := (realizedModel L).inducedKernel
  let s := selectedRepresentative K w
  have hEq : decodedClass (selectedRationalClass L w) =
      CommunicatingClass K s := by
    simpa [selectedRationalClass, s, K,
      rationalStrategicIntervention_applied, decode_encode] using
      (decodedClass_component_eq_native L L (encode s))
  constructor
  · intro hgood y hy
    have hmem : encode y ∈ selectedRationalClass L w := by
      have hx : y ∈ decodedClass (selectedRationalClass L w) := by
        rw [hEq]
        exact hy
      simpa [decodedClass] using hx
    exact hgood (encode y) hmem
  · intro hgood x hx
    have hy : decode x ∈ CommunicatingClass K s := by
      rw [← hEq]
      simpa [decodedClass] using hx
    simpa [encode_decode] using hgood (decode x) hy

/-- The class assignment is measurable; its domain is the true infinite
path space and its range is a finite set of physical bottom-class subsets. -/
theorem selectedRationalClass_measurable {n : ℕ} [NeZero n]
    (L : RationalMarkovMatrix n) :
    Measurable (selectedRationalClass L) := by
  have hfinite : Measurable
      (fun y : PermanssonLean.JointState Unit (Fin n) =>
        component L (encode y)) := Measurable.of_discrete
  exact hfinite.comp
    (selectedRepresentative_measurable (realizedModel L).inducedKernel)

/-- Exact source-specific probability equality for the global frozen
Boolean eventual-true event. Each intervention uses its OWN bottom classes
and exact Cramer values; no numerical-to-path-law premise appears. -/
theorem cramer_eventValue_eq_canonical_probability {n : ℕ} [NeZero n]
    (L : RationalMarkovMatrix n) (h : Fin n → Bool) (x : Fin n) :
    ((realizedModel L).pathLaw (Measure.dirac (decode x))).real
      (eventuallyObserved (fun y => h (encode y)) true) =
    (∑ C ∈ (bottomClasses L).filter (GoodClass h),
      (cramerWeight L C x : ℝ)) := by
  let K := (realizedModel L).inducedKernel
  let P := (realizedModel L).pathLaw (Measure.dirac (decode x))
  let G : Finset (Finset (Fin n)) := (bottomClasses L).filter (GoodClass h)
  let chosen := selectedRationalClass L
  have hAE := eventuallyObserved_iff_selectedGood_ae K
    (fun y => h (encode y)) (diracProba (decode x))
  change ∀ᵐ w ∂P,
      (w ∈ eventuallyObserved (fun y => h (encode y)) true ↔
        AllTrueClass K (fun y => h (encode y))
          (selectedRepresentative K w)) at hAE
  have hEvent : ∀ᵐ w ∂P,
      (w ∈ eventuallyObserved (fun y => h (encode y)) true ↔
        chosen w ∈ G) := by
    filter_upwards [hAE] with w hw
    rw [hw]
    simp only [G, Finset.mem_filter]
    constructor
    · intro hnative
      exact ⟨selectedRationalClass_mem L w,
        (good_selectedRationalClass_iff_native L h w).mpr hnative⟩
    · intro hselected
      exact (good_selectedRationalClass_iff_native L h w).mp hselected.2
  have hSets :
      eventuallyObserved (fun y => h (encode y)) true =ᵐ[P]
        (chosen ⁻¹' (↑G : Set (Finset (Fin n)))) := by
    filter_upwards [hEvent] with w hw
    exact propext hw
  have hMeas : ∀ C ∈ G, MeasurableSet (chosen ⁻¹' ({C} : Set (Finset (Fin n)))) :=
    fun C _ => (measurableSet_singleton C).preimage
      (selectedRationalClass_measurable L)
  calc
    P.real (eventuallyObserved (fun y => h (encode y)) true) =
        P.real (chosen ⁻¹' (↑G : Set (Finset (Fin n)))) :=
      measureReal_congr hSets
    _ = ∑ C ∈ G, P.real (chosen ⁻¹' ({C} : Set (Finset (Fin n)))) :=
      (sum_measureReal_preimage_singleton G hMeas).symm
    _ = ∑ C ∈ G, (cramerWeight L C x : ℝ) := by
      apply Finset.sum_congr rfl
      intro C hC
      have hBottom : C ∈ bottomClasses L := (Finset.mem_filter.mp hC).1
      have hSet : (chosen ⁻¹' ({C} : Set (Finset (Fin n)))) =
          ((selectedRepresentative K) ⁻¹' decodedClass C) := by
        ext w
        simpa [chosen, Set.mem_preimage, Set.mem_singleton_iff] using
          (selectedRationalClass_eq_iff_selected_mem L C hBottom w)
      rw [hSet]
      exact (cramerWeight_eq_canonical_selected_class L C hBottom x).symm

end
end C10
end ReverseSolver
end PermanssonResearch