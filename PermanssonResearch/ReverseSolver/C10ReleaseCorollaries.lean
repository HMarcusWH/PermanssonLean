import PermanssonResearch.ReverseSolver.TypedObservedCramerCorrespondence
import PermanssonResearch.ReverseSolver.RationalTypedSupportBridge
import PermanssonResearch.MultipleLimit.FiniteObservedSupportReachability
import PermanssonResearch.MultipleLimit.TypedObservedEventConstitution
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# C10 final correspondence corollaries

These results compose existing compiled C7/C8/C10 theorems. They are genuine
source-specific point-law/positive-reachability statements, NOT generic
external-game identification or unsupported regression status flags.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

open FiniteStrategicRealization
open RationalTypedSupportBridge
open PermanssonResearch.MultipleLimit.FiniteCanonicalPath
open PermanssonResearch.MultipleLimit.FiniteObservedSupportReachability
open PermanssonResearch.MultipleLimit.TypedObservedEventConstitution
open PermanssonResearch.MultipleLimit.FrozenObservedEvent
open PermanssonResearch.MultipleLimit.KernelCommunication
open PermanssonResearch.MultipleLimit.RecurrentClassDecomposition
open PermanssonResearch.MultipleLimit.CanonicalClassSelector

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

/-- The exact Cramer good-BSCC sum is also the original C7 kernel-specific
pointGoodMass, not merely an arithmetic occupation approximation. -/
theorem cramer_goodClass_eq_native_pointGoodMass {n : ℕ} [NeZero n]
    (L : RationalMarkovMatrix n) (h : Fin n → Bool) (x : Fin n) :
    (∑ C ∈ (bottomClasses L).filter (GoodClass h),
      (cramerWeight L C x : ℝ)) =
      (pointGoodMass (realizedModel L).inducedKernel
        (fun y => h (encode y)) (decode x)).toReal := by
  let M := realizedModel L
  let H := fun y : PermanssonLean.JointState Unit (Fin n) => h (encode y)
  have hEvent := cramer_eventValue_eq_canonical_probability L h x
  have hMass := (pointGoodMass_eq_event_probability M.inducedKernel
    H (decode x)).symm
  have hPath : M.pathLaw (Measure.dirac (decode x)) =
      canonicalPathLaw M.inducedKernel (Measure.dirac (decode x)) :=
    typed_pathLaw_eq_canonical M (Measure.dirac (decode x))
  calc
    (∑ C ∈ (bottomClasses L).filter (GoodClass h),
        (cramerWeight L C x : ℝ)) =
        (M.pathLaw (Measure.dirac (decode x))).real
          (eventuallyObserved H true) := by
      simpa only [M, H] using hEvent.symm
    _ = (pointGoodMass M.inducedKernel H (decode x)).toReal := by
      rw [hPath]
      simpa only [Measure.real] using congrArg ENNReal.toReal hMass

/-- A computed C10 bottom class has positive *actual rational Cramer*
absorption mass exactly when the source graph can reach any of its
members. This follows from the original C8 positive-representative
theorem and the C10 exact selected-class/Dirichlet correspondence. -/
theorem cramerWeight_real_pos_iff_class_reachable
    {n : ℕ} [NeZero n]
    (L : RationalMarkovMatrix n)
    (C : Finset (Fin n)) (hC : C ∈ bottomClasses L)
    (x : Fin n) :
    (0 : ℝ) < (cramerWeight L C x : ℝ) ↔
      ∃ z ∈ C, RationalReachable L x z := by
  let K := (realizedModel L).inducedKernel
  have hNative : decodedClass C ∈ RecurrentClasses K := by
    have h := (bottomClasses_native_iff L L C).mp hC
    simpa [K, rationalStrategicIntervention_applied] using h
  obtain ⟨y, hy, hClass⟩ := (recurrentClasses_mem_iff K _).mp hNative
  let i := classRepresentative K y
  have hi : i ∈ recurrentRepresentatives K := by
    simp only [recurrentRepresentatives, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change y ∈ RecurrentStates K at hy
    exact ⟨classRepresentative_recurrent K hy,
      classRepresentative_idempotent K y⟩
  have hiC : i ∈ decodedClass C := by
    rw [← hClass]
    exact classRepresentative_mem K y
  have hClassI : CommunicatingClass K i = decodedClass C := by
    exact (communicatingClass_eq_of_communicates K
      (communicates_symm K (classRepresentative_mem K y))).trans hClass
  have hSel (w : ℕ → PermanssonLean.JointState Unit (Fin n)) :
      selectedRepresentative K w ∈ decodedClass C ↔
        selectedRepresentative K w = i := by
    constructor
    · intro hw
      have hCom : selectedRepresentative K w ∈ CommunicatingClass K y := by
        rw [hClass]
        exact hw
      have hRep := classRepresentative_eq_of_communicates K hCom
      calc
        selectedRepresentative K w =
            classRepresentative K (selectedRepresentative K w) :=
          (selectedRepresentative_fixed K w).symm
        _ = classRepresentative K y := hRep.symm
        _ = i := rfl
    · intro hw
      rw [hw]
      exact hiC
  have hSet :
      (selectedRepresentative K) ⁻¹' decodedClass C =
        (selectedRepresentative K) ⁻¹'
          ({i} : Set (PermanssonLean.JointState Unit (Fin n))) := by
    ext w
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hSel w
  let P := canonicalPathLaw K (Measure.dirac (decode x))
  have hSource := cramerWeight_eq_canonical_selected_class L C hC x
  have hPath :
      (realizedModel L).pathLaw (Measure.dirac (decode x)) = P :=
    typed_pathLaw_eq_canonical (realizedModel L) (Measure.dirac (decode x))
  have hWeight : (cramerWeight L C x : ℝ) =
      (P ((selectedRepresentative K) ⁻¹'
        ({i} : Set (PermanssonLean.JointState Unit (Fin n))))).toReal := by
    calc
      (cramerWeight L C x : ℝ) =
        (((realizedModel L).pathLaw (Measure.dirac (decode x)))
          ((selectedRepresentative K) ⁻¹' decodedClass C)).toReal := by
            simpa only [K] using hSource
      _ = (P ((selectedRepresentative K) ⁻¹'
            ({i} : Set (PermanssonLean.JointState Unit (Fin n))))).toReal := by
            rw [hPath, hSet]
  have hFinite :
      P ((selectedRepresentative K) ⁻¹'
        ({i} : Set (PermanssonLean.JointState Unit (Fin n)))) ≠ ⊤ :=
    measure_ne_top _ _
  have hPos :
      (0 : ℝ) < (cramerWeight L C x : ℝ) ↔
        P ((selectedRepresentative K) ⁻¹'
          ({i} : Set (PermanssonLean.JointState Unit (Fin n)))) ≠ 0 := by
    rw [hWeight, ENNReal.toReal_pos_iff]
    constructor
    · exact fun h => ne_of_gt h.1
    · intro h
      exact ⟨pos_iff_ne_zero.mpr h, lt_top_iff_ne_top.mpr hFinite⟩
  have hReach :
      P ((selectedRepresentative K) ⁻¹'
        ({i} : Set (PermanssonLean.JointState Unit (Fin n)))) ≠ 0 ↔
        Reachable K (decode x) i := by
    exact selected_weight_nonzero_iff_reachable K (decode x) i hi
  have hNativeReach :
      Reachable K (decode x) i ↔
        ∃ z ∈ C, RationalReachable L x z := by
    constructor
    · intro h
      refine ⟨encode i, ?_, ?_⟩
      · change encode i ∈ C at hiC
        exact hiC
      · apply (rationalTyped_reachable_iff L L x (encode i)).mpr
        simpa [K, rationalStrategicIntervention_applied,
          decode_encode] using h
    · rintro ⟨z, hz, hzReach⟩
      have hzC : decode z ∈ decodedClass C := by
        change encode (decode z) ∈ C
        simpa only [encode_decode] using hz
      have hzCommunicates : decode z ∈ CommunicatingClass K i := by
        rw [hClassI]
        exact hzC
      have hzi : Reachable K (decode z) i :=
        (communicates_symm K hzCommunicates).1
      have hxz : Reachable K (decode x) (decode z) := by
        have h := (rationalTyped_reachable_iff L L x z).mp hzReach
        simpa [K, rationalStrategicIntervention_applied] using h
      exact reachable_trans K hxz hzi
  exact hPos.trans (hReach.trans hNativeReach)

end
end C10
end ReverseSolver
end PermanssonResearch
