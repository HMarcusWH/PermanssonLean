import PermanssonResearch.MultipleLimit.FiniteObservedEventMass
import PermanssonResearch.MultipleLimit.PositiveKernelPowers
import PermanssonResearch.MultipleLimit.CanonicalKernelMarginals
import PermanssonResearch.MultipleLimit.CanonicalClassContinuation
import Mathlib.Tactic

/-!
# C8-01 — positive-edge class reachability and real canonical selection

For any finite genuine homogeneous Markov kernel, a recurrent
representative has strictly positive selected-class probability from
a point exactly when it is reachable from that point by a finite
path of strictly positive transition atoms.

No rational surrogate, numerical cutoff, assumed aperiodicity or
cross-kernel class-selector transport is used.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteObservedSupportReachability

set_option autoImplicit false

open KernelCommunication
open RecurrentClassDecomposition
open CanonicalClassSelector
open CanonicalClassWeights
open CanonicalClassContinuation
open CanonicalRecurrentResidence
open FiniteCanonicalPath
open CanonicalKernelMarginals
open PositiveKernelPowers
open FiniteObservedClassSupport
open FiniteObservedEventMass
open FrozenObservedEvent

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [Nonempty Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- Graph reachability is constructed from strictly positive
ONE-STEP kernel atoms, including the zero-length path at y. -/
def reachableRegion (y : Y) : Set Y :=
  {z | Reachable K y z}

/-- The positive graph-reachable region is closed under the actual
kernel: a positive edge cannot leave the set by definition. -/
theorem reachableRegion_closed (y : Y) :
    ClosedSubset K (reachableRegion K y) := by
  intro z hz w hzw
  exact reachable_trans K hz (reachable_single K hzw)

/-- The time-zero coordinate in the true canonical point-started
infinite path is the declared initial state almost surely. -/
theorem canonical_start_eq_ae (y : Y) :
    ∀ᵐ w ∂canonicalPathLaw K (Measure.dirac y), w 0 = y := by
  rw [ae_iff]
  have h := canonical_eval_zero_dirac K y
  have hzero :
      ((canonicalPathLaw K (Measure.dirac y)).map
        (fun w : ℕ → Y => w 0))
          (({y} : Set Y)ᶜ) = 0 := by
    rw [h]
    simp
  rw [Measure.map_apply (measurable_pi_apply 0)
    (measurableSet_singleton y).compl] at hzero
  change (canonicalPathLaw K (Measure.dirac y))
    {w : ℕ → Y | w 0 ≠ y} = 0 at hzero
  exact hzero

/-- Almost every selected recurrent representative is accessible
from the ACTUAL point start in the same positive-edge graph.
The argument uses genuine path law closure and eventually selected
class residence; no presumed graph/probability equivalence. -/
theorem selected_reachable_ae (y : Y) :
    ∀ᵐ w ∂canonicalPathLaw K (Measure.dirac y),
      Reachable K y (selectedRepresentative K w) := by
  let C := reachableRegion K y
  filter_upwards [canonical_start_eq_ae K y,
      closed_stay_after_entry_ae K (diracProba y) C
        (reachableRegion_closed K y),
      selected_class_eventual_ae K (diracProba y)]
    with w hstart hstay hselected
  obtain ⟨n, hn⟩ := hselected
  have h0 : w 0 ∈ C := by
    rw [hstart]
    exact reachable_refl K y
  have hreach : Reachable K y (w n) :=
    hstay 0 h0 n (Nat.zero_le n)
  have hback : Reachable K (w n) (selectedRepresentative K w) :=
    (hn n le_rfl).2
  exact reachable_trans K hreach hback

/-- The key new C8 bridge. Strictly positive canonical probability of
selecting a recurrent class iff the class representative is reachable
through the exact positive-transition graph. All class representatives
come from THIS kernel. -/
theorem selected_weight_nonzero_iff_reachable
    (y i : Y) (hi : i ∈ recurrentRepresentatives K) :
    canonicalPathLaw K (Measure.dirac y)
      ((selectedRepresentative K) ⁻¹' ({i} : Set Y)) ≠ 0 ↔
      Reachable K y i := by
  classical
  let P := canonicalPathLaw K (Measure.dirac y)
  constructor
  · intro hpos
    by_contra hno
    have hAE := selected_reachable_ae K y
    rw [ae_iff] at hAE
    have hsubset :
        (selectedRepresentative K) ⁻¹' ({i} : Set Y) ⊆
          {w : ℕ → Y | ¬ Reachable K y
            (selectedRepresentative K w)} := by
      intro w hw
      have hsel : selectedRepresentative K w = i := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hw
      change ¬Reachable K y (selectedRepresentative K w)
      simpa only [hsel] using hno
    exact hpos (measure_mono_null hsubset hAE)
  · intro hreach
    obtain ⟨n, hn⟩ := positive_kernel_power_of_reachable K hreach
    have hs : i ∈ RecurrentStates K ∧ classRepresentative K i = i := by
      have hf :
          i ∈ (Finset.univ.filter
            (fun z => z ∈ RecurrentStates K ∧
              classRepresentative K z = z)) := hi
      exact (Finset.mem_filter.mp hf).2
    have hrec : i ∈ RecurrentStates K := hs.1
    have hfixed : classRepresentative K i = i := hs.2
    have hclass :
        CommunicatingClass K i ∈ RecurrentClasses K :=
      (recurrentClasses_mem_iff K _).mpr ⟨i, hrec, rfl⟩
    have hAE :
        ∀ᵐ w ∂P, w n = i → selectedRepresentative K w = i := by
      filter_upwards
        [all_closed_classes_stay_ae K (diracProba y),
         selected_class_identifies_unique_ae K (diracProba y)]
        with w hstay hunique
      intro hw
      have hmem : w n ∈ CommunicatingClass K i := by
        rw [hw]
        exact mem_communicatingClass K i
      have hev : EventuallyInClass w (CommunicatingClass K i) :=
        ⟨n, hstay (CommunicatingClass K i) hrec n hmem⟩
      have heq : CommunicatingClass K i =
          CommunicatingClass K (selectedRepresentative K w) :=
        hunique (CommunicatingClass K i) hclass hev
      have hin : selectedRepresentative K w ∈ CommunicatingClass K i := by
        rw [heq]
        exact mem_communicatingClass K _
      have hs : classRepresentative K i =
          classRepresentative K (selectedRepresentative K w) :=
        classRepresentative_eq_of_communicates K hin
      calc
        selectedRepresentative K w =
            classRepresentative K (selectedRepresentative K w) :=
          (selectedRepresentative_fixed K w).symm
        _ = classRepresentative K i := hs.symm
        _ = i := hfixed
    have htime :
        P {w : ℕ → Y | w n = i} =
          (K ^ n) y ({i} : Set Y) := by
      have hm := canonical_eval_eq_kernel_pow K y n
      have h := congrArg
        (fun ν : Measure Y => ν ({i} : Set Y)) hm
      rw [Measure.map_apply (measurable_pi_apply n)
        (measurableSet_singleton i)] at h
      exact h
    have hpair :
        {w : ℕ → Y | w n = i} =ᵐ[P]
          ({w : ℕ → Y | w n = i} ∩
            ((selectedRepresentative K) ⁻¹' ({i} : Set Y))) := by
      filter_upwards [hAE] with w hw
      apply propext
      constructor
      · intro hnwi
        exact ⟨hnwi, hw hnwi⟩
      · intro hs
        exact hs.1
    have hmeasure :
        P {w : ℕ → Y | w n = i} ≤
          P ((selectedRepresentative K) ⁻¹' ({i} : Set Y)) := by
      rw [measure_congr hpair]
      exact measure_mono Set.inter_subset_right
    have hpositive :
        0 < P ((selectedRepresentative K) ⁻¹' ({i} : Set Y)) :=
      lt_of_lt_of_le (htime.symm ▸ hn) hmeasure
    exact ne_of_gt hpositive

/-- G1: positive probability of eventual true observation exactly
means that a GOOD recurrent representative is graph-reachable. -/
theorem eventual_true_positive_iff_reachable_good
    (h : Y → Bool) (y : Y) :
    0 < (canonicalPathLaw K (Measure.dirac y))
      (eventuallyObserved h true) ↔
      ∃ i ∈ goodRecurrentRepresentatives K h, Reachable K y i := by
  classical
  have hmass := eventuallyObserved_probability_eq_good_sum
    K h (diracProba y)
  change (canonicalPathLaw K (Measure.dirac y))
      (eventuallyObserved h true) =
    ∑ i ∈ goodRecurrentRepresentatives K h,
      (canonicalPathLaw K (Measure.dirac y))
        ((selectedRepresentative K) ⁻¹' ({i} : Set Y)) at hmass
  rw [hmass]
  constructor
  · intro hpos
    by_contra hn
    push_neg at hn
    have hzero (i : Y) (hi : i ∈ goodRecurrentRepresentatives K h) :
        canonicalPathLaw K (Measure.dirac y)
          ((selectedRepresentative K) ⁻¹' ({i} : Set Y)) = 0 := by
      by_contra hne
      exact hn i hi ((selected_weight_nonzero_iff_reachable K y i
        (Finset.mem_filter.mp hi).1).mp hne)
    have hsum :
        (∑ i ∈ goodRecurrentRepresentatives K h,
          canonicalPathLaw K (Measure.dirac y)
            ((selectedRepresentative K) ⁻¹' ({i} : Set Y))) = 0 :=
      Finset.sum_eq_zero (fun i hi => hzero i hi)
    exact (ne_of_gt hpos) hsum
  · rintro ⟨i, hi, hreach⟩
    have hne := (selected_weight_nonzero_iff_reachable K y i
      (Finset.mem_filter.mp hi).1).mpr hreach
    have hpositive : 0 < canonicalPathLaw K (Measure.dirac y)
        ((selectedRepresentative K) ⁻¹' ({i} : Set Y)) :=
      lt_of_le_of_ne bot_le (Ne.symm hne)
    exact lt_of_lt_of_le hpositive
      (Finset.single_le_sum
        (fun j hj => bot_le)
        (show i ∈ goodRecurrentRepresentatives K h from hi))

end FiniteObservedSupportReachability
end MultipleLimit
end PermanssonResearch
