import PermanssonResearch.MultipleLimit.FiniteObservedBadClassReachability
import Mathlib.Tactic

/-!
# C8-06 — exact positive-edge support transport across finite kernels

Equality of positive singleton transition supports preserves reachability,
communication classes, recurrence and good/bad Boolean class labels.
It does NOT imply equality of kernel entries, canonical path measures,
recurrent selection WEIGHTS, numerical margins or typed models.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit
namespace ObservedSupportInvariance

set_option autoImplicit false

open KernelCommunication
open RecurrentClassDecomposition
open CanonicalClassSelector
open FiniteObservedClassSupport
open FiniteObservedBadClassReachability

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [Nonempty Y]
variable (K L : Kernel Y Y)

/-- Exact equality of transition support, not TV closeness, support
inclusion or a floating point cutoff. -/
def SamePositiveSupport : Prop :=
  ∀ i j : Y, PositiveEdge K i j ↔ PositiveEdge L i j

theorem reachable_iff (hs : SamePositiveSupport K L)
    (i j : Y) :
    Reachable K i j ↔ Reachable L i j := by
  constructor
  · intro hij
    induction hij with
    | refl => exact Relation.ReflTransGen.refl
    | @tail a b hab hbc ih =>
      exact Relation.ReflTransGen.tail ih ((hs a b).mp hbc)
  · intro hij
    induction hij with
    | refl => exact Relation.ReflTransGen.refl
    | @tail a b hab hbc ih =>
      exact Relation.ReflTransGen.tail ih ((hs a b).mpr hbc)

theorem communicates_iff (hs : SamePositiveSupport K L)
    (i j : Y) :
    Communicates K i j ↔ Communicates L i j := by
  exact and_congr
    (reachable_iff K L hs i j)
    (reachable_iff K L hs j i)

theorem communicatingClass_eq (hs : SamePositiveSupport K L)
    (i : Y) :
    CommunicatingClass K i = CommunicatingClass L i := by
  ext j
  exact communicates_iff K L hs i j

theorem closedSubset_iff (hs : SamePositiveSupport K L)
    (C : Set Y) :
    ClosedSubset K C ↔ ClosedSubset L C := by
  constructor
  · intro hC i hi j he
    exact hC i hi j ((hs i j).mpr he)
  · intro hC i hi j he
    exact hC i hi j ((hs i j).mp he)

theorem recurrentState_iff (hs : SamePositiveSupport K L)
    (i : Y) :
    IsRecurrentState K i ↔ IsRecurrentState L i := by
  change ClosedSubset K (CommunicatingClass K i) ↔
    ClosedSubset L (CommunicatingClass L i)
  rw [communicatingClass_eq K L hs i]
  exact closedSubset_iff K L hs _

theorem recurrentClasses_eq (hs : SamePositiveSupport K L) :
    RecurrentClasses K = RecurrentClasses L := by
  classical
  apply Finset.ext
  intro C
  constructor
  · intro hC
    obtain ⟨i, hi, hEq⟩ := (recurrentClasses_mem_iff K C).mp hC
    apply (recurrentClasses_mem_iff L C).mpr
    refine ⟨i, (recurrentState_iff K L hs i).mp hi, ?_⟩
    exact (communicatingClass_eq K L hs i).symm.trans hEq
  · intro hC
    obtain ⟨i, hi, hEq⟩ := (recurrentClasses_mem_iff L C).mp hC
    apply (recurrentClasses_mem_iff K C).mpr
    refine ⟨i, (recurrentState_iff K L hs i).mpr hi, ?_⟩
    exact (communicatingClass_eq K L hs i).trans hEq

theorem classRepresentative_eq (hs : SamePositiveSupport K L)
    (i : Y) :
    classRepresentative K i = classRepresentative L i := by
  unfold classRepresentative
  rw [communicatingClass_eq K L hs i]

theorem recurrentRepresentatives_eq
    (hs : SamePositiveSupport K L) :
    recurrentRepresentatives K = recurrentRepresentatives L := by
  classical
  apply Finset.ext
  intro i
  change (i ∈ Finset.univ.filter
      (fun z => z ∈ RecurrentStates K ∧ classRepresentative K z = z)) ↔
    (i ∈ Finset.univ.filter
      (fun z => z ∈ RecurrentStates L ∧ classRepresentative L z = z))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (IsRecurrentState K i ∧ classRepresentative K i = i) ↔
    (IsRecurrentState L i ∧ classRepresentative L i = i)
  rw [recurrentState_iff K L hs i, classRepresentative_eq K L hs i]

theorem allTrueClass_iff (hs : SamePositiveSupport K L)
    (h : Y → Bool) (i : Y) :
    AllTrueClass K h i ↔ AllTrueClass L h i := by
  unfold AllTrueClass
  rw [communicatingClass_eq K L hs i]

theorem goodRecurrentRepresentatives_eq
    (hs : SamePositiveSupport K L) (h : Y → Bool) :
    goodRecurrentRepresentatives K h =
      goodRecurrentRepresentatives L h := by
  classical
  apply Finset.ext
  intro i
  change (i ∈ (recurrentRepresentatives K).filter
      (AllTrueClass K h)) ↔
    (i ∈ (recurrentRepresentatives L).filter
      (AllTrueClass L h))
  simp only [Finset.mem_filter]
  rw [recurrentRepresentatives_eq K L hs,
    allTrueClass_iff K L hs h i]

theorem badRecurrentRepresentatives_eq
    [IsMarkovKernel K] [IsMarkovKernel L]
    (hs : SamePositiveSupport K L) (h : Y → Bool) :
    badRecurrentRepresentatives K h =
      badRecurrentRepresentatives L h := by
  classical
  apply Finset.ext
  intro i
  change (i ∈ (recurrentRepresentatives K).filter
      (fun z => ¬ AllTrueClass K h z)) ↔
    (i ∈ (recurrentRepresentatives L).filter
      (fun z => ¬ AllTrueClass L h z))
  simp only [Finset.mem_filter]
  rw [recurrentRepresentatives_eq K L hs,
    allTrueClass_iff K L hs h i]

/-- A graph-reachable GOOD recurrent representative is a support-only
concept; the mass of selecting it is NOT support-invariant. -/
theorem goodReachability_iff
    [IsMarkovKernel K] [IsMarkovKernel L]
    (hs : SamePositiveSupport K L) (h : Y → Bool) (y : Y) :
    (∃ i ∈ goodRecurrentRepresentatives K h, Reachable K y i) ↔
      (∃ i ∈ goodRecurrentRepresentatives L h, Reachable L y i) := by
  constructor
  · rintro ⟨i, hi, hreach⟩
    exact ⟨i, by rwa [goodRecurrentRepresentatives_eq K L hs] at hi,
      (reachable_iff K L hs y i).mp hreach⟩
  · rintro ⟨i, hi, hreach⟩
    exact ⟨i, by rwa [goodRecurrentRepresentatives_eq K L hs],
      (reachable_iff K L hs y i).mpr hreach⟩

theorem badReachability_iff
    [IsMarkovKernel K] [IsMarkovKernel L]
    (hs : SamePositiveSupport K L) (h : Y → Bool) (y : Y) :
    (∃ i ∈ badRecurrentRepresentatives K h, Reachable K y i) ↔
      (∃ i ∈ badRecurrentRepresentatives L h, Reachable L y i) := by
  constructor
  · rintro ⟨i, hi, hreach⟩
    exact ⟨i, by rwa [badRecurrentRepresentatives_eq K L hs] at hi,
      (reachable_iff K L hs y i).mp hreach⟩
  · rintro ⟨i, hi, hreach⟩
    exact ⟨i, by rwa [badRecurrentRepresentatives_eq K L hs],
      (reachable_iff K L hs y i).mpr hreach⟩

end ObservedSupportInvariance
end MultipleLimit
end PermanssonResearch
