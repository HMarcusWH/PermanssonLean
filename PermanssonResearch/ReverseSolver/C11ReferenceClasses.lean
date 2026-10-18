import PermanssonResearch.ReverseSolver.C11ReferenceProbability
import PermanssonResearch.ReverseSolver.C11StationaryFamily
import PermanssonResearch.ReverseSolver.RationalGraphCompleteness

/-!
# Construct and check the rational stationary candidate of each bottom class

The restricted matrix uses the actual class subtype, with no decorative states.
The output is extended by zero to the original state universe.
-/

namespace PermanssonResearch.ReverseSolver.C11

open C10 RationalTypedSupportBridge

def restrictedMatrix {n : ℕ} (K : RationalMarkovMatrix n) (C : Finset (Fin n)) :
    Matrix C C ℚ := fun x y => K.entry x.val y.val

theorem restrictedMatrix_stochastic {n : ℕ} (K : RationalMarkovMatrix n)
    (C : Finset (Fin n)) (hC : C ∈ bottomClasses K) :
    (∀ x y : C, 0≤restrictedMatrix K C x y) ∧
    ∀ x : C, ∑ y : C, restrictedMatrix K C x y=1 := by
  refine ⟨fun x y => K.entry_nonneg x y, ?_⟩
  intro x
  have hz (y : Fin n) (hy : y ∉ C) : K.entry x y=0 := by
    apply le_antisymm _ (K.entry_nonneg x y)
    exact not_lt.mp (fun hp => hy (bottomClasses_closed K C hC x x.property y hp))
  calc
    (∑ y : C, restrictedMatrix K C x y) = ∑ y ∈ C, K.entry x y :=
      Finset.sum_coe_sort C (fun y => K.entry x y)
    _ = ∑ y : Fin n, K.entry x y :=
      Finset.sum_subset (Finset.subset_univ C) (fun y _ hy => hz y hy)
    _ = 1 := K.row_sum_one x

private theorem lift_class_path {n : ℕ} (K : RationalMarkovMatrix n)
    (C : Finset (Fin n)) (hC : C ∈ bottomClasses K)
    (a b : Fin n) (ha : a ∈ C) (hp : RationalReachable K a b) :
    ∃ hb : b ∈ C, Relation.ReflTransGen
      (fun x y : C => 0<restrictedMatrix K C x y) ⟨a,ha⟩ ⟨b,hb⟩ := by
  induction hp with
  | refl => exact ⟨ha, Relation.ReflTransGen.refl⟩
  | @tail z w hzw hedge ih =>
      rcases ih with ⟨hz,hpath⟩
      have hw := bottomClasses_closed K C hC z hz w hedge
      exact ⟨hw, Relation.ReflTransGen.tail hpath hedge⟩

theorem restrictedMatrix_irreducible {n : ℕ} (K : RationalMarkovMatrix n)
    (C : Finset (Fin n)) (hC : C ∈ bottomClasses K) :
    ∀ x y : C, Relation.ReflTransGen (fun a b => 0<restrictedMatrix K C a b) x y := by
  obtain ⟨r,_,hr⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hC).1
  intro x y
  have hx : x.val ∈ component K r := by rw [hr]; exact x.property
  have hy : y.val ∈ component K r := by rw [hr]; exact y.property
  have hxb := (andB_eq_true_iff _ _).mp (Finset.mem_filter.mp hx).2
  have hyb := (andB_eq_true_iff _ _).mp (Finset.mem_filter.mp hy).2
  have hp : RationalReachable K x y :=
    (reachesB_sound K x r hxb.2).trans (reachesB_sound K r y hyb.1)
  obtain ⟨_,hpath⟩ := lift_class_path K C hC x y x.property hp
  exact hpath

def referenceClassCandidate {n : ℕ} (K : RationalMarkovMatrix n)
    (C : Finset (Fin n)) : ClassStationaryCandidate n where
  classStates := C
  weights x := if hx : x ∈ C then referenceWeights (restrictedMatrix K C) ⟨x,hx⟩ else 0

private theorem extended_sum {n : ℕ} (K : RationalMarkovMatrix n)
    (C : Finset (Fin n)) (f : Fin n → ℚ) :
    (∑ x : Fin n, (referenceClassCandidate K C).weights x*f x) =
      ∑ x : C, referenceWeights (restrictedMatrix K C) x*f x := by
  let g := fun x : Fin n => (referenceClassCandidate K C).weights x*f x
  calc
    (∑ x : Fin n, g x) = ∑ x ∈ C, g x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ C)
      intro x _ hx
      simp [g, referenceClassCandidate, hx]
    _ = ∑ x : C, referenceWeights (restrictedMatrix K C) x*f x := by
      rw [← Finset.sum_coe_sort C g]
      apply Finset.sum_congr rfl
      intro x _
      simp [g, referenceClassCandidate, x.property]

theorem referenceClassCandidate_conditions {n : ℕ} [NeZero n]
    (K : RationalMarkovMatrix n) (C : Finset (Fin n)) (hC : C ∈ bottomClasses K) :
    ClassStationaryConditions K (referenceClassCandidate K C) := by
  have hne : C.Nonempty := (Finset.mem_filter.mp hC).2.1
  letI : Nonempty C := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  have hs := restrictedMatrix_stochastic K C hC
  have hp := referenceWeights_probability (restrictedMatrix K C) hs.1 hs.2
    (restrictedMatrix_irreducible K C hC)
  refine ⟨Nat.pos_of_ne_zero (NeZero.ne n), hC, ?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ C
    · simpa [referenceClassCandidate,hx] using hp.1 ⟨x,hx⟩
    · simp [referenceClassCandidate,hx]
  · have hh := extended_sum K C (fun _ => 1)
    simp only [mul_one] at hh
    exact hh.trans hp.2.1
  · intro x hx
    change x ∉ C at hx
    simp [referenceClassCandidate,hx]
  · intro y
    by_cases hy : y ∈ C
    · rw [extended_sum K C (fun x => K.entry x y)]
      simpa [referenceClassCandidate,hy,restrictedMatrix] using hp.2.2 ⟨y,hy⟩
    · have hz (x : Fin n) : (referenceClassCandidate K C).weights x*K.entry x y=0 := by
        by_cases hx : x ∈ C
        · have hxy : K.entry x y=0 := by
            apply le_antisymm _ (K.entry_nonneg x y)
            exact not_lt.mp (fun hp => hy (bottomClasses_closed K C hC x hx y hp))
          rw [hxy,mul_zero]
        · simp [referenceClassCandidate,hx]
      have hw : (referenceClassCandidate K C).weights y=0 := by
        simp [referenceClassCandidate,hy]
      rw [hw]
      exact (Finset.sum_eq_zero (fun x _ => hz x)).symm

theorem referenceClassCandidate_check {n : ℕ} [NeZero n]
    (K : RationalMarkovMatrix n) (C : Finset (Fin n)) (hC : C ∈ bottomClasses K) :
    checkClassStationary K (referenceClassCandidate K C)=true := by
  exact decide_eq_true (referenceClassCandidate_conditions K C hC)

end PermanssonResearch.ReverseSolver.C11
