import PermanssonResearch.ReverseSolver.C11ReferenceClasses

/-!
# Total exact rational stationary-family constructor

Classes are enumerated by scanning physical states in increasing Fin order,
deduplicating the computed components and retaining precisely the bottom
classes. Each candidate uses the specified column-replacement determinant
formula on the actual restricted class matrix.
-/

namespace PermanssonResearch.ReverseSolver.C11

open C10

def canonicalBottomClassList {n : ℕ} (K : RationalMarkovMatrix n) :
    List (Finset (Fin n)) :=
  (((List.finRange n).map (component K)).dedup).filter
    (fun C => decide (C ∈ bottomClasses K))

theorem canonicalBottomClassList_mem {n : ℕ} (K : RationalMarkovMatrix n)
    (C : Finset (Fin n)) : C ∈ canonicalBottomClassList K ↔ C ∈ bottomClasses K := by
  constructor
  · intro hc
    exact of_decide_eq_true (List.mem_filter.mp hc).2
  · intro hc
    apply List.mem_filter.mpr
    refine ⟨List.mem_dedup.mpr ?_, by simpa using hc⟩
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hc).1
    exact List.mem_map.mpr ⟨r, by simp, hr⟩

theorem canonicalBottomClassList_nodup {n : ℕ} (K : RationalMarkovMatrix n) :
    (canonicalBottomClassList K).Nodup := by
  apply List.Nodup.filter
  exact List.nodup_dedup _

theorem canonicalBottomClassList_toFinset {n : ℕ} (K : RationalMarkovMatrix n) :
    (canonicalBottomClassList K).toFinset=bottomClasses K := by
  ext C
  simpa using canonicalBottomClassList_mem K C

def referenceStationaryFamily {n : ℕ} (K : RationalMarkovMatrix n) :
    List (ClassStationaryCandidate n) :=
  (canonicalBottomClassList K).map (referenceClassCandidate K)

theorem referenceStationaryFamily_keys {n : ℕ} (K : RationalMarkovMatrix n) :
    classKeys (referenceStationaryFamily K)=canonicalBottomClassList K := by
  simp [classKeys,referenceStationaryFamily,referenceClassCandidate,List.map_map,
    Function.comp_def]

/-- The genuine checker accepts the complete Cramer-constructed family for
every nonempty finite rational stochastic matrix, with no certificate premise. -/
theorem referenceStationaryFamily_check {n : ℕ} [NeZero n] (K : RationalMarkovMatrix n) :
    checkStationaryFamily K (referenceStationaryFamily K)=true := by
  simp only [checkStationaryFamily, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, referenceStationaryFamily_keys]
  refine ⟨⟨⟨Nat.pos_of_ne_zero (NeZero.ne n), canonicalBottomClassList_nodup K⟩,
    canonicalBottomClassList_toFinset K⟩, ?_⟩
  intro r hr
  obtain ⟨C,hC,rfl⟩ := List.mem_map.mp hr
  exact referenceClassCandidate_check K C ((canonicalBottomClassList_mem K C).mp hC)

end PermanssonResearch.ReverseSolver.C11
