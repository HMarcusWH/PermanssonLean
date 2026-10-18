import PermanssonResearch.ReverseSolver.InfiniteSafetyBellman

/-! A finite, rational descending computation of the greatest controlled
invariant subset, with its exact characterization by the infinite value one. -/

namespace PermanssonResearch.ReverseSolver.InfiniteSafety
open ControlledKernel
variable {C : Type*} [DecidableEq C] {n : ℕ}

def rowMass (sys : FiniteControlSystem C n) (c : C) (y : Fin n)
    (S : Finset (Fin n)) : ℚ := ∑ z ∈ S, (sys.matrix c).entry y z

def stays (sys : FiniteControlSystem C n) (c : C) (y : Fin n)
    (S : Finset (Fin n)) : Prop := ∀ z : Fin n, 0<(sys.matrix c).entry y z → z ∈ S

instance (sys : FiniteControlSystem C n) (c : C) (y : Fin n) (S : Finset (Fin n)) :
    Decidable (stays sys c y S) := by unfold stays; infer_instance

theorem stays_iff_rowMass_one (sys : FiniteControlSystem C n) (c : C) (y : Fin n)
    (S : Finset (Fin n)) : stays sys c y S ↔ rowMass sys c y S=1 := by
  have hid : (∑ z : Fin n, if z ∈ S then (sys.matrix c).entry y z else 0)=rowMass sys c y S := by
    simp [rowMass,Finset.sum_ite_mem]
  constructor
  · intro hs
    rw [← hid,← (sys.matrix c).row_sum_one y]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : z ∈ S
    · simp [hz]
    · have hp : (sys.matrix c).entry y z=0 := le_antisymm
        (le_of_not_gt (fun h => hz (hs z h))) ((sys.matrix c).entry_nonneg y z)
      simp [hz,hp]
  · intro hm z hz
    have hdiff : (∑ w : Fin n, if w ∈ S then 0 else (sys.matrix c).entry y w)=0 := by
      have ht : (∑ w : Fin n, ((if w ∈ S then (sys.matrix c).entry y w else 0)+
          (if w ∈ S then 0 else (sys.matrix c).entry y w)))=1 := by
        simpa only [ite_add_ite,add_zero,zero_add,ite_self] using (sys.matrix c).row_sum_one y
      rw [Finset.sum_add_distrib,hid,hm] at ht
      linarith
    have he := (Finset.sum_eq_zero_iff_of_nonneg (fun w (_ : w ∈ Finset.univ) => by
      split <;> first | exact le_rfl | exact (sys.matrix c).entry_nonneg y w)).mp hdiff z (Finset.mem_univ z)
    by_contra hn
    simp only [if_neg hn] at he
    exact (ne_of_gt hz) he

def controlledInvariant (sys : FiniteControlSystem C n) (S : Finset (Fin n)) : Prop :=
  ∀ y ∈ S, ∃ c ∈ sys.options y, stays sys c y S

def prune (sys : FiniteControlSystem C n) (S : Finset (Fin n)) : Finset (Fin n) :=
  S.filter (fun y => ∃ c ∈ sys.options y, stays sys c y S)

theorem mem_prune_mass (sys : FiniteControlSystem C n) (S : Finset (Fin n)) (y : Fin n) :
    y ∈ prune sys S ↔ y ∈ S ∧ ∃ c ∈ sys.options y, rowMass sys c y S=1 := by
  simp only [prune,Finset.mem_filter,stays_iff_rowMass_one]

def invariantIterates (sys : FiniteControlSystem C n) (G : Finset (Fin n)) :
    ℕ → Finset (Fin n)
  | 0 => G
  | k+1 => prune sys (invariantIterates sys G k)

theorem invariantIterates_succ_subset (sys : FiniteControlSystem C n)
    (G : Finset (Fin n)) (k : ℕ) :
    invariantIterates sys G (k+1) ⊆ invariantIterates sys G k := Finset.filter_subset _ _

theorem invariantIterates_antitone (sys : FiniteControlSystem C n) (G : Finset (Fin n)) :
    Antitone (invariantIterates sys G) := antitone_nat_of_succ_le (invariantIterates_succ_subset sys G)

theorem invariantIterates_plateau (sys : FiniteControlSystem C n) (G : Finset (Fin n))
    (k : ℕ) (hk : invariantIterates sys G (k+1)=invariantIterates sys G k) :
    ∀ m, invariantIterates sys G (k+m)=invariantIterates sys G k := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.add_succ,invariantIterates,ih]
      exact hk

/-- At most |G| strict removals; this is an explicit finite stopping bound. -/
theorem invariantIterates_stable (sys : FiniteControlSystem C n) (G : Finset (Fin n)) :
    invariantIterates sys G (G.card+1)=invariantIterates sys G G.card := by
  by_contra hn
  have hne : ∀ k≤G.card, invariantIterates sys G (k+1)≠invariantIterates sys G k := by
    intro k hk he
    obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hk
    have hp := invariantIterates_plateau sys G k he
    apply hn
    rw [hm,show k+m+1=k+(m+1) by omega,hp (m+1),hp m]
  have hc : ∀ k≤G.card+1, (invariantIterates sys G k).card+k≤G.card := by
    intro k
    induction k with
    | zero => intro _; simp [invariantIterates]
    | succ k ih =>
        intro hk
        have hi := ih (by omega)
        have ht : (invariantIterates sys G (k+1)).card < (invariantIterates sys G k).card :=
          Finset.card_lt_card ⟨invariantIterates_succ_subset sys G k,
            fun he => hne k (by omega) (Finset.Subset.antisymm
              (invariantIterates_succ_subset sys G k) he)⟩
        omega
  have := hc (G.card+1) le_rfl
  omega

def invariantCore (sys : FiniteControlSystem C n) (G : Finset (Fin n)) : Finset (Fin n) :=
  invariantIterates sys G G.card

theorem invariantCore_subset (sys : FiniteControlSystem C n) (G : Finset (Fin n)) :
    invariantCore sys G ⊆ G := invariantIterates_antitone sys G (Nat.zero_le _)

theorem invariantCore_invariant (sys : FiniteControlSystem C n) (G : Finset (Fin n)) :
    controlledInvariant sys (invariantCore sys G) := by
  intro y hy
  have hp : y ∈ prune sys (invariantCore sys G) := by
    change y ∈ invariantIterates sys G (G.card+1)
    rw [invariantIterates_stable]
    exact hy
  exact (Finset.mem_filter.mp hp).2

theorem controlledInvariant_subset_iterates (sys : FiniteControlSystem C n)
    (G S : Finset (Fin n)) (hSG : S ⊆ G) (hS : controlledInvariant sys S) :
    ∀ k, S ⊆ invariantIterates sys G k := by
  intro k
  induction k with
  | zero => exact hSG
  | succ k ih =>
      intro y hy
      obtain ⟨c,hc,hs⟩ := hS y hy
      exact Finset.mem_filter.mpr ⟨ih hy,c,hc,fun z hz => ih (hs z hz)⟩

theorem invariantCore_greatest (sys : FiniteControlSystem C n) (G S : Finset (Fin n))
    (hSG : S ⊆ G) (hS : controlledInvariant sys S) : S ⊆ invariantCore sys G :=
  controlledInvariant_subset_iterates sys G S hSG hS G.card

noncomputable section

theorem invariant_horizonValue_one (sys : FiniteControlSystem C n) (G S : Finset (Fin n))
    (hSG : S ⊆ G) (hS : controlledInvariant sys S) (k : ℕ) :
    ∀ y ∈ S, horizonValue sys G k y=1 := by
  induction k with
  | zero => intro y hy; simp [horizonValue,hSG hy]
  | succ k ih =>
      intro y hy
      apply le_antisymm (horizonValue_bounds sys G (k+1) y).2
      obtain ⟨c,hc,hs⟩ := hS y hy
      have hr : rowScore sys (horizonValue sys G k) y c=1 := by
        rw [← rowScore_one sys y c]
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : 0<(sys.matrix c).entry y z
        · rw [ih z (hs z hz)]
        · have he : (sys.matrix c).entry y z=0 := le_antisymm (le_of_not_gt hz)
            ((sys.matrix c).entry_nonneg y z)
          simp [he]
      rw [horizonValue,step,if_pos (hSG hy),← hr]
      exact rowScore_le_maximum sys _ y c hc

theorem invariant_limitValue_one (sys : FiniteControlSystem C n) (G S : Finset (Fin n))
    (hSG : S ⊆ G) (hS : controlledInvariant sys S) (y : Fin n) (hy : y ∈ S) :
    limitValue sys G y=1 := by
  unfold limitValue
  simp_rw [invariant_horizonValue_one sys G S hSG hS _ y hy]
  simp

def valueOneSet (sys : FiniteControlSystem C n) (G : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun y => limitValue sys G y=1)

@[simp] theorem mem_valueOneSet (sys : FiniteControlSystem C n) (G : Finset (Fin n)) (y : Fin n) :
    y ∈ valueOneSet sys G ↔ limitValue sys G y=1 := by
  classical
  simp [valueOneSet]

theorem valueOneSet_subset (sys : FiniteControlSystem C n) (G : Finset (Fin n)) :
    valueOneSet sys G ⊆ G := by
  intro y hy
  by_contra hn
  have h1 := (mem_valueOneSet sys G y).mp hy
  rw [limitValue_eq_zero_outside sys G y hn] at h1
  norm_num at h1

theorem valueOneSet_invariant (sys : FiniteControlSystem C n) (G : Finset (Fin n)) :
    controlledInvariant sys (valueOneSet sys G) := by
  intro y hy
  refine ⟨(stationaryPolicy sys G).choose y,(stationaryPolicy sys G).permitted y,?_⟩
  intro z hz
  apply (mem_valueOneSet sys G z).mpr
  let c := (stationaryPolicy sys G).choose y
  have hr : rowScore sys (limitValue sys G) y c=1 := by
    rw [← stationaryChoice_fixed_point sys G y (valueOneSet_subset sys G hy)]
    exact (mem_valueOneSet sys G y).mp hy
  have ht : (∑ w : Fin n, ((sys.matrix c).entry y w : ℝ)*(1-limitValue sys G w))=0 := by
    simp only [mul_sub,Finset.sum_sub_distrib,mul_one]
    change (∑ w : Fin n, ((sys.matrix c).entry y w : ℝ))-rowScore sys (limitValue sys G) y c=0
    have hrow : (∑ w : Fin n, ((sys.matrix c).entry y w : ℝ))=1 := by
      exact_mod_cast (sys.matrix c).row_sum_one y
    rw [hrow,hr,sub_self]
  have he := (Finset.sum_eq_zero_iff_of_nonneg (fun w (_ : w ∈ Finset.univ) =>
    mul_nonneg (by exact_mod_cast (sys.matrix c).entry_nonneg y w)
      (sub_nonneg.mpr (limitValue_bounds sys G w).2))).mp ht z (Finset.mem_univ z)
  have hp : (0 : ℝ)<(sys.matrix c).entry y z := by exact_mod_cast hz
  have hzv := (mul_eq_zero.mp he).resolve_left (ne_of_gt hp)
  linarith

/-- Exact probability-one region, computed by the rational finite iteration. -/
theorem invariantCore_eq_valueOneSet (sys : FiniteControlSystem C n) (G : Finset (Fin n)) :
    invariantCore sys G=valueOneSet sys G := by
  apply Finset.Subset.antisymm
  · intro y hy
    apply (mem_valueOneSet sys G y).mpr
    exact invariant_limitValue_one sys G (invariantCore sys G)
      (invariantCore_subset sys G) (invariantCore_invariant sys G) y hy
  · exact invariantCore_greatest sys G (valueOneSet sys G)
      (valueOneSet_subset sys G) (valueOneSet_invariant sys G)

end
end PermanssonResearch.ReverseSolver.InfiniteSafety
