import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-! B-LOCAL-ORDER: minimality needs strict lower-set lifting, without global
injectivity or positivity monotonicity. -/

namespace PermanssonResearch.GrammarRobust

/-- Minimal positive element in the admitted poset. Admission belongs in the
carrier (for example the subtype of allowed blocks). -/
def IsMinimalPositive {P : Type*} [Preorder P] (positive : P → Prop) (a : P) : Prop :=
  positive a ∧ ∀ b, b < a → ¬ positive b

/-- Local strict order preservation and coverage of the entire strict lower set
are sufficient and necessary for the stated transport proof. -/
theorem minimalPositive_iff_of_lowerSet_lifting
    {P Q : Type*} [Preorder P] [Preorder Q]
    (f : P → Q) (p : P → Prop) (q : Q → Prop) (a : P)
    (hmatch : ∀ b, b ≤ a → (p b ↔ q (f b)))
    (hstrict : ∀ b, b < a → f b < f a)
    (hcover : ∀ c, c < f a → ∃ b, b < a ∧ f b = c) :
    IsMinimalPositive p a ↔ IsMinimalPositive q (f a) := by
  constructor
  · rintro ⟨ha, hmin⟩
    refine ⟨(hmatch a le_rfl).mp ha, ?_⟩
    intro c hc hqc
    obtain ⟨b, hb, hfb⟩ := hcover c hc
    exact hmin b hb ((hmatch b (le_of_lt hb)).mpr (hfb ▸ hqc))
  · rintro ⟨ha, hmin⟩
    refine ⟨(hmatch a le_rfl).mpr ha, ?_⟩
    intro b hb hpb
    exact hmin (f b) (hstrict b hb) ((hmatch b (le_of_lt hb)).mp hpb)

/-- A finite meet-closed positive family has a least element. The conclusion
does not hold from existence of a positive block alone. -/
theorem exists_least_positive_of_finite_meet_closed
    {P : Type*} [SemilatticeInf P]
    (s : Finset P) (hne : s.Nonempty)
    (hclosed : ∀ a ∈ s, ∀ b ∈ s, a ⊓ b ∈ s) :
    ∃ a ∈ s, ∀ b ∈ s, a ≤ b := by
  classical
  have aux : ∀ t : Finset P, t ⊆ s → t.Nonempty →
      ∃ a ∈ s, ∀ b ∈ t, a ≤ b := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert a t ha ih =>
      intro hsub _
      have has : a ∈ s := hsub (by simp)
      by_cases ht : t.Nonempty
      · obtain ⟨m, hm, hleast⟩ := ih (fun b hb => hsub (by simp [hb])) ht
        refine ⟨a ⊓ m, hclosed a has m hm, ?_⟩
        intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact inf_le_left
        · exact inf_le_right.trans (hleast b hb)
      · have hempty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
        subst t
        exact ⟨a, has, by simp⟩
  exact aux s (Finset.Subset.refl s) hne

end PermanssonResearch.GrammarRobust
