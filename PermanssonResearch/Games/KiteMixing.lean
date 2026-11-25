import PermanssonResearch.Games.BimatrixRegret

/-! Local best-response mixing lemma, following Cogentic's kite construction.
This does not assert the global MaximinKiteNE termination theorem. -/
namespace PermanssonResearch.ApproxEquilibrium

open ActionTrace
open scoped BigOperators
set_option autoImplicit false

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def mix (p q : Row I) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : Row I where
  mass i := (1-t) * p.mass i + t * q.mass i
  nonneg i := add_nonneg (mul_nonneg (sub_nonneg.mpr h1) (p.nonneg i))
    (mul_nonneg h0 (q.nonneg i))
  total := by
    simp [Finset.sum_add_distrib, ← Finset.mul_sum, p.total, q.total]

theorem expect_mix (p q : Row I) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (v : I → ℝ) :
    (mix p q t h0 h1).expect v = (1-t)*p.expect v + t*q.expect v := by
  simp only [Row.expect, mix, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

theorem gain_mix_opponent (C : J → I → ℝ) (p : Row J) (q q' : Row I)
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (j : J) :
    gain C p (mix q q' t h0 h1) j =
      (1-t)*gain C p q j + t*gain C p q' j := by
  simp only [gain, score, expect_mix, Row.expect_add, Row.expect_mul]
  ring

theorem gain_le_one (C : J → I → ℝ) (p : Row J) (q : Row I)
    (hC : ∀ j i, 0 ≤ C j i ∧ C j i ≤ 1) (j : J) :
    gain C p q j ≤ 1 := by
  have hi : ∀ k, 0 ≤ score C q k := by
    intro k
    simpa [score] using q.expect_mono (fun i => (hC k i).1)
  have hj : score C q j ≤ 1 := by
    simpa [score] using q.expect_mono (fun i => (hC j i).2)
  have hmean : 0 ≤ p.expect (score C q) := by
    simpa using p.expect_mono hi
  unfold gain
  linarith

def InKite (s r₁ r₂ : ℝ) : Prop :=
  0 ≤ r₁ ∧ 0 ≤ r₂ ∧ (1-s)*r₁+s*r₂ ≤ s ∧ s*r₁+(1-s)*r₂ ≤ s

/-- If the row player's regret exceeds s, the row mixing branch suffices.
Swapping the two own-action-first games gives the column branch. -/
theorem kite_repair_row [DecidableEq I] [DecidableEq J]
    (R : I → J → ℝ) (C : J → I → ℝ) (p : Row I) (q : Row J)
    (iStar : I) (s r₁ r₂ : ℝ) (hs : 0 < s) (hr : s < r₁)
    (hk : InKite s r₁ r₂)
    (hR : ∀ i, gain R p q i ≤ r₁)
    (hbest : gain R p q iStar = r₁)
    (hC : ∀ j, gain C q p j ≤ r₂)
    (hbounded : ∀ j i, 0 ≤ C j i ∧ C j i ≤ 1) :
    ∃ (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1),
      t = 1-s/r₁ ∧ ApproxNash R C (mix p (Row.pure iStar) t h0 h1) q s := by
  have hr0 : 0 < r₁ := hs.trans hr
  have hd0 : 0 ≤ s/r₁ := div_nonneg hs.le hr0.le
  have hd1 : s/r₁ ≤ 1 := (div_le_iff₀ hr0).2 (by linarith)
  let t := 1-s/r₁
  have ht0 : 0 ≤ t := sub_nonneg.mpr hd1
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have ht : (1-t)*r₁ = s := by
    dsimp [t]
    field_simp [ne_of_gt hr0] <;> ring
  refine ⟨t, ht0, ht1, rfl, hs.le, ?_, ?_⟩
  · rw [approxBestResponse_iff_pure]
    intro i
    have h := hR i
    unfold gain at hbest h ⊢
    rw [expect_mix, Row.expect_pure]
    nlinarith [ht]
  · rw [approxBestResponse_iff_pure]
    intro j
    rw [gain_mix_opponent]
    have h := add_le_add
      (mul_le_mul_of_nonneg_left (hC j) (sub_nonneg.mpr ht1))
      (mul_le_mul_of_nonneg_left (gain_le_one C q (Row.pure iStar) hbounded j) ht0)
    apply h.trans
    have hineq : ((1-t)*r₂+t) * r₁ ≤ s*r₁ := by
      have hk' := hk.2.2.1
      nlinarith [ht]
    exact le_of_mul_le_mul_right hineq hr0

/-- Entire kite: either the input works or one unilateral mixing branch does.
The returned strategies are real rows; the receipt layer checks rational
specializations. -/
theorem kite_exists [DecidableEq I] [DecidableEq J]
    (R : I → J → ℝ) (C : J → I → ℝ) (p : Row I) (q : Row J)
    (iStar : I) (jStar : J) (s r₁ r₂ : ℝ) (hs : 0 < s)
    (hk : InKite s r₁ r₂)
    (hR : ∀ i, gain R p q i ≤ r₁) (hRi : gain R p q iStar = r₁)
    (hC : ∀ j, gain C q p j ≤ r₂) (hCj : gain C q p jStar = r₂)
    (hRb : ∀ i j, 0 ≤ R i j ∧ R i j ≤ 1)
    (hCb : ∀ j i, 0 ≤ C j i ∧ C j i ≤ 1) :
    ∃ p' : Row I, ∃ q' : Row J, ApproxNash R C p' q' s := by
  by_cases h1 : r₁ ≤ s
  · by_cases h2 : r₂ ≤ s
    · refine ⟨p, q, hs.le, ?_, ?_⟩
      · rw [approxBestResponse_iff_pure]
        exact fun i => (hR i).trans h1
      · rw [approxBestResponse_iff_pure]
        exact fun j => (hC j).trans h2
    · have hk' : InKite s r₂ r₁ := by
        rcases hk with ⟨ha,hb,hc,hd⟩
        refine ⟨hb,ha,?_,?_⟩ <;> linarith
      obtain ⟨t, ht0, ht1, _, h⟩ :=
        kite_repair_row C R q p jStar s r₂ r₁ hs (lt_of_not_ge h2)
          hk' hC hCj hR hRb
      exact ⟨p, mix q (Row.pure jStar) t ht0 ht1, h.1, h.2.2, h.2.1⟩
  · obtain ⟨t, ht0, ht1, _, h⟩ :=
      kite_repair_row R C p q iStar s r₁ r₂ hs (lt_of_not_ge h1)
        hk hR hRi hC hCb
    exact ⟨mix p (Row.pure iStar) t ht0 ht1, q, h⟩

end PermanssonResearch.ApproxEquilibrium
