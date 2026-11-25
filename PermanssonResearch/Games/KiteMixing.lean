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
  have hscore :
      score C (mix q q' t h0 h1) =
        fun k => (1-t)*score C q k + t*score C q' k := by
    funext k
    unfold score
    exact expect_mix q q' t h0 h1 (C k)
  unfold gain
  simp only [hscore, Row.expect_add, Row.expect_mul]
  <;> ring

theorem gain_le_one (C : J → I → ℝ) (p : Row J) (q : Row I)
    (hC : ∀ j i, 0 ≤ C j i ∧ C j i ≤ 1) (j : J) :
    gain C p q j ≤ 1 := by
  have hi : ∀ k, 0 ≤ score C q k := by
    intro k
    simpa [score] using q.expect_mono (f := fun _ => (0:ℝ)) (fun i => (hC k i).1)
  have hj : score C q j ≤ 1 := by
    simpa [score] using q.expect_mono (g := fun _ => (1:ℝ)) (fun i => (hC j i).2)
  have hmean : 0 ≤ p.expect (score C q) := by
    simpa using p.expect_mono (f := fun _ => (0:ℝ)) hi
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
    have heq : gain R (mix p (Row.pure iStar) t ht0 ht1) q i =
        gain R p q i - t*r₁ := by
      unfold gain at hbest ⊢
      rw [expect_mix, Row.expect_pure]
      calc
        _ = score R q i - p.expect (score R q) -
            t*(score R q iStar - p.expect (score R q)) := by ring
        _ = _ := by rw [hbest]
    rw [heq]
    calc
      gain R p q i - t*r₁ ≤ r₁-t*r₁ := sub_le_sub_right (hR i) _
      _ = (1-t)*r₁ := by ring
      _ = s := ht
  · rw [approxBestResponse_iff_pure]
    intro j
    rw [gain_mix_opponent]
    have h := add_le_add
      (mul_le_mul_of_nonneg_left (hC j) (sub_nonneg.mpr ht1))
      (mul_le_mul_of_nonneg_left (gain_le_one C q (Row.pure iStar) hbounded j) ht0)
    apply h.trans
    have hineq : ((1-t)*r₂+t) * r₁ ≤ s*r₁ := by
      have hk' := hk.2.2.1
      calc
        ((1-t)*r₂+t)*r₁ = ((1-t)*r₁)*r₂ + r₁ - (1-t)*r₁ := by ring
        _ = s*r₂+r₁-s := by rw [ht]
        _ ≤ s*r₁ := by nlinarith only [hk']
    calc
      (1-t)*r₂+t*1 = (1-t)*r₂+t := by rw [mul_one]
      _ = (((1-t)*r₂+t)*r₁)/r₁ := by
        field_simp [ne_of_gt hr0] <;> ring
      _ ≤ s := (div_le_iff₀ hr0).2 hineq

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

/-- Exact rational kite domain. Threshold zero is handled by checkNash,
not by a mixing operation. -/
def RationalKite (s r₁ r₂ : ℚ) : Prop :=
  0 < s ∧ s < 1/2 ∧ 0 ≤ r₁ ∧ 0 ≤ r₂ ∧
    (1-s)*r₁+s*r₂ ≤ s ∧ s*r₁+(1-s)*r₂ ≤ s

instance (s r₁ r₂ : ℚ) : Decidable (RationalKite s r₁ r₂) := by
  unfold RationalKite
  infer_instance

/-- Independent finite certificate for the literal rational output.
Branch 0 retains the input, 1 repairs the row, 2 repairs the column.
Exact regret masks are checked separately by checkExactRegret. -/
def KiteConversionChecks [DecidableEq I] [DecidableEq J]
    (R : I → J → ℚ) (C : J → I → ℚ)
    (p p' : I → ℚ) (q q' : J → ℚ) (s r₁ r₂ t : ℚ)
    (iStar : I) (jStar : J) (branch : Fin 3) : Prop :=
  Simplex p ∧ Simplex q ∧
  (∀ i j, 0 ≤ R i j ∧ R i j ≤ 1) ∧
  (∀ j i, 0 ≤ C j i ∧ C j i ≤ 1) ∧
  (∀ i, rationalGain R p q i ≤ r₁) ∧ rationalGain R p q iStar = r₁ ∧
  (∀ j, rationalGain C q p j ≤ r₂) ∧ rationalGain C q p jStar = r₂ ∧
  RationalKite s r₁ r₂ ∧ 0 ≤ t ∧ t ≤ 1 ∧
  (if branch = 0 then
    r₁ ≤ s ∧ r₂ ≤ s ∧ t = 0 ∧ (∀ i, p' i = p i) ∧ (∀ j, q' j = q j)
   else if branch = 1 then
    s < r₁ ∧ t = 1-s/r₁ ∧
      (∀ i, p' i = (1-t)*p i + t*(if i=iStar then 1 else 0)) ∧
      (∀ j, q' j = q j)
   else
    r₁ ≤ s ∧ s < r₂ ∧ t = 1-s/r₂ ∧
      (∀ j, q' j = (1-t)*q j + t*(if j=jStar then 1 else 0)) ∧
      (∀ i, p' i = p i)) ∧
  NashChecks R C p' q' s

instance [DecidableEq I] [DecidableEq J]
    (R : I → J → ℚ) (C : J → I → ℚ)
    (p p' : I → ℚ) (q q' : J → ℚ) (s r₁ r₂ t : ℚ)
    (iStar : I) (jStar : J) (branch : Fin 3) :
    Decidable (KiteConversionChecks R C p p' q q' s r₁ r₂ t iStar jStar branch) := by
  unfold KiteConversionChecks
  infer_instance

def checkKiteConversion [DecidableEq I] [DecidableEq J]
    (R : I → J → ℚ) (C : J → I → ℚ)
    (p p' : I → ℚ) (q q' : J → ℚ) (s r₁ r₂ t : ℚ)
    (iStar : I) (jStar : J) (branch : Fin 3) : Bool :=
  decide (KiteConversionChecks R C p p' q q' s r₁ r₂ t iStar jStar branch)

theorem checked_kite_conversion [DecidableEq I] [DecidableEq J]
    (R : I → J → ℚ) (C : J → I → ℚ)
    (p p' : I → ℚ) (q q' : J → ℚ) (s r₁ r₂ t : ℚ)
    (iStar : I) (jStar : J) (branch : Fin 3)
    (h : checkKiteConversion R C p p' q q' s r₁ r₂ t iStar jStar branch = true) :
    ∃ hp : Simplex p', ∃ hq : Simplex q',
      ApproxNash (fun i j => (R i j : ℝ)) (fun j i => (C j i : ℝ))
        (realRow p' hp) (realRow q' hq) (s : ℝ) := by
  have hc : KiteConversionChecks R C p p' q q' s r₁ r₂ t iStar jStar branch := by
    unfold checkKiteConversion at h
    exact of_decide_eq_true h
  unfold KiteConversionChecks at hc
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hn⟩ := hc
  exact ⟨hn.1, hn.2.1, (rationalChecks_iff_real R C p' q' hn.1 hn.2.1 s).1 hn⟩

end PermanssonResearch.ApproxEquilibrium
