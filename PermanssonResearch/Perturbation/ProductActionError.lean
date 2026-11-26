import PermanssonResearch.Games.BimatrixRegret
import PermanssonLean.Probability.FinitePrefixTV
import Mathlib.Tactic

/-! Finite independent product rows: common mass multiplies. This is the
finite probability-row TV convention (one minus sum of common atoms).
It is not a bound for arbitrary correlated joint actions. -/
namespace PermanssonResearch.ApproxEquilibrium

open ActionTrace MeasureTheory ProbabilityTheory
open PermanssonLean.ProbabilitySupport
open scoped BigOperators ENNReal
set_option autoImplicit false
variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def overlap (p q : Row I) : ℝ := ∑ i, min (p.mass i) (q.mass i)

noncomputable def rowTV (p q : Row I) : ℝ := 1-overlap p q

theorem overlap_nonneg (p q : Row I) : 0 ≤ overlap p q := by
  unfold overlap
  exact Finset.sum_nonneg fun i _ => le_min (p.nonneg i) (q.nonneg i)

theorem overlap_le_one (p q : Row I) : overlap p q ≤ 1 := by
  unfold overlap
  rw [← p.total]
  exact Finset.sum_le_sum fun i _ => min_le_left _ _

noncomputable def productRow (p : Row I) (q : Row J) : Row (I × J) where
  mass a := p.mass a.1*q.mass a.2
  nonneg a := mul_nonneg (p.nonneg a.1) (q.nonneg a.2)
  total := by
    simp [Fintype.sum_prod_type, ← Finset.mul_sum, q.total, p.total]

theorem rowTV_nonneg (p q : Row I) : 0 ≤ rowTV p q :=
  sub_nonneg.mpr (overlap_le_one p q)

theorem rowTV_le_one (p q : Row I) : rowTV p q ≤ 1 :=
  sub_le_self _ (overlap_nonneg p q)

theorem rowTV_half_l1 (p q : Row I) :
    rowTV p q = (∑ i, |p.mass i-q.mass i|)/2 := by
  have h : (∑ i, |p.mass i-q.mass i|) =
      ∑ i, (p.mass i+q.mass i-2*min (p.mass i) (q.mass i)) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : p.mass i ≤ q.mass i
    · rw [min_eq_left hi, abs_of_nonpos (sub_nonpos.mpr hi)]
      ring
    · have hj := le_of_lt (lt_of_not_ge hi)
      rw [min_eq_right hj, abs_of_nonneg (sub_nonneg.mpr hj)]
      ring
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    p.total, q.total] at h
  unfold rowTV overlap
  linarith

theorem overlap_product_ge (p p' : Row I) (q q' : Row J) :
    overlap p p' * overlap q q' ≤ overlap (productRow p q) (productRow p' q') := by
  unfold overlap
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  change min (p.mass i) (p'.mass i) * min (q.mass j) (q'.mass j) ≤
    min (p.mass i*q.mass j) (p'.mass i*q'.mass j)
  have h := le_min (q.nonneg j) (q'.nonneg j)
  have h' := le_min (p.nonneg i) (p'.nonneg i)
  exact le_min
    (mul_le_mul (min_le_left _ _) (min_le_left _ _) h (p.nonneg i))
    (mul_le_mul (min_le_right _ _) (min_le_right _ _) h (p'.nonneg i))

theorem product_rowTV_le (p p' : Row I) (q q' : Row J) :
    rowTV (productRow p q) (productRow p' q') ≤
      1-(1-rowTV p p')*(1-rowTV q q') := by
  unfold rowTV
  have h := overlap_product_ge p p' q q'
  simpa only [sub_sub_cancel] using sub_le_sub_left h 1

section Measures

variable [MeasurableSpace I] [MeasurableSpace J]
  [MeasurableSingletonClass I] [MeasurableSingletonClass J]

noncomputable def commonRowMeasure (p q : Row I) : Measure I :=
  ∑ i, ENNReal.ofReal (min (p.mass i) (q.mass i)) • Measure.dirac i

theorem commonRowMeasure_le_left (p q : Row I) : commonRowMeasure p q ≤ p.measure := by
  classical
  apply Measure.le_iff.2
  intro s hs
  simp only [commonRowMeasure, Row.measure, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_le_sum
  intro i _
  have hm : ENNReal.ofReal (min (p.mass i) (q.mass i)) ≤
      ENNReal.ofReal (p.mass i) :=
    ENNReal.ofReal_le_ofReal (min_le_left _ _)
  have hd : (0 : ℝ≥0∞) ≤ Measure.dirac i s := bot_le
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hm hd

theorem commonRowMeasure_le_right (p q : Row I) : commonRowMeasure p q ≤ q.measure := by
  classical
  apply Measure.le_iff.2
  intro s hs
  simp only [commonRowMeasure, Row.measure, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_le_sum
  intro i _
  have hm : ENNReal.ofReal (min (p.mass i) (q.mass i)) ≤
      ENNReal.ofReal (q.mass i) :=
    ENNReal.ofReal_le_ofReal (min_le_right _ _)
  have hd : (0 : ℝ≥0∞) ≤ Measure.dirac i s := bot_le
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hm hd

theorem commonRowMeasure_mass (p q : Row I) :
    (commonRowMeasure p q).real Set.univ = overlap p q := by
  classical
  simp only [Measure.real, commonRowMeasure, Measure.finsetSum_apply,
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => le_min (p.nonneg i) (q.nonneg i))]
  exact ENNReal.toReal_ofReal (overlap_nonneg p q)

theorem eventTV_le_rowTV (p q : Row I) :
    eventTotalVariation p.measure q.measure ≤ rowTV p q := by
  letI : IsFiniteMeasure (commonRowMeasure p q) :=
    ⟨lt_of_le_of_lt (commonRowMeasure_le_left p q Set.univ) (by simp)⟩
  have h := eventTotalVariation_le_one_sub_commonMass
    (commonRowMeasure_le_left p q) (commonRowMeasure_le_right p q)
  rwa [commonRowMeasure_mass] at h

/-- The positive-difference event attains the finite common-mass bound.
Thus the executable half-L1 convention is the original event-TV exactly. -/
theorem eventTV_eq_rowTV (p q : Row I) :
    eventTotalVariation p.measure q.measure = rowTV p q := by
  classical
  let E : Set I := {i | q.mass i ≤ p.mass i}
  have hE : MeasurableSet E := (Set.toFinite E).measurableSet
  have hreal (r : Row I) :
      r.measure.real E = ∑ i, if q.mass i ≤ p.mass i then r.mass i else 0 := by
    rw [← integral_indicator_one (μ := r.measure) hE, ← Row.expect_eq_integral]
    simp [Row.expect, Set.indicator, E, mul_ite]
  have hdiff : p.measure.real E - q.measure.real E = rowTV p q := by
    rw [hreal, hreal, ← Finset.sum_sub_distrib]
    have heq : (∑ i, ((if q.mass i ≤ p.mass i then p.mass i else 0) -
        (if q.mass i ≤ p.mass i then q.mass i else 0))) =
        ∑ i, (p.mass i-min (p.mass i) (q.mass i)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : q.mass i ≤ p.mass i
      · simp [hi, min_eq_right hi]
      · simp [hi, min_eq_left (le_of_lt (lt_of_not_ge hi))]
    rw [heq, Finset.sum_sub_distrib, p.total]
    rfl
  apply le_antisymm (eventTV_le_rowTV p q)
  have h := abs_measureReal_sub_le_eventTotalVariation p.measure q.measure hE
  rw [hdiff, abs_of_nonneg (rowTV_nonneg p q)] at h
  exact h

theorem productRow_measure (p : Row I) (q : Row J) :
    (productRow p q).measure = p.measure.prod q.measure := by
  classical
  apply Measure.ext_of_singleton
  rintro ⟨i,j⟩
  rw [Row.measure_singleton, ← Set.singleton_prod_singleton, Measure.prod_prod,
    Row.measure_singleton, Row.measure_singleton,
    ← ENNReal.ofReal_mul (p.nonneg i)]
  rfl

theorem product_measure_tv_le (p p' : Row I) (q q' : Row J) :
    eventTotalVariation (p.measure.prod q.measure) (p'.measure.prod q'.measure) ≤
      1-(1-rowTV p p')*(1-rowTV q q') := by
  rw [← productRow_measure, ← productRow_measure]
  exact (eventTV_le_rowTV _ _).trans (product_rowTV_le p p' q q')

/-- Literal product-row identities on ALL source states convert marginal
bounds to the original uniform action-kernel bound. No statement is made
about correlated kernels which do not satisfy the identities. -/
theorem uniform_product_action_tv {Y : Type*} [MeasurableSpace Y]
    (K L : Kernel Y (I × J)) (p p' : Y → Row I) (q q' : Y → Row J)
    (hK : ∀ y, K y = (p y).measure.prod (q y).measure)
    (hL : ∀ y, L y = (p' y).measure.prod (q' y).measure)
    (δ : ℝ)
    (hδ : ∀ y, 1-(1-rowTV (p y) (p' y))*(1-rowTV (q y) (q' y)) ≤ δ) :
    HasUniformEventTVBound K L δ := by
  intro y
  rw [hK y, hL y]
  exact (product_measure_tv_le _ _ _ _).trans (hδ y)

end Measures

/-- Relocate only strictly suboptimal actions, leaving all other mass alone. -/
noncomputable def redirect (v : I → ℝ) (iStar i : I) : I := by
  classical
  exact if v i < v iStar then iStar else i

noncomputable def projectBest (p : Row I) (v : I → ℝ) (iStar : I) : Row I :=
  p.map (redirect v iStar)

theorem projectBest_nonbest_zero (p : Row I) (v : I → ℝ) (iStar j : I)
    (hj : v j < v iStar) :
    (projectBest p v iStar).mass j = 0 := by
  classical
  change (∑ i, if redirect v iStar i = j then p.mass i else 0) = 0
  apply Finset.sum_eq_zero
  intro i _
  have hne : redirect v iStar i ≠ j := by
    intro h
    unfold redirect at h
    split_ifs at h with hi
    · subst j
      exact (lt_irrefl _) hj
    · subst j
      exact hi hj
  simp [hne]

theorem projectBest_good_mass (p : Row I) (v : I → ℝ) (iStar j : I)
    (hj : ¬ v j < v iStar) :
    p.mass j ≤ (projectBest p v iStar).mass j := by
  classical
  change p.mass j ≤ ∑ i, if redirect v iStar i = j then p.mass i else 0
  have h := Finset.single_le_sum
    (f := fun i : I => if redirect v iStar i = j then p.mass i else 0)
    (fun i _ => by
      split_ifs
      · exact p.nonneg i
      · exact le_rfl)
    (Finset.mem_univ j)
  simpa [redirect, hj] using h

theorem projectBest_tv_le (p : Row I) (v : I → ℝ) (iStar : I) :
    rowTV p (projectBest p v iStar) ≤
      p.expect (fun i => if v i < v iStar then 1 else 0) := by
  classical
  have h : p.expect (fun i => 1 - (if v i < v iStar then 1 else 0)) ≤
      overlap p (projectBest p v iStar) := by
    unfold Row.expect overlap
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : v i < v iStar
    · simpa [hi] using le_min (p.nonneg i) ((projectBest p v iStar).nonneg i)
    · simp only [hi, if_false, sub_zero, mul_one]
      exact le_min le_rfl (projectBest_good_mass p v iStar i hi)
  rw [Row.expect_sub, Row.expect_const] at h
  unfold rowTV
  linarith

theorem projectBest_attains (p : Row I) (v : I → ℝ) (iStar : I)
    (hmax : ∀ i, v i ≤ v iStar) :
    (projectBest p v iStar).expect v = v iStar := by
  classical
  unfold projectBest
  rw [Row.expect_map]
  have h : (fun i => v (redirect v iStar i)) = fun _ => v iStar := by
    funext i
    by_cases hi : v i < v iStar
    · simp [redirect, hi]
    · have he := le_antisymm (hmax i) (le_of_not_gt hi)
      simp [redirect, hi, he]
  rw [h, Row.expect_const]

theorem projectBest_tv_eq (p : Row I) (v : I → ℝ) (iStar : I) :
    rowTV p (projectBest p v iStar) =
      p.expect (fun i => if v i < v iStar then 1 else 0) := by
  classical
  have h : overlap p (projectBest p v iStar) =
      p.expect (fun i => 1-(if v i < v iStar then 1 else 0)) := by
    unfold overlap Row.expect
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : v i < v iStar
    · rw [projectBest_nonbest_zero p v iStar i hi, min_eq_right (p.nonneg i)]
      simp [hi]
    · rw [min_eq_left (projectBest_good_mass p v iStar i hi)]
      simp [hi]
  rw [Row.expect_sub, Row.expect_const] at h
  unfold rowTV
  linarith

theorem projectBest_all_tied (p : Row I) (v : I → ℝ) (iStar : I)
    (h : ∀ i, v i = v iStar) :
    ∀ j, (projectBest p v iStar).mass j = p.mass j := by
  classical
  intro j
  change (∑ i, if redirect v iStar i = j then p.mass i else 0) = p.mass j
  have hred (i : I) : redirect v iStar i = i := by simp [redirect, h i]
  simp [hred]

theorem projectBest_gap_bound (p : Row I) (v : I → ℝ) (iStar : I)
    (g ε : ℝ) (hg : 0 < g) (hmax : ∀ i, v i ≤ v iStar)
    (hgap : ∀ i, v i < v iStar → g ≤ v iStar - v i)
    (hregret : v iStar - p.expect v ≤ ε) :
    rowTV p (projectBest p v iStar) ≤ min 1 (ε/g) := by
  apply le_min
  · unfold rowTV
    linarith [overlap_nonneg p (projectBest p v iStar)]
  · exact (projectBest_tv_le p v iStar).trans
      (nonbest_mass_le p v iStar g ε hg hmax hgap hregret)

end PermanssonResearch.ApproxEquilibrium
