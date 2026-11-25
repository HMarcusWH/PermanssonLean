import PermanssonResearch.Games.BimatrixRegret
import Mathlib.Tactic

/-! Finite independent product rows: common mass multiplies. This is the
finite probability-row TV convention (one minus sum of common atoms).
It is not a bound for arbitrary correlated joint actions. -/
namespace PermanssonResearch.ApproxEquilibrium

open ActionTrace
open scoped BigOperators
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

end PermanssonResearch.ApproxEquilibrium
