import PermanssonResearch.Probability.DependentHistoryCommonMass
import PermanssonResearch.Probability.CylinderTotalVariation
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Basic

/-! Q-DISCOUNT whole-product-law event TV from actual retained common
mass. Literal prefix marginals identify the original infinite laws with
their dependent history evolutions. Summable defects give a genuine
infinite product; a fixed positive recurring leak gives only budget one. -/

open MeasureTheory ProbabilityTheory Filter Finset Set
open scoped Topology ENNReal ProbabilityTheory
namespace PermanssonResearch.Probability.FullPathProduct
open PermanssonLean.ProbabilitySupport DependentHistory
set_option autoImplicit false

theorem retained_antitone (η : ℕ → ℝ) (hη0 : ∀ n, 0 ≤ η n)
    (hη1 : ∀ n, η n ≤ 1) : Antitone (retained η) := by
  apply antitone_nat_of_succ_le
  intro n
  change (∏ t ∈ range (n+1), (1-η t)) ≤ retained η n
  rw [prod_range_succ]
  change retained η n*(1-η n) ≤ retained η n
  exact mul_le_of_le_one_right (retained_nonneg η hη1 n) (by linarith [hη0 n])

theorem retained_multipliable (η : ℕ → ℝ) (hsum : Summable η) :
    Multipliable (fun n => 1-η n) := by
  simpa only [sub_eq_add_neg] using Real.multipliable_one_add_of_summable hsum.neg

theorem retained_tendsto (η : ℕ → ℝ) (hsum : Summable η) :
    Tendsto (retained η) atTop (𝓝 (∏' n, (1-η n))) :=
  (retained_multipliable η hsum).tendsto_prod_tprod_nat

theorem tprod_le_retained (η : ℕ → ℝ) (hη0 : ∀ n, 0 ≤ η n)
    (hη1 : ∀ n, η n ≤ 1) (hsum : Summable η) (n : ℕ) :
    (∏' t, (1-η t)) ≤ retained η n := by
  apply le_of_tendsto (retained_tendsto η hsum)
  filter_upwards [eventually_ge_atTop n] with m hm
  exact retained_antitone η hη0 hη1 hm

theorem tprod_bounds (η : ℕ → ℝ) (hη0 : ∀ n, 0 ≤ η n)
    (hη1 : ∀ n, η n ≤ 1) (hsum : Summable η) :
    0 ≤ (∏' t, (1-η t)) ∧ (∏' t, (1-η t)) ≤ 1 := by
  constructor
  · exact ge_of_tendsto' (retained_tendsto η hsum) (retained_nonneg η hη1)
  · exact le_of_tendsto' (retained_tendsto η hsum) (retained_le_one η hη0 hη1)

universe u
abbrev History (X : ℕ → Type u) (n : ℕ) := (i : Finset.Iic n) → X i

theorem path_tv_le_product {X : ℕ → Type u} [∀ n, MeasurableSpace (X n)]
    (P Q : Measure (∀ n, X n)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (μ ν ξ : Measure (History X 0)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K L R : ∀ n, Kernel (History X n) (History X (n+1)))
    [∀ n, IsMarkovKernel (K n)] [∀ n, IsMarkovKernel (L n)]
    [∀ n, IsFiniteKernel (R n)]
    (hP : ∀ n, P.map (Finset.Iic n).restrict = evolution μ K n)
    (hQ : ∀ n, Q.map (Finset.Iic n).restrict = evolution ν L n)
    (hξμ : ξ ≤ μ) (hξν : ξ ≤ ν)
    (hRK : ∀ n, R n ≤ K n) (hRL : ∀ n, R n ≤ L n)
    (η : ℕ → ℝ) (hη0 : ∀ n, 0 ≤ η n) (hη1 : ∀ n, η n ≤ 1)
    (hsum : Summable η)
    (hmass : ∀ n h, ENNReal.ofReal (1-η n) ≤ R n h univ)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hξmass : ENNReal.ofReal (1-ε) ≤ ξ univ) :
    eventTotalVariation P Q ≤ 1-(1-ε)*(∏' t, (1-η t)) := by
  apply path_eventTotalVariation_le_of_prefixes P Q
  intro n
  rw [hP n,hQ n]
  apply (prefix_tv_le_product μ ν ξ K L R hξμ hξν hRK hRL
    η hη1 hmass hε1 hξmass n).trans
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left
    (tprod_le_retained η hη0 hη1 hsum n) (sub_nonneg.mpr hε1)) 1

theorem zero_defect_product : (∏' _n : ℕ, (1-(0 : ℝ))) = 1 := by simp

theorem unit_defect_product (η : ℕ → ℝ) {n : ℕ} (hn : η n = 1) :
    (∏' t, (1-η t)) = 0 :=
  tprod_of_exists_eq_zero ⟨n,by rw [hn,sub_self]⟩

theorem constant_retained (η : ℝ) (n : ℕ) :
    retained (fun _ => η) n = (1-η)^n := by simp [retained]

theorem recurring_leak_retained_tendsto_zero {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) :
    Tendsto (retained (fun _ => η)) atTop (𝓝 0) := by
  change Tendsto (fun n => retained (fun _ => η) n) atTop (𝓝 0)
  simp_rw [constant_retained]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hη1) (by linarith)

theorem recurring_leak_budget_tendsto_one {η ε : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) :
    Tendsto (fun n => 1-(1-ε)*retained (fun _ => η) n) atTop (𝓝 1) := by
  simpa only [mul_zero,sub_zero] using
    tendsto_const_nhds.sub ((recurring_leak_retained_tendsto_zero hη0 hη1).const_mul (1-ε))

end PermanssonResearch.Probability.FullPathProduct
