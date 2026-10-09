import PermanssonResearch.ReverseSolver.NonstationaryPrefixKernel
import PermanssonResearch.ReverseSolver.CanonicalHistoryAtoms
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Tactic

/-!
# D1-C1: genuine nonstationary path-atom recurrence and exact product

This adapts D0's genuine partialTraj atom argument to an indexed family
of history kernels. The step at elapsed time i uses the original deadline
T's selected row with T-i transitions remaining, rather than silently
replacing the family with a stationary kernel.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace Nonstationary

open Bellman
open ControlledKernel
open PermanssonLean.ProbabilitySupport

universe uC

/-- A concrete partialTraj pair-law decomposition for the nonstationary
kernel family; a genuine distributional equality, not a synthetic product. -/
theorem prefix_transition_pair {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (D : ℕ) (x : Fin n) (t : ℕ) :
    prefixLaw sys π D x t ⊗ₘ historyStep sys π D t =
      (prefixLaw sys π D x (t+1)).map
        (fun (w : (i : Finset.Iic (t+1)) → Fin n) =>
          (Preorder.frestrictLe₂ (π := fun _ : ℕ => Fin n) t.le_succ w,
           w ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩)) := by
  let κ : (k : ℕ) → Kernel ((i : Finset.Iic k) → Fin n) (Fin n) :=
    fun k => historyStep sys π D k
  let x₀ := singletonPrefix x
  have hpair := Kernel.partialTraj_compProd_eq_map_traj
    (X := fun _ : ℕ => Fin n) (κ := κ)
    (a := 0) (b := t) (Nat.zero_le t) (x₀ := x₀)
  have hprefix := congrArg
    (fun Q : Kernel ((i : Finset.Iic 0) → Fin n)
      ((i : Finset.Iic (t+1)) → Fin n) => Q x₀)
    (Kernel.traj_map_frestrictLe (X := fun _ : ℕ => Fin n)
      (κ := κ) 0 (t+1))
  rw [Kernel.map_apply _ (by fun_prop)] at hprefix
  calc
    prefixLaw sys π D x t ⊗ₘ historyStep sys π D t =
        (Kernel.traj κ 0 x₀).map
          (fun w : ℕ → Fin n => (Preorder.frestrictLe t w, w (t+1))) := by
            simpa [prefixLaw, κ, x₀] using hpair
    _ = (prefixLaw sys π D x (t+1)).map
          (fun (w : (i : Finset.Iic (t+1)) → Fin n) =>
            (Preorder.frestrictLe₂ (π := fun _ : ℕ => Fin n) t.le_succ w,
             w ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩)) := by
            change (Kernel.traj κ 0 x₀).map
                (fun w : ℕ → Fin n => (Preorder.frestrictLe t w, w (t+1))) =
              (Kernel.partialTraj (X := fun _ : ℕ => Fin n)
                  κ 0 (t+1) x₀).map
                (fun (w : (i : Finset.Iic (t+1)) → Fin n) =>
                  (Preorder.frestrictLe₂ (π := fun _ : ℕ => Fin n) t.le_succ w,
                   w ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩))
            rw [← hprefix]
            have hl : Measurable
                (Preorder.frestrictLe₂ (π := fun _ : ℕ => Fin n) t.le_succ) :=
              Preorder.measurable_frestrictLe₂ t.le_succ
            have hr : Measurable
                (fun w : ((i : Finset.Iic (t+1)) → Fin n) =>
                  w ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩) :=
              measurable_pi_apply _
            have hm : Measurable
                (fun (w : (i : Finset.Iic (t+1)) → Fin n) =>
                  (Preorder.frestrictLe₂ (π := fun _ : ℕ => Fin n) t.le_succ w,
                    w ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩)) :=
              hl.prodMk hr
            rw [Measure.map_map hm (Preorder.measurable_frestrictLe (t+1))]
            rfl

private def prefixPair {n : ℕ} (t : ℕ) :
    ((i : Finset.Iic (t+1)) → Fin n) →
      (((i : Finset.Iic t) → Fin n) × Fin n) :=
  fun w => (Preorder.frestrictLe₂ (π := fun _ : ℕ => Fin n) t.le_succ w,
    w ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩)

private theorem prefixPair_injective {n : ℕ} (t : ℕ) :
    Function.Injective (prefixPair (n := n) t) := by
  intro w v h
  have hp := congrArg Prod.fst h
  have hl := congrArg Prod.snd h
  funext i
  by_cases hi : (i : ℕ) ≤ t
  · have hpoint := congrFun hp ⟨(i : ℕ), Finset.mem_Iic.mpr hi⟩
    simpa [prefixPair, Preorder.frestrictLe₂] using hpoint
  · have hibound : (i : ℕ) ≤ t+1 := Finset.mem_Iic.mp i.property
    have hieq : (i : ℕ) = t+1 := by omega
    have heq : i = ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩ := Subtype.ext hieq
    simpa [prefixPair, heq] using hl

/-- Exact atom mass recurrence, on the ACTUAL nonstationary mathlib
trajectory measure. -/
theorem prefix_singleton_succ {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (D : ℕ) (x : Fin n) (t : ℕ)
    (w : (i : Finset.Iic (t+1)) → Fin n) :
    prefixLaw sys π D x (t+1) {w} =
      prefixLaw sys π D x t
        {Preorder.frestrictLe₂ (π := fun _ : ℕ => Fin n) t.le_succ w} *
      ENNReal.ofReal
        ((selectedMatrix sys π D t).entry
          (w ⟨t, Finset.mem_Iic.mpr t.le_succ⟩)
          (w ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩) : ℝ) := by
  classical
  let pre := Preorder.frestrictLe₂ (π := fun _ : ℕ => Fin n) t.le_succ w
  let z := w ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩
  let μ := prefixLaw sys π D x t
  let ν := prefixLaw sys π D x (t+1)
  let κ := historyStep sys π D t
  have hpair := congrArg
    (fun ρ : Measure (((i : Finset.Iic t) → Fin n) × Fin n) =>
      ρ {(pre,z)}) (prefix_transition_pair sys π D x t)
  change (μ ⊗ₘ κ) {(pre,z)} =
    (ν.map (prefixPair t)) {(pre,z)} at hpair
  have hpre : prefixPair (n := n) t ⁻¹' {(pre,z)} = {w} := by
    ext u
    change prefixPair t u = prefixPair t w ↔ u = w
    exact (prefixPair_injective t).eq_iff
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (pre,z)),
    hpre] at hpair
  have hprod : ({pre} ×ˢ {z} : Set (((i : Finset.Iic t) → Fin n) × Fin n)) =
      {(pre,z)} := by
    ext p
    rcases p with ⟨a,b⟩
    simp
  rw [← hprod, Measure.compProd_apply_prod
    (measurableSet_singleton pre) (measurableSet_singleton z)] at hpair
  rw [lintegral_singleton' (Kernel.measurable_coe κ
    (measurableSet_singleton z)) pre] at hpair
  have hstep : κ pre {z} =
      ENNReal.ofReal ((selectedMatrix sys π D t).entry
        (w ⟨t, Finset.mem_Iic.mpr t.le_succ⟩)
        (w ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩) : ℝ) := by
    change selectedKernel sys π D t
      (w ⟨t, Finset.mem_Iic.mpr t.le_succ⟩) {z} = _
    exact rationalFiniteKernel_singleton (selectedMatrix sys π D t) _ _
  change ν {w} = μ {pre} * _
  rw [← hstep, mul_comm]
  exact hpair.symm

/-- Chronological exact rational transition product. -/
def rationalPathWeight {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (D t : ℕ) (w : (i : Finset.Iic t) → Fin n) : ℚ :=
  ∏ i : Fin t, (selectedMatrix sys π D i).entry
    (w ⟨i.val, Finset.mem_Iic.mpr (Nat.le_of_lt i.isLt)⟩)
    (w ⟨i.val+1, Finset.mem_Iic.mpr (Nat.succ_le_of_lt i.isLt)⟩)

theorem rationalPathWeight_nonneg {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (D t : ℕ) (w : (i : Finset.Iic t) → Fin n) :
    0 ≤ rationalPathWeight sys π D t w := by
  unfold rationalPathWeight
  exact Finset.prod_nonneg (fun i _ =>
    (selectedMatrix sys π D i).entry_nonneg _ _)

theorem rationalPathWeight_succ {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (D t : ℕ) (w : (i : Finset.Iic (t+1)) → Fin n) :
    rationalPathWeight sys π D (t+1) w =
      rationalPathWeight sys π D t
        (Preorder.frestrictLe₂ (π := fun _ : ℕ => Fin n) t.le_succ w) *
      (selectedMatrix sys π D t).entry
        (w ⟨t, Finset.mem_Iic.mpr t.le_succ⟩)
        (w ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩) := by
  classical
  unfold rationalPathWeight
  rw [Fin.prod_univ_castSucc]
  congr 1

/-- Every rational product embeds into ENNReal exactly, using certified
row nonnegativity. -/
theorem rationalPathWeight_ofReal_prod {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (D t : ℕ) (w : (i : Finset.Iic t) → Fin n) :
    (∏ i : Fin t,
      ENNReal.ofReal ((selectedMatrix sys π D i).entry
        (w ⟨i.val, Finset.mem_Iic.mpr (Nat.le_of_lt i.isLt)⟩)
        (w ⟨i.val+1, Finset.mem_Iic.mpr
          (Nat.succ_le_of_lt i.isLt)⟩) : ℝ)) =
      ENNReal.ofReal ((rationalPathWeight sys π D t w : ℚ) : ℝ) := by
  classical
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin t)),
      0 ≤ ((selectedMatrix sys π D i).entry
        (w ⟨i.val, Finset.mem_Iic.mpr (Nat.le_of_lt i.isLt)⟩)
        (w ⟨i.val+1, Finset.mem_Iic.mpr
          (Nat.succ_le_of_lt i.isLt)⟩) : ℝ) := by
    intro i _
    exact_mod_cast (selectedMatrix sys π D i).entry_nonneg _ _
  have hprod := ENNReal.ofReal_prod_of_nonneg hnonneg
  unfold rationalPathWeight
  rw [← hprod]
  congr 1
  norm_cast

/-- Genuine all-horizon atomic probability equals exact rational
chronological-product mass, and wrong initial states have mass zero. -/
theorem prefix_atom_product {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (D : ℕ) (x : Fin n) :
    ∀ (t : ℕ) (w : (i : Finset.Iic t) → Fin n),
      prefixLaw sys π D x t {w} =
        if w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le t)⟩ = x then
          ENNReal.ofReal ((rationalPathWeight sys π D t w : ℚ) : ℝ)
        else 0 := by
  intro t
  induction t with
  | zero =>
      intro w
      rw [prefixLaw_zero]
      rw [Measure.dirac_apply' _ (measurableSet_singleton w)]
      by_cases hx : w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 0)⟩ = x
      · have hw : w = singletonPrefix x := by
          funext i
          have hi : i = ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 0)⟩ := by
            apply Subtype.ext
            exact Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.property)
          rw [hi]
          simpa [singletonPrefix] using hx
        simp [rationalPathWeight, hx, hw, singletonPrefix]
      · have hw : singletonPrefix x ≠ w := by
          intro hh
          apply hx
          have hh0 := congrFun hh ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 0)⟩
          simpa [singletonPrefix] using hh0.symm
        simp [rationalPathWeight, hx, hw]
  | succ t ih =>
      intro w
      rw [prefix_singleton_succ sys π D x t w]
      rw [ih (Preorder.frestrictLe₂ (π := fun _ : ℕ => Fin n) t.le_succ w)]
      rw [rationalPathWeight_succ]
      have hzero :
          (Preorder.frestrictLe₂ (π := fun _ : ℕ => Fin n)
            t.le_succ w)
              ⟨0, Finset.mem_Iic.mpr (Nat.zero_le t)⟩ =
          w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le (t+1))⟩ := rfl
      rw [hzero]
      by_cases hx :
          w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le (t+1))⟩ = x
      · simp only [if_pos hx]
        have hmass : 0 ≤ ((rationalPathWeight sys π D t
            (Preorder.frestrictLe₂ (π := fun _ : ℕ => Fin n) t.le_succ w) : ℚ) : ℝ) := by
          exact_mod_cast rationalPathWeight_nonneg sys π D t
            (Preorder.frestrictLe₂ (π := fun _ : ℕ => Fin n) t.le_succ w)
        rw [← ENNReal.ofReal_mul hmass]
        norm_cast
      · simp only [if_neg hx, zero_mul]

end Nonstationary
end ReverseSolver
end PermanssonResearch
