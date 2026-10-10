import PermanssonResearch.ReverseSolver.HistoryTypedPrefix
import PermanssonResearch.ReverseSolver.HistoryPathAtoms
import Mathlib.Tactic

/-!
# D1-C2: exact typed history-conditioned typed trajectory atom recurrence

The underlying law is the real alpha/P/U induced-kernel partialTraj,
composed at each chronological step for a fixed original deadline.
This proof adapts the generic D0/D1-C1 transition-pair decomposition to
the actual typed joint-state space, without treating it as one frozen
intervention.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace HistoryDependentTyped

open Bellman
open ControlledKernel
open FiniteStrategicRealization
open FiniteStrategicPathBridge
open PermanssonLean
open PermanssonLean.ProbabilitySupport

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov
universe uC

/-- A concrete partialTraj pair-law decomposition for the history-dependent
kernel family; a genuine distributional equality, not a synthetic product. -/
theorem typed_prefix_transition_pair {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D : ℕ) (x : Fin n) (t : ℕ) :
    typedPrefixLaw sys σ D x t ⊗ₘ typedHistoryStep sys σ D t =
      (typedPrefixLaw sys σ D x (t+1)).map
        (fun (w : (i : Finset.Iic (t+1)) → JointState Unit (Fin n)) =>
          (Preorder.frestrictLe₂ (π := fun _ : ℕ => JointState Unit (Fin n)) t.le_succ w,
           w ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩)) := by
  let κ : (k : ℕ) → Kernel ((i : Finset.Iic k) → JointState Unit (Fin n)) (JointState Unit (Fin n)) :=
    fun k => typedHistoryStep sys σ D k
  let x₀ := singletonPrefix (decode x)
  have hpair := Kernel.partialTraj_compProd_eq_map_traj
    (X := fun _ : ℕ => JointState Unit (Fin n)) (κ := κ)
    (a := 0) (b := t) (Nat.zero_le t) (x₀ := x₀)
  have hprefix := congrArg
    (fun Q : Kernel ((i : Finset.Iic 0) → JointState Unit (Fin n))
      ((i : Finset.Iic (t+1)) → JointState Unit (Fin n)) => Q x₀)
    (Kernel.traj_map_frestrictLe (X := fun _ : ℕ => JointState Unit (Fin n))
      (κ := κ) 0 (t+1))
  rw [Kernel.map_apply _ (by fun_prop)] at hprefix
  calc
    typedPrefixLaw sys σ D x t ⊗ₘ typedHistoryStep sys σ D t =
        (Kernel.traj κ 0 x₀).map
          (fun w : ℕ → JointState Unit (Fin n) => (Preorder.frestrictLe t w, w (t+1))) := by
            simpa [typedPrefixLaw, κ, x₀] using hpair
    _ = (typedPrefixLaw sys σ D x (t+1)).map
          (fun (w : (i : Finset.Iic (t+1)) → JointState Unit (Fin n)) =>
            (Preorder.frestrictLe₂ (π := fun _ : ℕ => JointState Unit (Fin n)) t.le_succ w,
             w ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩)) := by
            change (Kernel.traj κ 0 x₀).map
                (fun w : ℕ → JointState Unit (Fin n) => (Preorder.frestrictLe t w, w (t+1))) =
              (Kernel.partialTraj (X := fun _ : ℕ => JointState Unit (Fin n))
                  κ 0 (t+1) x₀).map
                (fun (w : (i : Finset.Iic (t+1)) → JointState Unit (Fin n)) =>
                  (Preorder.frestrictLe₂ (π := fun _ : ℕ => JointState Unit (Fin n)) t.le_succ w,
                   w ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩))
            rw [← hprefix]
            have hl : Measurable
                (Preorder.frestrictLe₂ (π := fun _ : ℕ => JointState Unit (Fin n)) t.le_succ) :=
              Preorder.measurable_frestrictLe₂ t.le_succ
            have hr : Measurable
                (fun w : ((i : Finset.Iic (t+1)) → JointState Unit (Fin n)) =>
                  w ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩) :=
              measurable_pi_apply _
            have hm : Measurable
                (fun (w : (i : Finset.Iic (t+1)) → JointState Unit (Fin n)) =>
                  (Preorder.frestrictLe₂ (π := fun _ : ℕ => JointState Unit (Fin n)) t.le_succ w,
                    w ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩)) :=
              hl.prodMk hr
            rw [Measure.map_map hm (Preorder.measurable_frestrictLe (t+1))]
            rfl

private def prefixPair {n : ℕ} (t : ℕ) :
    ((i : Finset.Iic (t+1)) → JointState Unit (Fin n)) →
      (((i : Finset.Iic t) → JointState Unit (Fin n)) × JointState Unit (Fin n)) :=
  fun w => (Preorder.frestrictLe₂ (π := fun _ : ℕ => JointState Unit (Fin n)) t.le_succ w,
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

/-- Exact atom mass recurrence, on the ACTUAL history-dependent mathlib
trajectory measure. -/
theorem typed_prefix_singleton_succ {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D : ℕ) (x : Fin n) (t : ℕ)
    (w : (i : Finset.Iic (t+1)) → JointState Unit (Fin n)) :
    typedPrefixLaw sys σ D x (t+1) {w} =
      typedPrefixLaw sys σ D x t
        {Preorder.frestrictLe₂ (π := fun _ : ℕ => JointState Unit (Fin n)) t.le_succ w} *
      typedHistoryStep sys σ D t
        (Preorder.frestrictLe₂ (π := fun _ : ℕ => JointState Unit (Fin n))
          t.le_succ w)
        {w ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩} := by
  classical
  let pre := Preorder.frestrictLe₂ (π := fun _ : ℕ => JointState Unit (Fin n)) t.le_succ w
  let z := w ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩
  let μ := typedPrefixLaw sys σ D x t
  let ν := typedPrefixLaw sys σ D x (t+1)
  let κ := typedHistoryStep sys σ D t
  have hpair := congrArg
    (fun ρ : Measure (((i : Finset.Iic t) → JointState Unit (Fin n)) × JointState Unit (Fin n)) =>
      ρ {(pre,z)}) (typed_prefix_transition_pair sys σ D x t)
  change (μ ⊗ₘ κ) {(pre,z)} =
    (ν.map (prefixPair t)) {(pre,z)} at hpair
  have hpre : prefixPair (n := n) t ⁻¹' {(pre,z)} = {w} := by
    ext u
    change prefixPair t u = prefixPair t w ↔ u = w
    exact (prefixPair_injective t).eq_iff
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (pre,z)),
    hpre] at hpair
  have hprod : ({pre} ×ˢ {z} : Set (((i : Finset.Iic t) → JointState Unit (Fin n)) × JointState Unit (Fin n))) =
      {(pre,z)} := by
    ext p
    rcases p with ⟨a,b⟩
    simp
  rw [← hprod, Measure.compProd_apply_prod
    (measurableSet_singleton pre) (measurableSet_singleton z)] at hpair
  rw [lintegral_singleton' (Kernel.measurable_coe κ
    (measurableSet_singleton z)) pre] at hpair
  change ν {w} = μ {pre} * κ pre {z}
  rw [mul_comm]
  exact hpair.symm


end HistoryDependentTyped
end ReverseSolver
end PermanssonResearch
