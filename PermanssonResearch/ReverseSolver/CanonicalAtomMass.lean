import PermanssonResearch.ReverseSolver.CanonicalTransitionPair
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Tactic

/-!
# D0-C: conditional one-step atomic path masses

Every atom of the canonical prefix law at time T+1 is the mass of
its T-prefix times the *actual* rational one-step transition entry.
This is a universal-in-T relation on the real Ionescu-Tulcea path law,
not a separate synthetic measure.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver

private def prefixPair {n : ℕ} (T : ℕ) :
    ((i : Finset.Iic (T+1)) → Fin n) →
      (((i : Finset.Iic T) → Fin n) × Fin n) :=
  fun w => (Preorder.frestrictLe₂ T.le_succ w,
    w ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩)

private theorem prefixPair_injective {n : ℕ} (T : ℕ) :
    Function.Injective (prefixPair (n := n) T) := by
  intro w v h
  have hp := congrArg Prod.fst h
  have hl := congrArg Prod.snd h
  funext i
  by_cases hi : (i : ℕ) ≤ T
  · have hpoint := congrFun hp ⟨(i : ℕ), Finset.mem_Iic.mpr hi⟩
    simpa [prefixPair, Preorder.frestrictLe₂] using hpoint
  · have hibound : (i : ℕ) ≤ T+1 := Finset.mem_Iic.mp i.property
    have hieq : (i : ℕ) = T+1 := by omega
    have heq : i = ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩ := Subtype.ext hieq
    simpa [prefixPair, heq] using hl

/-- An atom of the canonical T+1-prefix has precisely the previous atom
mass multiplied by the certified rational transition probability. -/
theorem rationalFiniteKernel_prefix_singleton_succ {n : ℕ}
    (M : RationalMarkovMatrix n) (y : Fin n) (T : ℕ)
    (w : (i : Finset.Iic (T+1)) → Fin n) :
    PermanssonLean.ProbabilitySupport.finitePrefixLaw
      (rationalFiniteKernel M) y (T+1) {w} =
    PermanssonLean.ProbabilitySupport.finitePrefixLaw
      (rationalFiniteKernel M) y T
      {Preorder.frestrictLe₂ T.le_succ w} *
    ENNReal.ofReal (M.entry
      (w ⟨T, Finset.mem_Iic.mpr T.le_succ⟩)
      (w ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩) : ℝ) := by
  classical
  let pre := Preorder.frestrictLe₂ T.le_succ w
  let z := w ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩
  let μ := PermanssonLean.ProbabilitySupport.finitePrefixLaw
    (rationalFiniteKernel M) y T
  let ν := PermanssonLean.ProbabilitySupport.finitePrefixLaw
    (rationalFiniteKernel M) y (T+1)
  let κ := PermanssonLean.ProbabilitySupport.stationaryPrefixKernel
    (rationalFiniteKernel M) T
  have hpair := congrArg
    (fun ρ : Measure (((i : Finset.Iic T) → Fin n) × Fin n) =>
      ρ {(pre, z)})
    (rationalFiniteKernel_transition_pair M y T)
  change (μ ⊗ₘ κ) {(pre,z)} =
    (ν.map (prefixPair T)) {(pre,z)} at hpair
  have hpre : prefixPair (n := n) T ⁻¹' {(pre,z)} = {w} := by
    ext u
    change prefixPair T u = prefixPair T w ↔ u = w
    exact (prefixPair_injective T).eq_iff
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (pre,z)),
    hpre] at hpair
  have hprod : ({pre} ×ˢ {z} : Set (((i : Finset.Iic T) → Fin n) × Fin n)) =
      {(pre,z)} := by
    ext p
    rcases p with ⟨a,b⟩
    simp
  rw [← hprod, Measure.compProd_apply_prod
    (measurableSet_singleton pre) (measurableSet_singleton z)] at hpair
  rw [lintegral_singleton' (Kernel.measurable_coe κ
    (measurableSet_singleton z)) pre] at hpair
  have hstep : κ pre {z} =
      ENNReal.ofReal (M.entry
        (w ⟨T, Finset.mem_Iic.mpr T.le_succ⟩)
        (w ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩) : ℝ) := by
    change rationalFiniteKernel M
      (w ⟨T, Finset.mem_Iic.mpr T.le_succ⟩) {z} = _
    exact rationalFiniteKernel_singleton M _ _
  change ν {w} = μ {pre} * _ 
  rw [← hstep, mul_comm]
  exact hpair.symm

end ReverseSolver
end PermanssonResearch
