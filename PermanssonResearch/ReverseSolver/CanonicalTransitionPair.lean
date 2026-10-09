import PermanssonResearch.ReverseSolver.CanonicalProjectivity
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Tactic

/-!
# D0-C: finite-horizon transition-pair factorization

The actual `finitePrefixLaw` (not an independently invented path measure)
admits the expected transition pair law. It provides the measurable
disintegration needed to transport finite path weights and success events.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver

/-- Every finite-prefix extension is precisely the prior prefix together
with one step of the certified rational Markov kernel, in the *canonical*
mathlib Ionescu-Tulcea construction. -/
theorem rationalFiniteKernel_transition_pair {n : ℕ}
    (M : RationalMarkovMatrix n) (y : Fin n) (T : ℕ) :
    (PermanssonLean.ProbabilitySupport.finitePrefixLaw
        (rationalFiniteKernel M) y T) ⊗ₘ
      (PermanssonLean.ProbabilitySupport.stationaryPrefixKernel
        (rationalFiniteKernel M) T) =
    (PermanssonLean.ProbabilitySupport.finitePrefixLaw
        (rationalFiniteKernel M) y (T+1)).map
      (fun w =>
        (Preorder.frestrictLe₂ T.le_succ w,
         w ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩)) := by
  let κ : (k : ℕ) → Kernel ((i : Finset.Iic k) → Fin n) (Fin n) :=
    fun k => PermanssonLean.ProbabilitySupport.stationaryPrefixKernel
      (rationalFiniteKernel M) k
  let x₀ := PermanssonLean.ProbabilitySupport.singletonPrefix y
  have hpair := Kernel.partialTraj_compProd_eq_map_traj
    (X := fun _ : ℕ => Fin n) (κ := κ)
    (a := 0) (b := T) (Nat.zero_le T) (x₀ := x₀)
  have hprefix := congrArg
    (fun K : Kernel ((i : Finset.Iic 0) → Fin n)
      ((i : Finset.Iic (T+1)) → Fin n) => K x₀)
    (Kernel.traj_map_frestrictLe (X := fun _ : ℕ => Fin n)
      (κ := κ) 0 (T+1))
  rw [Kernel.map_apply _ (by fun_prop)] at hprefix
  calc
    (PermanssonLean.ProbabilitySupport.finitePrefixLaw
        (rationalFiniteKernel M) y T) ⊗ₘ
      (PermanssonLean.ProbabilitySupport.stationaryPrefixKernel
        (rationalFiniteKernel M) T) =
      (Kernel.traj κ 0 x₀).map
        (fun w : ℕ → Fin n => (Preorder.frestrictLe T w, w (T+1))) := by
          simpa [PermanssonLean.ProbabilitySupport.finitePrefixLaw,
            κ, x₀] using hpair
    _ = (PermanssonLean.ProbabilitySupport.finitePrefixLaw
        (rationalFiniteKernel M) y (T+1)).map
      (fun w => (Preorder.frestrictLe₂ T.le_succ w,
          w ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩)) := by
          rw [← hprefix]
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rfl

end ReverseSolver
end PermanssonResearch
