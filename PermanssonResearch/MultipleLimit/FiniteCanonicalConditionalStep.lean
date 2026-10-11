import PermanssonResearch.MultipleLimit.CanonicalKernelMarginals
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Tactic

/-!
# Lane C2 — genuine canonical Markov conditional step identity

For ANY measurable finite past-prefix event B and next-state event D,
the real infinite Markov path law assigns the joint event probability
given by integration of K(last_state,D) over B's actual prefix law.

This is the exact conditional-mean identity from Ionescu–Tulcea.
It does NOT identify different time steps as independent, and does
NOT yet assert a martingale strong law. It supplies the required
canonical filtering input for constructing the centered residual
martingale in the subsequent C2 occupation proof.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteCanonicalConditionalStep

open FiniteCanonicalPath
open CanonicalKernelMarginals

variable {Y : Type*} [MeasurableSpace Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- For the actual Markov law P on INFINITE paths, conditioning
next-state membership in D on an arbitrary measurable prefix
event B is represented by the ORIGINAL transition kernel K.
This is an exact event probability identity. -/
theorem canonical_joint_next_event
    (μ : ProbabilityMeasure Y)
    (n : ℕ)
    (B : Set ((i : Finset.Iic n) → Y))
    (hB : MeasurableSet B)
    (D : Set Y) (hD : MeasurableSet D) :
    (canonicalPathLaw K μ.toMeasure)
      {w : ℕ → Y |
        Preorder.frestrictLe n w ∈ B ∧ w (n+1) ∈ D} =
      ∫⁻ h in B,
        K (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) D
        ∂((canonicalPathLaw K μ.toMeasure).map
          (Preorder.frestrictLe n)) := by
  let P := canonicalPathLaw K μ.toMeasure
  let pairFn : (ℕ → Y) → (((i : Finset.Iic n) → Y) × Y) :=
    fun w => (Preorder.frestrictLe n w, w (n+1))
  have hpairMeas : Measurable pairFn := by fun_prop
  have hpreevent :
      pairFn ⁻¹' (B ×ˢ D) =
        {w : ℕ → Y |
          Preorder.frestrictLe n w ∈ B ∧ w (n+1) ∈ D} := by
    ext w
    simp [pairFn]
  calc
    P {w : ℕ → Y |
        Preorder.frestrictLe n w ∈ B ∧ w (n+1) ∈ D} =
      (P.map pairFn) (B ×ˢ D) := by
        rw [Measure.map_apply hpairMeas (hB.prod hD), hpreevent]
    _ = ((P.map (Preorder.frestrictLe n)) ⊗ₘ
          PermanssonLean.ProbabilitySupport.stationaryPrefixKernel K n)
          (B ×ˢ D) := by
        rw [canonical_transition_pair K μ.toMeasure n]
    _ = ∫⁻ h in B,
          K (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) D
          ∂(P.map (Preorder.frestrictLe n)) := by
        rw [Measure.compProd_apply_prod hB hD]
        rfl

/-- At an exact next state z, this identifies the genuine
conditional probability atom, for ALL measurable history events. -/
theorem canonical_joint_next_singleton
    [MeasurableSingletonClass Y]
    (μ : ProbabilityMeasure Y) (n : ℕ)
    (B : Set ((i : Finset.Iic n) → Y))
    (hB : MeasurableSet B)
    (z : Y) :
    (canonicalPathLaw K μ.toMeasure)
      {w : ℕ → Y |
        Preorder.frestrictLe n w ∈ B ∧ w (n+1) = z} =
      ∫⁻ h in B,
        K (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) ({z} : Set Y)
        ∂((canonicalPathLaw K μ.toMeasure).map
          (Preorder.frestrictLe n)) := by
  simpa only [Set.mem_singleton_iff] using
    canonical_joint_next_event K μ n B hB {z}
      (measurableSet_singleton z)

end FiniteCanonicalConditionalStep
end MultipleLimit
end PermanssonResearch
