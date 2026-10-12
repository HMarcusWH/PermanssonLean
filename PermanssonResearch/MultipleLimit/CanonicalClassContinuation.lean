import PermanssonResearch.MultipleLimit.CanonicalClassEntry
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Tactic

/-!
# Lane C2 — almost-sure continuation inside any graph-closed class

A Markov state whose one-step kernel assigns full mass to a closed
finite set C cannot EXIT C at a fixed step except on a probability-zero
canonical event. Countable intersection over the true time indices
then proves permanent class residence after any visit, a.s., for every
initial law. This does not claim every imaginable path obeys closure.

Together with the independently proved recurrent-union hitting theorem,
this supports genuine eventual residence in an *individual* closed
communicating class. The measurable class selector is a later module.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit
namespace CanonicalClassContinuation

open KernelCommunication
open FiniteClassClosure
open FiniteCanonicalPath
open CanonicalKernelMarginals

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- At any specified genuine canonical time n, the event of departing
a graph-closed class C on the next transition has measure ZERO. -/
theorem closed_step_exit_null
    (μ : ProbabilityMeasure Y)
    (C : Set Y) (hC : ClosedSubset K C) (n : ℕ) :
    canonicalPathLaw K μ.toMeasure
      {w : ℕ → Y | w n ∈ C ∧ w (n+1) ∉ C} = 0 := by
  let P := canonicalPathLaw K μ.toMeasure
  let D : Set Y := Cᶜ
  let B : Set ((i : Finset.Iic n) → Y) :=
    {h | h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ C}
  have hCmeas : MeasurableSet C := (Set.toFinite C).measurableSet
  have hB : MeasurableSet B :=
    hCmeas.preimage (measurable_pi_apply _)
  have hD : MeasurableSet D := hCmeas.compl
  have hpair := canonical_transition_pair K μ.toMeasure n
  have hpairEvent :
      P {w : ℕ → Y | w n ∈ C ∧ w (n+1) ∉ C} =
      ((P.map (Preorder.frestrictLe n)) ⊗ₘ
        PermanssonLean.ProbabilitySupport.stationaryPrefixKernel K n)
          (B ×ˢ D) := by
    have h := congrArg
      (fun ρ : Measure (((i : Finset.Iic n) → Y) × Y) => ρ (B ×ˢ D))
      hpair
    have hpre :
        (fun w : ℕ → Y => (Preorder.frestrictLe n w, w (n+1))) ⁻¹'
          (B ×ˢ D) =
        {w : ℕ → Y | w n ∈ C ∧ w (n+1) ∉ C} := by
      ext w
      simp [B, D, Preorder.frestrictLe]
    rw [Measure.map_apply (by fun_prop) (hB.prod hD), hpre] at h
    exact h.symm
  rw [hpairEvent, Measure.compProd_apply_prod hB hD]
  apply setLIntegral_eq_zero hB
  intro h hh
  change K (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) D = 0
  rw [show D = Cᶜ from rfl, prob_compl_eq_one_sub hCmeas,
    closedSubset_kernel_mass_one K C hC _ hh]
  simp

/-- A genuine canonical trajectory satisfies every one-step closure
implication on a joint probability-one event across ALL time indices. -/
theorem closed_step_stay_ae
    (μ : ProbabilityMeasure Y)
    (C : Set Y) (hC : ClosedSubset K C) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      ∀ t : ℕ, w t ∈ C → w (t+1) ∈ C := by
  apply ae_all_iff.mpr
  intro t
  rw [ae_iff]
  have hset :
      {w : ℕ → Y | ¬(w t ∈ C → w (t+1) ∈ C)} =
      {w : ℕ → Y | w t ∈ C ∧ w (t+1) ∉ C} := by
    ext w
    simp
  rw [hset]
  exact closed_step_exit_null K μ C hC t

/-- Graph-closed residence is a.s. *permanent* after any random time
of entry, even though the underlying event is defined pointwise for
all infinite paths. The countable intersection is essential. -/
theorem closed_stay_after_entry_ae
    (μ : ProbabilityMeasure Y)
    (C : Set Y) (hC : ClosedSubset K C) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      ∀ t : ℕ, w t ∈ C →
        ∀ n : ℕ, t ≤ n → w n ∈ C := by
  filter_upwards [closed_step_stay_ae K μ C hC] with w hstep
  intro t ht n htn
  induction n, htn using Nat.le_induction with
  | base => exact ht
  | succ n hle ih => exact hstep n ih

end CanonicalClassContinuation
end MultipleLimit
end PermanssonResearch
