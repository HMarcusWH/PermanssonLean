import PermanssonResearch.MultipleLimit.TypedAbsorbingKernel
import PermanssonResearch.MultipleLimit.TypedInitialMixture
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Tactic

/-!
# Lane C1 — absorbing continuation in the actual alpha/P/U path law

A fixed-point transition row guarantees the next state agrees with an
absorbing state almost surely, conditional on being there at time n.
All time indices are combined by a countable intersection, rather than
mistaking pointwise kernel equality for an identity on every conceivable
infinite path.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit
namespace TypedAbsorbingContinuation

open TypedStrategicWitness TypedAbsorbingKernel
open PermanssonLean

attribute [local instance] StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

/-- One absorbing state cannot be left at a specified canonical time.
The proof uses the genuine canonical transition-pair measure. -/
theorem step_exit_null (μ : ProbabilityMeasure Y) (z : Y)
    (hz : model.inducedKernel z = Measure.dirac z) (n : ℕ) :
    model.pathLaw μ.toMeasure
      {w : ℕ → Y | w n = z ∧ w (n+1) ≠ z} = 0 := by
  let P := model.pathLaw μ.toMeasure
  let K := model.inducedKernel
  let C : Set ((i : Finset.Iic n) → Y) :=
    {h | h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ = z}
  let D : Set Y := {z}ᶜ
  have hC : MeasurableSet C :=
    (measurableSet_singleton z).preimage (measurable_pi_apply _)
  have hD : MeasurableSet D := (measurableSet_singleton z).compl
  have hpair := StrategicWorldModel.pathLaw_has_transition_pair
    model μ.toMeasure n
  have hpairEvent :
      P {w : ℕ → Y | w n = z ∧ w (n+1) ≠ z} =
      ((P.map (Preorder.frestrictLe n)) ⊗ₘ
        StrategicWorldModel.stationaryHistoryKernel K n)
          (C ×ˢ D) := by
    have h := congrArg
      (fun ρ : Measure (((i : Finset.Iic n) → Y) × Y) => ρ (C ×ˢ D))
      hpair
    have hpre :
        (fun w : ℕ → Y => (Preorder.frestrictLe n w, w (n+1))) ⁻¹'
          (C ×ˢ D) =
        {w : ℕ → Y | w n = z ∧ w (n+1) ≠ z} := by
      ext w
      simp [C, D, Preorder.frestrictLe]
    rw [Measure.map_apply (by fun_prop) (hC.prod hD), hpre] at h
    exact h.symm
  rw [hpairEvent, Measure.compProd_apply_prod hC hD]
  apply setLIntegral_eq_zero hC
  intro h hh
  have hlast : h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ = z := hh
  change K (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) D = 0
  rw [hlast, hz]
  simp [D]

/-- The one-step transition of a canonical trajectory is correct on a
probability-one set for each of the two absorbing states. -/
theorem next_state_fixed_ae (μ : ProbabilityMeasure Y) (n : ℕ) :
    ∀ᵐ w ∂model.pathLaw μ.toMeasure,
      ∀ z : Y, z ∈ ({a,b} : Finset Y) →
        w n = z → w (n+1) = z := by
  have hA : ∀ᵐ w ∂model.pathLaw μ.toMeasure,
      w n = a → w (n+1) = a := by
    rw [ae_iff]
    have hh :
        {w : ℕ → Y | ¬ (w n = a → w (n+1) = a)} =
        {w : ℕ → Y | w n = a ∧ w (n+1) ≠ a} := by
      ext w; simp
    rw [hh]
    exact step_exit_null μ a typed_a_fixed n
  have hB : ∀ᵐ w ∂model.pathLaw μ.toMeasure,
      w n = b → w (n+1) = b := by
    rw [ae_iff]
    have hh :
        {w : ℕ → Y | ¬ (w n = b → w (n+1) = b)} =
        {w : ℕ → Y | w n = b ∧ w (n+1) ≠ b} := by
      ext w; simp
    rw [hh]
    exact step_exit_null μ b typed_b_fixed n
  filter_upwards [hA, hB] with w hwA hwB
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact hwA
  · exact hwB

/-- On a single probability-one event, every absorbing-state visit is
permanent, for every time index. -/
theorem stays_after_absorbing_ae (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂model.pathLaw μ.toMeasure,
      ∀ t : ℕ, w t ∈ ({a,b} : Finset Y) →
        ∀ n : ℕ, t ≤ n → w n = w t := by
  have hsteps : ∀ᵐ w ∂model.pathLaw μ.toMeasure,
      ∀ n : ℕ, ∀ z : Y, z ∈ ({a,b} : Finset Y) →
        w n = z → w (n+1) = z :=
    ae_all_iff.mpr (fun n => next_state_fixed_ae μ n)
  filter_upwards [hsteps] with w hw
  intro t ht n htn
  induction n, htn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      have hz := hw n (w t) ht ih
      simpa [ih] using hz

end
end TypedAbsorbingContinuation
end MultipleLimit
end PermanssonResearch
