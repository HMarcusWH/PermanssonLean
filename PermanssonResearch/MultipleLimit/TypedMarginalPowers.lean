import PermanssonResearch.MultipleLimit.TypedInitialMixture
import PermanssonLean.Regime.ExitTime
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic

/-!
# Lane C1 — genuine canonical time marginals are kernel powers

This theorem derives, from the frozen infinite strategic-world path law's
actual transition-pair identity, that the state at time n has distribution
K^n under a point start. No unverified finite-word surrogate is used.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit
namespace TypedMarginalPowers

open TypedStrategicWitness
open PermanssonLean

attribute [local instance] StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

/-- Exact Chapman–Kolmogorov one-step marginal recursion of the genuine
Ionescu–Tulcea path law for any initial probability measure. -/
theorem canonical_eval_succ (μ : Measure Y) [IsProbabilityMeasure μ]
    (n : ℕ) :
    (model.pathLaw μ).map (fun w : ℕ → Y => w (n+1)) =
      model.inducedKernel ∘ₘ
        (model.pathLaw μ).map (fun w : ℕ → Y => w n) := by
  let P := model.pathLaw μ
  let K := model.inducedKernel
  let pairFn : (ℕ → Y) → (((i : Finset.Iic n) → Y) × Y) :=
    fun w => (Preorder.frestrictLe n w, w (n+1))
  let last : ((i : Finset.Iic n) → Y) → Y :=
    fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩
  have hpair :
      (P.map (Preorder.frestrictLe n)) ⊗ₘ
        StrategicWorldModel.stationaryHistoryKernel K n =
          P.map pairFn :=
    StrategicWorldModel.pathLaw_has_transition_pair model μ n
  ext C hC
  have hpairMeas : Measurable pairFn := by fun_prop
  have hlastMeas : Measurable last := measurable_pi_apply _
  have hK : Measurable (fun z : Y => K z C) :=
    Kernel.measurable_coe K hC
  calc
    ((P.map (fun w : ℕ → Y => w (n+1))) C) =
        P ((fun w : ℕ → Y => w (n+1)) ⁻¹' C) :=
      Measure.map_apply (measurable_pi_apply (n+1)) hC
    _ = (P.map pairFn) (Set.univ ×ˢ C) := by
      rw [Measure.map_apply hpairMeas (MeasurableSet.univ.prod hC)]
      congr 1
      ext w
      simp [pairFn]
    _ = ((P.map (Preorder.frestrictLe n)) ⊗ₘ
        StrategicWorldModel.stationaryHistoryKernel K n)
        (Set.univ ×ˢ C) := by rw [hpair]
    _ = ∫⁻ h, K (last h) C ∂(P.map (Preorder.frestrictLe n)) := by
      rw [Measure.compProd_apply_prod MeasurableSet.univ hC]
      simp only [MeasureTheory.setLIntegral_univ]
      rfl
    _ = ∫⁻ w, K (w n) C ∂P := by
      change (∫⁻ h, ((fun z : Y => K z C) ∘ last) h
        ∂(P.map (Preorder.frestrictLe n))) = _
      rw [lintegral_map (hK.comp hlastMeas)
        (Preorder.measurable_frestrictLe n)]
      rfl
    _ = (K ∘ₘ (P.map (fun w : ℕ → Y => w n))) C := by
      rw [Measure.bind_apply hC (Kernel.aemeasurable _)]
      rw [lintegral_map hK (measurable_pi_apply n)]

/-- The genuine typed model's time-n marginal equals the n-step power of
its real induced kernel, at every finite horizon and physical initial state. -/
theorem canonical_eval_eq_kernel_pow (y : Y) :
    ∀ n : ℕ,
      (model.pathLaw (Measure.dirac y)).map
        (fun w : ℕ → Y => w n) =
      (model.inducedKernel ^ n) y := by
  intro n
  induction n with
  | zero =>
      rw [StrategicWorldModel.pathLaw_eval_zero model (Measure.dirac y)]
      simp only [pow_zero, Kernel.id_apply]
  | succ n ih =>
      rw [canonical_eval_succ (Measure.dirac y) n, ih]
      apply Measure.ext
      intro C hC
      rw [Measure.bind_apply hC (Kernel.aemeasurable _)]
      exact (Kernel.pow_succ_apply_eq_lintegral
        model.inducedKernel n y hC).symm

end
end TypedMarginalPowers
end MultipleLimit
end PermanssonResearch
