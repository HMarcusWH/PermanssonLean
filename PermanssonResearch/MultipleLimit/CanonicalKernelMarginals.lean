import PermanssonResearch.MultipleLimit.FiniteCanonicalPath
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic

/-!
# Lane C2 — real canonical infinite-path marginals equal K^n

This module generalizes the actual C1 typed marginal theorem to
arbitrary homogeneous Markov kernels on a measurable state type.
The proof uses the TRUE Ionescu–Tulcea transition-pair identity
and proves time zero separately, rather than assuming independent
coordinate samples or transplanting a rational finite-prefix law.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit
namespace CanonicalKernelMarginals

open FiniteCanonicalPath

variable {Y : Type*} [MeasurableSpace Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- Exact finite-history transition identity of the real generic
canonical infinite Markov trajectory. -/
theorem canonical_transition_pair
    (μ : Measure Y) [IsProbabilityMeasure μ] (n : ℕ) :
    (canonicalPathLaw K μ).map (Preorder.frestrictLe n) ⊗ₘ
      PermanssonLean.ProbabilitySupport.stationaryPrefixKernel K n =
    (canonicalPathLaw K μ).map
      (fun w : ℕ → Y => (Preorder.frestrictLe n w, w (n+1))) := by
  unfold canonicalPathLaw
  simpa using
    (Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ : ℕ => Y)
      (κ := fun k => PermanssonLean.ProbabilitySupport.stationaryPrefixKernel K k)
      (μ₀ := μ) (a := n))

/-- One-step marginal Chapman–Kolmogorov identity, derived from the
true canonical infinite trajectory and the actual stationary kernel. -/
theorem canonical_eval_succ
    (μ : Measure Y) [IsProbabilityMeasure μ] (n : ℕ) :
    (canonicalPathLaw K μ).map (fun w : ℕ → Y => w (n+1)) =
      K ∘ₘ (canonicalPathLaw K μ).map (fun w : ℕ → Y => w n) := by
  let P := canonicalPathLaw K μ
  let pairFn : (ℕ → Y) → (((i : Finset.Iic n) → Y) × Y) :=
    fun w => (Preorder.frestrictLe n w, w (n+1))
  let last : ((i : Finset.Iic n) → Y) → Y :=
    fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩
  have hpair :
      (P.map (Preorder.frestrictLe n)) ⊗ₘ
        PermanssonLean.ProbabilitySupport.stationaryPrefixKernel K n =
          P.map pairFn :=
    canonical_transition_pair K μ n
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
        PermanssonLean.ProbabilitySupport.stationaryPrefixKernel K n)
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

/-- The zeroth state under the canonical Dirac-initial law is
exactly the declared starting point. -/
theorem canonical_eval_zero_dirac
    [MeasurableSingletonClass Y] (y : Y) :
    (canonicalPathLaw K (Measure.dirac y)).map
      (fun w : ℕ → Y => w 0) =
      Measure.dirac y := by
  let last : ((i : Finset.Iic 0) → Y) → Y :=
    fun h => h ⟨0, Finset.mem_Iic.mpr le_rfl⟩
  calc
    (canonicalPathLaw K (Measure.dirac y)).map
        (fun w : ℕ → Y => w 0) =
      ((canonicalPathLaw K (Measure.dirac y)).map
        (Preorder.frestrictLe 0)).map last := by
        have hlast : Measurable last := measurable_pi_apply _
        rw [Measure.map_map hlast (Preorder.measurable_frestrictLe 0)]
        rfl
    _ = (PermanssonLean.ProbabilitySupport.finitePrefixLaw K y 0).map last := by
      rw [canonicalPathLaw_prefix_dirac K y 0]
    _ = Measure.dirac y := by
      unfold PermanssonLean.ProbabilitySupport.finitePrefixLaw
      rw [Kernel.partialTraj_self, Kernel.id_apply]
      rw [Measure.map_dirac]
      rfl

/-- Generic point-start canonical time-n marginal = n-step REAL
kernel power, including all n and arbitrary finite or infinite
measurable state types with singleton measurability. -/
theorem canonical_eval_eq_kernel_pow
    [MeasurableSingletonClass Y] (y : Y) :
    ∀ n : ℕ,
      (canonicalPathLaw K (Measure.dirac y)).map
        (fun w : ℕ → Y => w n) = (K ^ n) y := by
  intro n
  induction n with
  | zero =>
      rw [canonical_eval_zero_dirac K y]
      change Measure.dirac y = Kernel.id y
      exact (Kernel.id_apply y).symm
  | succ n ih =>
      rw [canonical_eval_succ K (Measure.dirac y) n, ih]
      apply Measure.ext
      intro C hC
      rw [Measure.bind_apply hC (Kernel.aemeasurable _)]
      exact (Kernel.pow_succ_apply_eq_lintegral K n y hC).symm

end CanonicalKernelMarginals
end MultipleLimit
end PermanssonResearch
