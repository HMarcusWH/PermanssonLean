import PermanssonResearch.MultipleLimit.KernelCanonicalBlockBridge
import PermanssonResearch.MultipleLimit.TypedMarginalPowers
import PermanssonResearch.MultipleLimit.TypedAbsorbingKernel
import PermanssonResearch.MultipleLimit.TypedInitialMixture
import PermanssonResearch.MultipleLimit.AbsorptionFromTail
import PermanssonResearch.MultipleLimit.TypedAbsorbingContinuation
import Mathlib.Tactic

/-!
# Lane C1 — actual kernel-power to canonical geometric absorption

This is a separate, self-contained path from the genuine alpha/P/U induced
kernel to an N=2, q=1/2 canonical no-hit bound. It instantiates the generic
Chapman–Kolmogorov theorem with proved two-step kernel rows, then transfers
point laws to arbitrary initial probability laws without independent blocks.
The earlier exact-hitting absorption proof is not used in this derivation.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace TypedGeometricAbsorption

open TypedStrategicWitness TypedAbsorbingKernel
open TypedMarginalPowers TypedInitialMixture
open KernelCanonicalBlockBridge TypedAbsorbingContinuation
open ExactRationalAbsorption

noncomputable section

private def A : Set Y := ({a, b} : Finset Y)

private theorem hA : MeasurableSet A := MeasurableSet.of_discrete

private theorem half_ofReal :
    ENNReal.ofReal (1/2 : ℝ) = (1/2 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

private theorem half_toNNReal :
    (↑(((2 : ℝ)⁻¹).toNNReal) : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ := by
  simpa only [one_div, ENNReal.ofReal] using half_ofReal

private theorem compl_eq : Aᶜ = ({t, u} : Set Y) := by
  ext z
  rcases z with ⟨s, x⟩
  cases s <;> cases x <;> simp [A, t, u, a, b]

/-- Exact one-step survival mass, computed from the true typed induced
kernel, not independently postulated transition probabilities. -/
private theorem one_step_outside (y : Y) :
    model.inducedKernel y Aᶜ =
      if y = t then 1 else if y = u then (1/2 : ℝ≥0∞) else 0 := by
  rw [compl_eq]
  have htu : Disjoint ({t} : Set Y) ({u} : Set Y) := by
    simp [t, u]
  have hu : MeasurableSet ({u} : Set Y) := measurableSet_singleton _
  rw [show ({t, u} : Set Y) = ({t} : Set Y) ∪ {u} by ext z; simp [or_comm]]
  rw [measure_union htu hu]
  rw [inducedKernel_atom_entry y t, inducedKernel_atom_entry y u]
  rcases y with ⟨s, x⟩
  cases s <;> cases x <;>
    norm_num [fourStateMatrix, codeState, t, u, a, b] <;>
    exact half_ofReal

/-- Exact two-step survival probability for each of the four typed states.
The sharp transient values are 1/2 from t and 1/4 from u. -/
theorem two_step_kernel_outside (y : Y) :
    (model.inducedKernel ^ 2) y Aᶜ =
      if y = t then (1/2 : ℝ≥0∞)
      else if y = u then (1/4 : ℝ≥0∞) else 0 := by
  have hpow :
      (model.inducedKernel ^ 2) y Aᶜ =
        ∫⁻ z, model.inducedKernel z Aᶜ ∂(model.inducedKernel y) := by
    simpa using Kernel.pow_succ_apply_eq_lintegral
      model.inducedKernel 1 y hA.compl
  rw [hpow, lintegral_fintype]
  simp_rw [one_step_outside]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  rcases y with ⟨s, x⟩
  cases s <;> cases x <;>
    norm_num [inducedKernel_atom_entry, fourStateMatrix, codeState,
      t, u, a, b, ENNReal.ofReal] <;>
    norm_num [half_toNNReal]

private theorem two_step_inside (z : Y) (hz : z ∈ A) :
    (model.inducedKernel ^ 2) z Aᶜ = 0 := by
  rw [two_step_kernel_outside]
  rcases z with ⟨s, x⟩
  cases s <;> cases x <;> simp [A, t, u, a, b] at hz ⊢

private theorem two_step_outside_bound (z : Y) (hz : z ∉ A) :
    (model.inducedKernel ^ 2) z Aᶜ ≤ (1/2 : ℝ≥0∞) := by
  rw [two_step_kernel_outside]
  split_ifs <;> norm_num

/-- The generic set-valued no-hit event is literally the finite-absorber
no-hit event; no change of hitting-time convention is hidden in transport. -/
theorem noHitThrough_eq (n : ℕ) :
    KernelCanonicalBlockBridge.noHitThrough A n =
      NoHitThrough ({a, b} : Finset Y) n := by
  rfl

/-- Canonical geometric tail from a POINT start, instantiated from the
actual induced kernel and actual infinite path-law time marginals. -/
theorem point_geometric_noHit (y : Y) (k : ℕ) :
    model.pathLaw (Measure.dirac y)
      (NoHitThrough ({a, b} : Finset Y) (k*2)) ≤
      (1/2 : ℝ≥0∞)^k := by
  rw [← noHitThrough_eq]
  exact KernelCanonicalBlockBridge.canonical_geometric_noHit
    model.inducedKernel (model.pathLaw (Measure.dirac y)) y
    A hA (canonical_eval_eq_kernel_pow y)
    2 (1/2 : ℝ≥0∞)
    two_step_inside two_step_outside_bound k

private theorem measurable_noHitThrough (n : ℕ) :
    MeasurableSet (NoHitThrough ({a, b} : Finset Y) n) := by
  have heq :
      NoHitThrough ({a, b} : Finset Y) n =
        ⋂ t : ℕ,
          (if t ≤ n then
            {w : ℕ → Y | w t ∉ ({a, b} : Finset Y)}
          else Set.univ) := by
    ext w
    simp only [NoHitThrough, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hw t
      split_ifs with ht
      · exact hw t ht
      · trivial
    · intro hw t ht
      simpa [ht] using hw t
  rw [heq]
  apply MeasurableSet.iInter
  intro t
  split_ifs
  · exact (MeasurableSet.of_discrete :
      MeasurableSet (({a, b} : Finset Y) : Set Y)).compl.preimage
      (measurable_pi_apply t)
  · exact MeasurableSet.univ

/-- Universal all-starting-law path-space geometric bound. This step
integrates the verified point-start estimates using the genuine infinite
canonical initial-mixture law; no independent-block assumption appears. -/
theorem canonical_geometric_noHit_initial (μ : ProbabilityMeasure Y)
    (k : ℕ) :
    model.pathLaw μ.toMeasure
      (NoHitThrough ({a, b} : Finset Y) (k*2)) ≤
      (1/2 : ℝ≥0∞)^k := by
  let E := NoHitThrough ({a, b} : Finset Y) (k*2)
  have hmass : (∑ y : Y, μ.toMeasure {y}) = 1 := by
    have h := typed_pathLaw_event_initial_mixture μ
      (Set.univ : Set (ℕ → Y)) MeasurableSet.univ
    simp only [measure_univ, mul_one] at h
    exact h.symm
  have hmix := typed_pathLaw_event_initial_mixture μ E
    (measurable_noHitThrough (k*2))
  calc
    model.pathLaw μ.toMeasure E =
        ∑ y : Y, μ.toMeasure {y} *
          model.pathLaw (Measure.dirac y) E := hmix
    _ ≤ ∑ y : Y, μ.toMeasure {y} * (1/2 : ℝ≥0∞)^k := by
      apply Finset.sum_le_sum
      intro y _
      simpa [mul_comm] using
        (mul_le_mul_left (point_geometric_noHit y k) (μ.toMeasure {y}))
    _ = (∑ y : Y, μ.toMeasure {y}) * (1/2 : ℝ≥0∞)^k := by
      rw [Finset.sum_mul]
    _ = (1/2 : ℝ≥0∞)^k := by rw [hmass, one_mul]

/-- The independent kernel-derived geometric tail plus the proved
absorbing-row continuation yield actual almost-sure absorption of the
canonical path law, without using the earlier exact-hitting theorem. -/
theorem canonical_almostSureAbsorption_from_geometric
    (μ : ProbabilityMeasure Y) :
    HasAlmostSureAbsorption family (model.pathLaw μ.toMeasure) := by
  have hpow (k : ℕ) :
      (1/2 : ℝ≥0∞)^k =
        ENNReal.ofReal ((1 - (1/2 : ℝ))^k) := by
    rw [show (1 - (1/2 : ℝ)) = (1/2 : ℝ) by norm_num,
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1/2) k,
      half_ofReal]
  have hblocks (k : ℕ) :
      model.pathLaw μ.toMeasure
        (NoHitThrough family.absorbing (k*2)) ≤
        ENNReal.ofReal ((1 - (1/2 : ℝ))^k) := by
    simpa only [family, hpow k] using
      canonical_geometric_noHit_initial μ k
  exact ae_absorptionPaths_of_geometric_bounds family
    (model.pathLaw μ.toMeasure) 2 (1/2 : ℝ)
    (by norm_num) (by norm_num) hblocks
    (stays_after_absorbing_ae μ)

end
end TypedGeometricAbsorption
end MultipleLimit
end PermanssonResearch
