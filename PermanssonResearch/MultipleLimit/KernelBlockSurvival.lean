import PermanssonResearch.MultipleLimit.AbsorbingFamily
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Lane C1 — generic Chapman–Kolmogorov geometric N-block tail

The conditional N-step bound is stated directly in terms of the actual
kernel power. This file derives a geometric bound on the endpoint marginal
using the genuine Markov semigroup, without asserting independent blocks
or assuming the geometric inequality itself.

Lifting this endpoint estimate to the infinite canonical path law is a
separate theorem; neither almost-sure hitting nor a random limit is
claimed by this algebraic lemma alone.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace KernelBlockSurvival

noncomputable section

/-- A uniform one-block bound on the actual N-step endpoint kernel,
vanishing outside the survival set, yields a geometric bound for every
multiple of N. No independence assumption is present. -/
theorem geometric_endpoint_power
    {Y : Type*} [MeasurableSpace Y]
    (K : Kernel Y Y) (B : Set Y) (hB : MeasurableSet B)
    (N : ℕ) (q : ℝ≥0∞)
    (hblock : ∀ y : Y,
      (K ^ N) y B ≤ B.indicator (fun _ => q) y) :
    ∀ (k : ℕ) (y : Y),
      (K ^ (k*N)) y B ≤ q^k := by
  intro k
  induction k with
  | zero =>
      intro y
      simp only [Nat.zero_mul, pow_zero]
      change (Measure.dirac y) B ≤ 1
      by_cases hy : y ∈ B
      · simp [Measure.dirac_apply' _ hB, hy]
      · simp [Measure.dirac_apply' _ hB, hy]
  | succ k ih =>
      intro y
      have hpow :
          (K ^ ((k+1)*N)) y B =
            ∫⁻ z, (K ^ N) z B ∂((K ^ (k*N)) y) := by
        rw [show (k+1)*N = k*N+N by ring]
        exact Kernel.pow_add_apply_eq_lintegral K (k*N) N y hB
      calc
        (K ^ ((k+1)*N)) y B =
            ∫⁻ z, (K ^ N) z B ∂((K ^ (k*N)) y) := hpow
        _ ≤ ∫⁻ z, B.indicator (fun _ => q) z ∂((K ^ (k*N)) y) :=
          lintegral_mono (fun z => hblock z)
        _ = q * (K ^ (k*N)) y B := lintegral_indicator_const hB q
        _ ≤ q * q^k := mul_le_mul_left' (ih y) q
        _ = q^(k+1) := by rw [pow_succ]; ac_rfl

/-- Input in the natural absorbing-set form: the genuine N-step kernel
cannot exit the absorbing set, and from its complement the chance to
remain outside after N steps is uniformly at most q. -/
theorem geometric_endpoint_power_of_absorbing_block
    {Y : Type*} [MeasurableSpace Y]
    (K : Kernel Y Y) (A : Set Y) (hA : MeasurableSet A)
    (N : ℕ) (q : ℝ≥0∞)
    (hinside : ∀ y ∈ A, (K ^ N) y Aᶜ = 0)
    (houtside : ∀ y ∉ A, (K ^ N) y Aᶜ ≤ q) :
    ∀ (k : ℕ) (y : Y),
      (K ^ (k*N)) y Aᶜ ≤ q^k := by
  apply geometric_endpoint_power K Aᶜ hA.compl N q
  intro y
  by_cases hy : y ∈ A
  · have hnot : y ∉ Aᶜ := by simpa using hy
    rw [Set.indicator_of_notMem hnot, hinside y hy]
    exact le_rfl
  · have hmem : y ∈ Aᶜ := hy
    simpa only [Set.indicator_of_mem hmem] using houtside y hy

end
end KernelBlockSurvival
end MultipleLimit
end PermanssonResearch
