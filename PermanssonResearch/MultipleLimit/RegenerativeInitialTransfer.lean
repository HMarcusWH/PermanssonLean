import PermanssonResearch.MultipleLimit.CanonicalShiftLaw
import PermanssonResearch.Probability.RegenerativeRenewalMass

/-! Actual stationary good paths transfer to every initial law for a
regenerative kernel, when the declared good event is measurable and
shift invariant. No stationarity of the arbitrary-initial law is assumed. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ProbabilityTheory
namespace PermanssonResearch.MultipleLimit.RegenerativeTransfer
open FiniteCanonicalPath StationaryCanonical CanonicalShift
open PermanssonResearch.Probability PermanssonResearch.Probability.Regenerative
open PermanssonLean.ProbabilitySupport
set_option autoImplicit false
variable {Y : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y]

theorem shifted_tv_le_pow (R K : Kernel Y Y) [IsMarkovKernel R] [IsMarkovKernel K]
    (ξ μ π : ProbabilityMeasure Y) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hmix : IsMixture R K ξ r) (hπ : K ∘ₘ π.toMeasure = π.toMeasure) (n : ℕ) :
    eventTotalVariation ((canonicalPathLaw K μ.toMeasure).map (shift^[n]))
      (canonicalPathLaw K π.toMeasure) ≤ r^n := by
  rw [iterated_shift_law]
  exact (canonical_tv_le_initial K _ _).trans
    (RegenerativeRenewal.orbit_tv_le_pow R K ξ μ π hr hr1 hmix hπ n)

theorem ae_shiftInvariant_transfer (R K : Kernel Y Y) [IsMarkovKernel R] [IsMarkovKernel K]
    (ξ μ π : ProbabilityMeasure Y) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hmix : IsMixture R K ξ r) (hπ : K ∘ₘ π.toMeasure = π.toMeasure)
    (p : (ℕ → Y) → Prop) (hp : MeasurableSet {w | p w})
    (hshift : ∀ w, p (shift w) ↔ p w)
    (hgood : ∀ᵐ w ∂canonicalPathLaw K π.toMeasure, p w) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure, p w := by
  have hi (n : ℕ) (w : ℕ → Y) : p ((shift^[n]) w) ↔ p w := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply',hshift,ih]
  let B := {w : ℕ → Y | ¬ p w}
  have hB : MeasurableSet B := hp.compl
  have hnull : canonicalPathLaw K π.toMeasure B = 0 := ae_iff.mp hgood
  have hrealnull : (canonicalPathLaw K π.toMeasure).real B = 0 := by
    rw [Measure.real,hnull,ENNReal.toReal_zero]
  have he (n : ℕ) : ((canonicalPathLaw K μ.toMeasure).map (shift^[n])).real B =
      (canonicalPathLaw K μ.toMeasure).real B := by
    rw [Measure.real,Measure.real,Measure.map_apply (measurable_shift.iterate n) hB]
    have hpre : (shift^[n]) ⁻¹' B = B := by
      ext w
      exact not_congr (hi n w)
    rw [hpre]
  have hb (n : ℕ) : (canonicalPathLaw K μ.toMeasure).real B ≤ r^n := by
    have hh := abs_measureReal_sub_le_eventTotalVariation
      ((canonicalPathLaw K μ.toMeasure).map (shift^[n]))
      (canonicalPathLaw K π.toMeasure) hB
    rw [hrealnull,sub_zero,he,abs_of_nonneg measureReal_nonneg] at hh
    exact hh.trans (shifted_tv_le_pow R K ξ μ π hr hr1 hmix hπ n)
  have hz : (canonicalPathLaw K μ.toMeasure).real B = 0 :=
    le_antisymm (ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1) hb)
      measureReal_nonneg
  exact ae_iff.mpr ((measureReal_eq_zero_iff (μ := canonicalPathLaw K μ.toMeasure) (s := B)).mp hz)

end PermanssonResearch.MultipleLimit.RegenerativeTransfer
