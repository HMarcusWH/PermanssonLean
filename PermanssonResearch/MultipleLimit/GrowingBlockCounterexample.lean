import PermanssonResearch.MultipleLimit.NonfiniteClock
import PermanssonResearch.MultipleLimit.GrowingBlockAverages

/-! C-01: a homogeneous countable-state chain with a fixed two-point
descriptor whose actual empirical occupations fail to converge. The
transition is always the same successor kernel; the clock is physical
state, rather than an undeclared time-dependent kernel. -/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction
namespace PermanssonResearch.MultipleLimit.GrowingBlock
open NonfiniteClock FiniteCanonicalPath FiniteStateOccupation
set_option autoImplicit false

noncomputable def descriptor (n : ℕ) : Fin 2 :=
  ⟨block n % 2,Nat.mod_lt _ (by omega)⟩

theorem descriptor_measurable : Measurable descriptor := measurable_of_countable _

theorem descriptor_continuous : Continuous descriptor := continuous_of_discreteTopology

noncomputable def score : Fin 2 →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun a => (a.val : ℝ),continuous_of_discreteTopology⟩

theorem score_descriptor (n : ℕ) : score (descriptor n) = value n := rfl

theorem descriptor_empirical_integral (n : ℕ) :
    (∫ a, score a ∂(empiricalOccupation descriptor (n+1) (Nat.succ_pos n)).toMeasure) =
      average (n+1) := by
  rw [empirical_integral _ _ score score.continuous.measurable]
  rfl

theorem descriptor_occupations_do_not_converge :
    ¬ ∃ π : ProbabilityMeasure (Fin 2),
      Tendsto (fun n => empiricalOccupation descriptor (n+1) (Nat.succ_pos n)) atTop (𝓝 π) := by
  rintro ⟨π,hπ⟩
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℝ).1 hπ score
  simp_rw [descriptor_empirical_integral] at h
  exact positive_horizon_averages_do_not_converge ⟨_,h⟩

theorem canonical_growing_block_averages_fail :
    ∀ᵐ w ∂canonicalPathLaw clock (Measure.dirac 0),
      ¬ ∃ a : ℝ, Tendsto (fun n =>
        (∑ t ∈ Finset.range (n+1), value (w t))/((n+1 : ℕ) : ℝ)) atTop (𝓝 a) := by
  rw [clock_law,ae_dirac_eq]
  exact positive_horizon_averages_do_not_converge

theorem canonical_growing_block_occupations_fail :
    ∀ᵐ w ∂canonicalPathLaw clock (Measure.dirac 0),
      ¬ ∃ π : ProbabilityMeasure (Fin 2), Tendsto
        (fun n => empiricalOccupation (fun t => descriptor (w t)) (n+1) (Nat.succ_pos n))
        atTop (𝓝 π) := by
  rw [clock_law,ae_dirac_eq]
  exact descriptor_occupations_do_not_converge

end PermanssonResearch.MultipleLimit.GrowingBlock
