import PermanssonLean.Regime.GeneratedRegime
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.MetricSpace.Polish

open Filter MeasureTheory Set
open scoped Topology

namespace PermanssonLean
namespace DescriptorTopology

universe uH uI

variable {H : Type uH}

/-- A compatible metric can always be truncated at one without changing the
underlying topology. This is the metric-level content used in Proposition 4.1a. -/
@[instance_reducible]\nnoncomputable def boundedCompatibleMetric
    (H : Type uH) [TopologicalSpace H] [TopologicalSpace.MetrizableSpace H] :
    MetricSpace H := by
  letI : MetricSpace H := TopologicalSpace.metrizableSpaceMetric H
  let d : H → H → ℝ := fun x y => min 1 (dist x y)
  refine MetricSpace.ofDistTopology d ?_ ?_ ?_ ?_ ?_
  · intro x
    simp [d]
  · intro x y
    simp [d, dist_comm]
  · intro x y z
    dsimp [d]
    by_cases hxy : 1 ≤ dist x y
    · calc
        min 1 (dist x z) ≤ 1 := min_le_left _ _
        _ = min 1 (dist x y) := (min_eq_left hxy).symm
        _ ≤ min 1 (dist x y) + min 1 (dist y z) := by
          have hnonneg : 0 ≤ min 1 (dist y z) :=
            le_min zero_le_one dist_nonneg
          linarith
    · have hxy' : dist x y < 1 := lt_of_not_ge hxy
      by_cases hyz : 1 ≤ dist y z
      · calc
          min 1 (dist x z) ≤ 1 := min_le_left _ _
          _ = min 1 (dist y z) := (min_eq_left hyz).symm
          _ ≤ min 1 (dist x y) + min 1 (dist y z) := by
            have hnonneg : 0 ≤ min 1 (dist x y) :=
              le_min zero_le_one dist_nonneg
            linarith
      · have hyz' : dist y z < 1 := lt_of_not_ge hyz
        rw [min_eq_right hxy'.le, min_eq_right hyz'.le]
        exact (min_le_right _ _).trans (dist_triangle x y z)
  · intro s
    constructor
    · intro hs x hx
      rcases (Metric.isOpen_iff.1 hs x hx) with ⟨ε, hε, hball⟩
      refine ⟨min ε (1 / 2 : ℝ), lt_min hε (by norm_num), ?_⟩
      intro y hy
      have hdelta_one : min ε (1 / 2 : ℝ) < 1 := by
        exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have hdist_one : dist x y < 1 := by
        by_contra hnot
        have hge : 1 ≤ dist x y := le_of_not_gt hnot
        change min 1 (dist x y) < min ε (1 / 2 : ℝ) at hy
        rw [min_eq_left hge] at hy
        linarith
      change min 1 (dist x y) < min ε (1 / 2 : ℝ) at hy
      rw [min_eq_right hdist_one.le] at hy
      apply hball
      simp only [Metric.mem_ball]
      rw [dist_comm]
      exact lt_of_lt_of_le hy (min_le_left _ _)
    · intro hs
      rw [Metric.isOpen_iff]
      intro x hx
      rcases hs x hx with ⟨ε, hε, hmem⟩
      refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
      intro y hy
      apply hmem y
      simp only [Metric.mem_ball] at hy
      have hxy : dist x y < min ε 1 := by
        simpa [dist_comm] using hy
      exact lt_of_le_of_lt (min_le_right _ _)
        (lt_of_lt_of_le hxy (min_le_left _ _))
  · intro x y hzero
    apply dist_eq_zero.mp
    by_contra hne
    have hpos : 0 < dist x y :=
      lt_of_le_of_ne dist_nonneg (Ne.symm hne)
    have hminpos : 0 < min 1 (dist x y) := lt_min zero_lt_one hpos
    exact (ne_of_gt hminpos) hzero

theorem boundedCompatibleMetric_dist_eq
    (H : Type uH) [TopologicalSpace H] [TopologicalSpace.MetrizableSpace H]
    (x y : H) :
    @dist H (boundedCompatibleMetric H).toDist x y =
      min 1 (@dist H (TopologicalSpace.metrizableSpaceMetric H).toDist x y) :=
  rfl

theorem boundedCompatibleMetric_dist_le_one
    (H : Type uH) [TopologicalSpace H] [TopologicalSpace.MetrizableSpace H]
    (x y : H) :
    @dist H (boundedCompatibleMetric H).toDist x y ≤ 1 := by
  rw [boundedCompatibleMetric_dist_eq]
  exact min_le_left _ _

/-- The weak-convergence topology on probability measures over a Polish Borel
space is metrizable. -/
theorem probabilityMeasure_weak_metrizable_of_polish
    (H : Type uH) [TopologicalSpace H] [PolishSpace H]
    [MeasurableSpace H] [BorelSpace H] :
    TopologicalSpace.MetrizableSpace (ProbabilityMeasure H) := by
  infer_instance

/-- Mathlib's Portmanteau theorem gives the bounded-Lipschitz test-function
characterization of weak convergence on a Polish descriptor space. -/
theorem weakConvergence_iff_boundedLipschitzIntegrals
    {I : Type uI} {F : Filter I} [F.IsCountablyGenerated]
    [TopologicalSpace H] [PolishSpace H]
    [MeasurableSpace H] [BorelSpace H]
    {μs : I → ProbabilityMeasure H} {μ : ProbabilityMeasure H} :
    letI : MetricSpace H := boundedCompatibleMetric H
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : H → ℝ,
        (∃ C : ℝ, ∀ x y, dist (f x) (f y) ≤ C) →
        (∃ L, LipschitzWith L f) →
        Tendsto
          (fun i => ∫ x, f x ∂(μs i))
          F
          (𝓝 (∫ x, f x ∂μ)) := by
  exact tendsto_iff_forall_lipschitz_integral_tendsto

/-- Proposition 4.1a does not need compactness to make the canonical almost-sure
weak convergence mode meaningful. -/
noncomputable def polishAlmostSureWeak
    (Y : Type*) (H : Type uH)
    [MeasurableSpace Y]
    [TopologicalSpace H] [PolishSpace H]
    [MeasurableSpace H] [BorelSpace H] :
    ConvergenceMode Y H :=
  ConvergenceMode.almostSureWeak Y H

/-- A concrete noncompact Polish witness showing that arbitrary probability-law
families need not be uniformly tight. -/
theorem natDirac_not_tight :
    ¬ IsTightMeasureSet (Set.range (fun n : ℕ => Measure.dirac n)) := by
  intro htight
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight
  obtain ⟨K, hKcompact, hKbound⟩ :=
    htight ((2 : ℝ≥0∞)⁻¹) (by positivity)
  have hKfinite : K.Finite := hKcompact.finite_of_discrete
  have hKne : K ≠ Set.univ := by
    intro hKuniv
    have hfinNat : Finite ℕ := Set.finite_univ_iff.mp (hKuniv ▸ hKfinite)
    exact not_finite ℕ hfinNat
  obtain ⟨n, hn⟩ := Set.ne_univ_iff_exists_not_mem.mp hKne
  have hbound := hKbound (Measure.dirac n) ⟨n, rfl⟩
  have hncompl : n ∈ Kᶜ := hn
  rw [Measure.dirac_apply_of_mem hncompl] at hbound
  norm_num at hbound

end DescriptorTopology
end PermanssonLean
