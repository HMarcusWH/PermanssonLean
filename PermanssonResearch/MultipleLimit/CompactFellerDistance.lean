import PermanssonResearch.MultipleLimit.CompactFellerEmpirical
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! A fixed compatible weak metric makes the compact-Feller family
conclusion an explicit distance-to-family limit. The metric is chosen from
the weak topology before any paths are compared. -/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PermanssonResearch.MultipleLimit.CompactFeller

set_option autoImplicit false
noncomputable section

open FiniteCanonicalPath FiniteStateOccupation

variable {Y : Type*} [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable [Nonempty Y]

def weakFamilyDistance (F : Set (ProbabilityMeasure Y)) (π : ProbabilityMeasure Y) : ℝ :=
  letI : MetricSpace (ProbabilityMeasure Y) := TopologicalSpace.metrizableSpaceMetric (ProbabilityMeasure Y)
  Metric.infDist π F

theorem weakFamilyDistance_continuous (F : Set (ProbabilityMeasure Y)) :
    Continuous (weakFamilyDistance F) := by
  letI : MetricSpace (ProbabilityMeasure Y) := TopologicalSpace.metrizableSpaceMetric (ProbabilityMeasure Y)
  exact Metric.continuous_infDist_pt F

theorem weakFamilyDistance_zero (F : Set (ProbabilityMeasure Y)) (π : ProbabilityMeasure Y)
    (hπ : π ∈ F) : weakFamilyDistance F π = 0 := by
  letI : MetricSpace (ProbabilityMeasure Y) := TopologicalSpace.metrizableSpaceMetric (ProbabilityMeasure Y)
  exact Metric.infDist_zero_of_mem hπ

theorem weakFamilyDistance_zero_iff (F : Set (ProbabilityMeasure Y))
    (hF : IsClosed F) (hne : F.Nonempty) (π : ProbabilityMeasure Y) :
    weakFamilyDistance F π = 0 ↔ π ∈ F := by
  letI : MetricSpace (ProbabilityMeasure Y) := TopologicalSpace.metrizableSpaceMetric (ProbabilityMeasure Y)
  exact (hF.mem_iff_infDist_zero hne).symm

/-- For a fixed nonempty closed family in the compact law space, approach
in distance and inclusion of all weak cluster points are equivalent. -/
theorem distance_tendsto_iff_clusters (L : ℕ → ProbabilityMeasure Y)
    (F : Set (ProbabilityMeasure Y)) (hF : IsClosed F) (hne : F.Nonempty) :
    Tendsto (fun n => weakFamilyDistance F (L n)) atTop (𝓝 0) ↔
      ∀ π, MapClusterPt π atTop L → π ∈ F := by
  constructor
  · intro h π hc
    have hp := hc.continuousAt_comp (weakFamilyDistance_continuous F).continuousAt
    have hl : Filter.map (weakFamilyDistance F ∘ L) atTop ≤ 𝓝 (0 : ℝ) := h
    have hz : weakFamilyDistance F π = 0 := eq_of_nhds_neBot (hp.clusterPt.mono hl)
    exact (weakFamilyDistance_zero_iff F hF hne π).mp hz
  · intro h
    have hs : Tendsto L atTop (𝓝ˢ F) := isCompact_univ.tendsto_nhdsSet_of_mapClusterPt
      (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) (fun π _ hc => h π hc)
    exact ((weakFamilyDistance_continuous F).tendsto_nhdsSet_nhds
      (fun π hπ => weakFamilyDistance_zero F π hπ)).comp hs

/-- Singleton family distance recovers the original weak convergence
clause, with no claim about the other Exact-GR requirements. -/
theorem singleton_distance_iff_tendsto (L : ℕ → ProbabilityMeasure Y) (ν : ProbabilityMeasure Y) :
    Tendsto (fun n => weakFamilyDistance {ν} (L n)) atTop (𝓝 0) ↔
      Tendsto L atTop (𝓝 ν) := by
  constructor
  · intro h
    have hc := (distance_tendsto_iff_clusters L {ν} isClosed_singleton (Set.singleton_nonempty ν)).mp h
    exact isCompact_univ.tendsto_nhds_of_unique_mapClusterPt
      (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
      (fun π _ hp => Set.mem_singleton_iff.mp (hc π hp))
  · intro h
    have ht := ((weakFamilyDistance_continuous {ν}).tendsto ν).comp h
    simpa only [weakFamilyDistance_zero {ν} ν (by simp),Function.comp_def] using ht

variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- Actual distance to the fixed invariant-law set tends to zero almost
surely, for every initial probability law. -/
theorem empirical_invariant_distance_ae (hF : IsFeller K) (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n => weakFamilyDistance {π | Invariant K π}
        (empiricalOccupation w (n+1) (Nat.succ_pos n))) atTop (𝓝 0) := by
  have hp := (weakFamilyDistance_continuous {π | Invariant K π}).tendsto_nhdsSet_nhds
    (fun π hπ => weakFamilyDistance_zero _ π hπ)
  filter_upwards [empirical_invariant_family_ae K hF μ] with w hw
  exact hp.comp hw

theorem empirical_predeclared_family_distance_ae (hF : IsFeller K) (μ : ProbabilityMeasure Y)
    (F : Set (ProbabilityMeasure Y)) (cover : ∀ π, Invariant K π → π ∈ F) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n => weakFamilyDistance F
        (empiricalOccupation w (n+1) (Nat.succ_pos n))) atTop (𝓝 0) := by
  have hp := (weakFamilyDistance_continuous F).tendsto_nhdsSet_nhds
    (fun π hπ => weakFamilyDistance_zero F π (cover π hπ))
  filter_upwards [empirical_invariant_family_ae K hF μ] with w hw
  exact hp.comp hw

end
end PermanssonResearch.MultipleLimit.CompactFeller
