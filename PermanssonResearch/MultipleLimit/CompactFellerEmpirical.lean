import PermanssonResearch.MultipleLimit.CompactFellerKernel
import PermanssonResearch.MultipleLimit.FiniteStateOccupation
import PermanssonResearch.MultipleLimit.FiniteUniformAverage

/-! Actual almost-sure compact-Feller empirical cluster theorem. The
empirical laws are the frozen time-zero-inclusive positive-horizon laws.
Stationary random-law Birkhoff convergence is a separate theorem. -/

open Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology ENNReal

namespace PermanssonResearch.MultipleLimit.CompactFeller

set_option autoImplicit false
noncomputable section

open CanonicalBoundedInnovations FiniteCanonicalPath FiniteStateOccupation

variable {Y : Type*} [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable [Nonempty Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

theorem empirical_integral (w : ℕ → Y) (n : ℕ) (f : Y → ℝ) (hf : Measurable f) :
    (∫ y, f y ∂(empiricalOccupation w (n+1) (Nat.succ_pos n)).toMeasure) =
      (((n+1 : ℕ) : ℝ)⁻¹) * ∑ t ∈ Finset.range (n+1), f (w t) := by
  change (∫ y, f y ∂Measure.map (fun i : Fin (n+1) => w (i : ℕ))
    (PermanssonLean.RegimeSpecification.uniformFinProbability (n+1) (Nat.succ_pos n)).toMeasure) = _
  rw [integral_map (by fun_prop) hf.aestronglyMeasurable]
  rw [FiniteUniformAverage.integral_uniformFin_eq_average]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => f (w i))]

theorem empirical_residual_telescope (w : ℕ → Y) (n : ℕ) (f : C(Y,ℝ)) :
    residual K (empiricalOccupation w (n+1) (Nat.succ_pos n)) f =
      (f (w (n+1))-f (w 0)) / ((n+1 : ℕ) : ℝ) -
      (∑ t ∈ Finset.range (n+1), innovation K f t w) / ((n+1 : ℕ) : ℝ) := by
  rw [residual_eq_predict,empirical_integral w n (predict K f) (predict_measurable K f f.continuous.measurable),
    empirical_integral w n f f.continuous.measurable]
  have ht : (∑ t ∈ Finset.range (n+1), (f (w (t+1))-f (w t))) =
      f (w (n+1))-f (w 0) := Finset.sum_range_sub (fun t => f (w t)) (n+1)
  rw [← ht]
  simp only [innovation,Finset.sum_sub_distrib]
  ring

theorem endpoint_average_tendsto_zero (w : ℕ → Y) (f : C(Y,ℝ)) :
    Tendsto (fun n => (f (w (n+1))-f (w 0)) / ((n+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hu : Tendsto (fun n : ℕ => (2*‖f‖)/((n+1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat (2*‖f‖))
  have hb (n : ℕ) : |(f (w (n+1))-f (w 0)) / ((n+1 : ℕ) : ℝ)| ≤
      (2*‖f‖)/((n+1 : ℕ) : ℝ) := by
    rw [abs_div,abs_of_pos (show (0 : ℝ) < ((n+1 : ℕ) : ℝ) by positivity)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h1 : |f (w (n+1))| ≤ ‖f‖ := by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm _
    have h0 : |f (w 0)| ≤ ‖f‖ := by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm _
    exact (abs_sub _ _).trans ((add_le_add h1 h0).trans_eq (by ring))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using squeeze_zero (fun n => abs_nonneg _) hb hu

/-- The actual canonical martingale strong law gives vanishing empirical
stationarity defect for each bounded continuous test. -/
theorem empirical_residual_ae (μ : ProbabilityMeasure Y) (f : C(Y,ℝ)) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n => residual K (empiricalOccupation w (n+1) (Nat.succ_pos n)) f)
        atTop (𝓝 0) := by
  have hi := canonical_innovation_strong_law K μ f f.continuous.measurable ‖f‖ (norm_nonneg _)
    (fun y => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm y)
  filter_upwards [hi] with w hw
  have hs := (endpoint_average_tendsto_zero w f).sub hw
  simpa only [← empirical_residual_telescope,sub_zero] using hs

/-- The intersection uses a countable norm-dense class in compact C(Y,R),
then a uniform approximation argument yields all continuous tests. -/
theorem empirical_all_residuals_ae (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      ∀ f : C(Y,ℝ),
        Tendsto (fun n => residual K (empiricalOccupation w (n+1) (Nat.succ_pos n)) f)
          atTop (𝓝 0) := by
  have hc (k : ℕ) := empirical_residual_ae K μ (denseSeq C(Y,ℝ) k)
  filter_upwards [ae_all_iff.mpr hc] with w hw
  intro f
  exact residual_tendsto_of_dense K (fun n => empiricalOccupation w (n+1) (Nat.succ_pos n))
    (denseSeq C(Y,ℝ)) (denseRange_denseSeq _) hw f

/-- Every weak empirical cluster point is invariant, almost surely under
the actual canonical law from every initial probability distribution. -/
theorem empirical_clusters_invariant_ae (hF : IsFeller K) (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      ∀ π : ProbabilityMeasure Y,
        MapClusterPt π atTop (fun n => empiricalOccupation w (n+1) (Nat.succ_pos n)) →
          K ∘ₘ π.toMeasure = π.toMeasure := by
  filter_upwards [empirical_all_residuals_ae K μ] with w hw
  intro π hc
  exact (invariant_iff_measure K π).mp
    (cluster_invariant K hF _ hw π hc)

/-- A genuine a.s. weak approach to the fixed invariant-law family, not
an assertion that every path chooses a single limit when laws are multiple. -/
theorem empirical_invariant_family_ae (hF : IsFeller K) (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n => empiricalOccupation w (n+1) (Nat.succ_pos n)) atTop
        (𝓝ˢ {π | Invariant K π}) := by
  filter_upwards [empirical_all_residuals_ae K μ] with w hw
  exact tendsto_invariant_family K hF _ hw

/-- A unique invariant probability forces full a.s. weak empirical
convergence, allowing arbitrary initial laws and periodic behavior. -/
theorem empirical_unique_invariant_ae (hF : IsFeller K) (μ π : ProbabilityMeasure Y)
    (hu : ∀ ν : ProbabilityMeasure Y, K ∘ₘ ν.toMeasure = ν.toMeasure → ν = π) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n => empiricalOccupation w (n+1) (Nat.succ_pos n)) atTop (𝓝 π) := by
  filter_upwards [empirical_all_residuals_ae K μ] with w hw
  exact tendsto_unique_invariant K hF _ hw π (fun ν hν => hu ν ((invariant_iff_measure K ν).mp hν))

/-- Compactness and the actual all-test residual theorem also prove
existence of an invariant probability; no separate recurrence hypothesis. -/
theorem exists_invariant (hF : IsFeller K) :
    ∃ π : ProbabilityMeasure Y, K ∘ₘ π.toMeasure = π.toMeasure := by
  let μ : ProbabilityMeasure Y := ⟨Measure.dirac (Classical.arbitrary Y),by infer_instance⟩
  obtain ⟨w,hw⟩ := (empirical_all_residuals_ae K μ).exists
  obtain ⟨π,_,hc⟩ := (isCompact_univ : IsCompact (Set.univ : Set (ProbabilityMeasure Y))).exists_mapClusterPt
    (f := atTop) (u := fun n : ℕ => empiricalOccupation w (n+1) (Nat.succ_pos n)) (by simp)
  exact ⟨π,(invariant_iff_measure K π).mp (cluster_invariant K hF _ hw π hc)⟩

variable {H : Type*} [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]

/-- A descriptor and a family are fixed before taking the path limit.
Continuity, rather than mere measurability, transports weak approach to
the family. The inclusion premise concerns every actual invariant law. -/
theorem empirical_descriptor_family_ae (hF : IsFeller K) (μ : ProbabilityMeasure Y)
    (h : Y → H) (hh : Continuous h) (F : Set (ProbabilityMeasure H))
    (cover : ∀ π : ProbabilityMeasure Y, Invariant K π → π.map h ∈ F) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n => (empiricalOccupation w (n+1) (Nat.succ_pos n)).map h)
        atTop (𝓝ˢ F) := by
  have hp : Tendsto (fun π : ProbabilityMeasure Y => π.map h)
      (𝓝ˢ {π | Invariant K π}) (𝓝ˢ F) :=
    (ProbabilityMeasure.continuous_map hh).tendsto_nhdsSet cover
  filter_upwards [empirical_invariant_family_ae K hF μ] with w hw
  exact hp.comp hw

/-- Observable uniqueness can hold across several distinct invariant
physical laws. It yields actual a.s. descriptor convergence without
claiming uniqueness of the underlying physical class. -/
theorem empirical_descriptor_unique_ae (hF : IsFeller K) (μ : ProbabilityMeasure Y)
    (h : Y → H) (hh : Continuous h) (ν : ProbabilityMeasure H)
    (cover : ∀ π : ProbabilityMeasure Y, Invariant K π → π.map h = ν) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n => (empiricalOccupation w (n+1) (Nat.succ_pos n)).map h)
        atTop (𝓝 ν) := by
  have hp : Tendsto (fun π : ProbabilityMeasure Y => π.map h)
      (𝓝ˢ {π | Invariant K π}) (𝓝 ν) :=
    (ProbabilityMeasure.continuous_map hh).tendsto_nhdsSet_nhds cover
  filter_upwards [empirical_invariant_family_ae K hF μ] with w hw
  exact hp.comp hw

theorem empirical_map {V : Type*} [MeasurableSpace V] (w : ℕ → V)
    (h : V → H) (hh : Measurable h) (n : ℕ) :
    (empiricalOccupation w (n+1) (Nat.succ_pos n)).map h =
      empiricalOccupation (fun t => h (w t)) (n+1) (Nat.succ_pos n) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [empiricalOccupation,ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map hh (measurable_of_finite _)]
  rfl

variable {S X A : Type*} [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

theorem original_descriptor_empirical_eq
    (spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H)
    (w : ℕ → PermanssonLean.JointState S X) (n : ℕ) :
    PermanssonLean.RegimeSpecification.empiricalOccupation spec w (n+1) (Nat.succ_pos n) =
      (empiricalOccupation w (n+1) (Nat.succ_pos n)).map spec.descriptor := by
  rw [empirical_map w spec.descriptor spec.descriptor_measurable]
  rfl

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- The original frozen occupation clause under its original almost-sure
weak mode. The other Exact-GR clauses retain their separate obligations. -/
theorem original_occupation_of_invariant_descriptor
    [MetricSpace (PermanssonLean.JointState S X)]
    [CompactSpace (PermanssonLean.JointState S X)]
    [BorelSpace (PermanssonLean.JointState S X)]
    [Nonempty (PermanssonLean.JointState S X)]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H)
    (μ : ProbabilityMeasure (PermanssonLean.JointState S X))
    (hF : IsFeller M.inducedKernel) (hh : Continuous spec.descriptor)
    (cover : ∀ π : ProbabilityMeasure (PermanssonLean.JointState S X),
      M.inducedKernel ∘ₘ π.toMeasure = π.toMeasure → π.map spec.descriptor = spec.target)
    (hmode : spec.convergenceMode = PermanssonLean.ConvergenceMode.almostSureWeak _ _) :
    PermanssonLean.RegimeSpecification.IsLimitingOccupationLaw M spec μ := by
  unfold PermanssonLean.RegimeSpecification.IsLimitingOccupationLaw
  rw [hmode]
  change ∀ᵐ w ∂M.pathLaw μ.toMeasure,
    Tendsto (fun n => PermanssonLean.RegimeSpecification.empiricalOccupation spec w
      (n+1) (Nat.succ_pos n)) atTop (𝓝 spec.target)
  rw [typed_pathLaw_eq_canonical]
  have hc := empirical_descriptor_unique_ae M.inducedKernel hF μ spec.descriptor hh spec.target
    (fun π hπ => cover π ((invariant_iff_measure M.inducedKernel π).mp hπ))
  filter_upwards [hc] with w hw
  simpa only [original_descriptor_empirical_eq] using hw

end
end PermanssonResearch.MultipleLimit.CompactFeller
