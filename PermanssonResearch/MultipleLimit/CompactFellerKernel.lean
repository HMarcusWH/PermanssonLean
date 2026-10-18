import PermanssonResearch.MultipleLimit.CanonicalBoundedInnovations
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! Compact-Feller weak topology and invariant laws. All invariance
statements refer to actual composition with the supplied Markov kernel. -/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace PermanssonResearch.MultipleLimit.CompactFeller

set_option autoImplicit false
noncomputable section

open CanonicalBoundedInnovations

variable {Y : Type*} [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable [Nonempty Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

def IsFeller : Prop := ∀ f : C(Y,ℝ), Continuous (predict K f)

def operator (hF : IsFeller K) (f : C(Y,ℝ)) : C(Y,ℝ) := ⟨predict K f,hF f⟩

def step (π : ProbabilityMeasure Y) : ProbabilityMeasure Y := ⟨K ∘ₘ π.toMeasure,by infer_instance⟩

def Invariant (π : ProbabilityMeasure Y) : Prop := step K π = π

theorem invariant_iff_measure (π : ProbabilityMeasure Y) :
    Invariant K π ↔ K ∘ₘ π.toMeasure = π.toMeasure := by
  constructor
  · intro h; exact congrArg ProbabilityMeasure.toMeasure h
  · intro h; exact ProbabilityMeasure.toMeasure_injective h

theorem continuousMap_integrable (f : C(Y,ℝ)) (ν : Measure Y) [IsFiniteMeasure ν] :
    Integrable f ν := by
  apply Integrable.of_bound f.continuous.measurable.aestronglyMeasurable ‖f‖
  exact ae_of_all _ f.norm_coe_le_norm

theorem integral_step (π : ProbabilityMeasure Y) (f : C(Y,ℝ)) :
    (∫ y, f y ∂(step K π).toMeasure) = ∫ y, predict K f y ∂π.toMeasure := by
  change (∫ y, f y ∂(K ∘ₘ π.toMeasure)) = _
  rw [Measure.comp_eq_comp_const_apply]
  rw [Kernel.integral_comp (continuousMap_integrable f _)]
  rfl

theorem step_continuous (hF : IsFeller K) : Continuous (step K) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro f
  simpa only [integral_step,operator,ContinuousMap.coe_mk] using
    ProbabilityMeasure.continuous_integral_continuousMap (operator K hF f)

theorem invariant_set_closed (hF : IsFeller K) : IsClosed {π | Invariant K π} :=
  isClosed_eq (step_continuous K hF) continuous_id

def residual (π : ProbabilityMeasure Y) (f : C(Y,ℝ)) : ℝ :=
  (∫ y, f y ∂(step K π).toMeasure) - ∫ y, f y ∂π.toMeasure

theorem residual_eq_predict (π : ProbabilityMeasure Y) (f : C(Y,ℝ)) :
    residual K π f = (∫ y, predict K f y ∂π.toMeasure) - ∫ y, f y ∂π.toMeasure := by
  rw [residual,integral_step]

theorem residual_continuous (hF : IsFeller K) (f : C(Y,ℝ)) :
    Continuous (fun π => residual K π f) :=
  ((ProbabilityMeasure.continuous_integral_continuousMap f).comp (step_continuous K hF)).sub
    (ProbabilityMeasure.continuous_integral_continuousMap f)

theorem invariant_iff_residual_zero (π : ProbabilityMeasure Y) :
    Invariant K π ↔ ∀ f : C(Y,ℝ), residual K π f = 0 := by
  constructor
  · intro h f
    change step K π = π at h
    rw [residual,h,sub_self]
  · intro h
    apply ProbabilityMeasure.toMeasure_injective
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    have hz := h (⟨f,f.continuous⟩ : C(Y,ℝ))
    exact sub_eq_zero.mp hz

theorem integral_test_bound (π : ProbabilityMeasure Y) (f : C(Y,ℝ)) :
    |∫ y, f y ∂π.toMeasure| ≤ ‖f‖ := by
  simpa [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const
    (μ := π.toMeasure) (ae_of_all _ f.norm_coe_le_norm)

/-- The same uniform continuity bound holds for every probability law;
it therefore survives an uncountable family of continuous test functions. -/
theorem residual_test_lipschitz (π : ProbabilityMeasure Y) (f g : C(Y,ℝ)) :
    |residual K π f-residual K π g| ≤ 2*‖f-g‖ := by
  have he : residual K π f-residual K π g =
      (∫ y, (f-g) y ∂(step K π).toMeasure) - ∫ y, (f-g) y ∂π.toMeasure := by
    simp only [residual,ContinuousMap.sub_apply]
    rw [integral_sub (continuousMap_integrable f _) (continuousMap_integrable g _),
      integral_sub (continuousMap_integrable f _) (continuousMap_integrable g _)]
    ring
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add (integral_test_bound (step K π) (f-g))
    (integral_test_bound π (f-g))).trans_eq (by ring))

/-- A countable norm-dense class suffices simultaneously. No countable
supnorm density on a noncompact `C_b` space is asserted. -/
theorem residual_tendsto_of_dense (L : ℕ → ProbabilityMeasure Y)
    (d : ℕ → C(Y,ℝ)) (hd : DenseRange d)
    (h : ∀ k, Tendsto (fun n => residual K (L n) (d k)) atTop (𝓝 0)) (f : C(Y,ℝ)) :
    Tendsto (fun n => residual K (L n) f) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k,hk⟩ := hd.exists_dist_lt f (show 0 < ε/4 by positivity)
  have hkn : ‖f-d k‖ < ε/4 := by simpa only [dist_eq_norm] using hk
  obtain ⟨N,hN⟩ := (Metric.tendsto_atTop.mp (h k)) (ε/2) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hv : |residual K (L n) (d k)| < ε/2 := by
    simpa only [Real.dist_eq,sub_zero] using hN n hn
  have hl := residual_test_lipschitz K (L n) f (d k)
  have ha : |residual K (L n) f| ≤ |residual K (L n) f-residual K (L n) (d k)| +
      |residual K (L n) (d k)| := by
    simpa only [sub_add_cancel] using abs_add_le
      (residual K (L n) f-residual K (L n) (d k)) (residual K (L n) (d k))
  have hb : |residual K (L n) f| < ε := by linarith
  simpa only [Real.dist_eq,sub_zero] using hb

/-- Every weak cluster point of laws with vanishing Markov residuals is
invariant. Feller continuity is used precisely at passage to that limit. -/
theorem cluster_invariant (hF : IsFeller K) (L : ℕ → ProbabilityMeasure Y)
    (h : ∀ f : C(Y,ℝ), Tendsto (fun n => residual K (L n) f) atTop (𝓝 0))
    (π : ProbabilityMeasure Y) (hc : MapClusterPt π atTop L) : Invariant K π := by
  rw [invariant_iff_residual_zero]
  intro f
  have hp := hc.continuousAt_comp (residual_continuous K hF f).continuousAt
  have hl : Filter.map ((fun π => residual K π f) ∘ L) atTop ≤ 𝓝 (0 : ℝ) := h f
  exact eq_of_nhds_neBot (hp.clusterPt.mono hl)

/-- Compactness gives convergence to the predeclared closed invariant
family in the weak neighborhood-of-set sense, without choosing one limit. -/
theorem tendsto_invariant_family (hF : IsFeller K) (L : ℕ → ProbabilityMeasure Y)
    (h : ∀ f : C(Y,ℝ), Tendsto (fun n => residual K (L n) f) atTop (𝓝 0)) :
    Tendsto L atTop (𝓝ˢ {π | Invariant K π}) :=
  isCompact_univ.tendsto_nhdsSet_of_mapClusterPt (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
    (fun π _ hc => cluster_invariant K hF L h π hc)

theorem tendsto_unique_invariant (hF : IsFeller K) (L : ℕ → ProbabilityMeasure Y)
    (h : ∀ f : C(Y,ℝ), Tendsto (fun n => residual K (L n) f) atTop (𝓝 0))
    (π : ProbabilityMeasure Y) (hu : ∀ ν, Invariant K ν → ν = π) :
    Tendsto L atTop (𝓝 π) :=
  isCompact_univ.tendsto_nhds_of_unique_mapClusterPt (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
    (fun ν _ hc => hu ν (cluster_invariant K hF L h ν hc))

end
end PermanssonResearch.MultipleLimit.CompactFeller
