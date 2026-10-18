import PermanssonResearch.MultipleLimit.StationaryRandomOccupation
import PermanssonResearch.MultipleLimit.CanonicalInitialDensity
import PermanssonResearch.MultipleLimit.PolishStationaryRandomOccupation
import Mathlib.Probability.Distributions.Bernoulli

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology ENNReal

namespace PermanssonResearch.StationaryRandomTests

noncomputable section
open MultipleLimit.FiniteCanonicalPath MultipleLimit.FiniteStateOccupation
open MultipleLimit.StationaryCanonical MultipleLimit.StationaryConditional
open MultipleLimit.StationaryRandom MultipleLimit.CanonicalInitial
open PermanssonLean.ProbabilitySupport

abbrev Interval := Set.Icc (0 : ℝ) 1
def zero : Interval := ⟨0,by constructor <;> norm_num⟩
def one : Interval := ⟨1,by constructor <;> norm_num⟩
def half : Interval := ⟨1/2,by constructor <;> norm_num⟩
instance : Nonempty Interval := ⟨zero⟩
instance : CompactSpace Interval := isCompact_iff_compactSpace.mp isCompact_Icc

def identityKernel : Kernel Interval Interval := Kernel.deterministic id measurable_id
instance : IsMarkovKernel identityKernel := by unfold identityKernel; infer_instance

theorem identity_invariant (π : ProbabilityMeasure Interval) :
    identityKernel ∘ₘ π.toMeasure = π.toMeasure := by
  rw [identityKernel,Measure.deterministic_comp_eq_map]
  simp

theorem constant_point_law (y : Interval) :
    canonicalPathLaw identityKernel (Measure.dirac y) = Measure.dirac (fun _ : ℕ => y) := by
  apply measure_eq_of_prefix_maps
  apply prefix_maps_eq identityKernel
  · rw [canonical_prefix_zero,Measure.map_dirac,Measure.map_dirac]
    rfl
  · exact MultipleLimit.CanonicalKernelMarginals.canonical_transition_pair _ _
  · intro n
    rw [Measure.map_dirac,Measure.map_dirac]
    ext E hE
    rw [Measure.dirac_compProd_apply hE]
    change Measure.dirac y ((Prod.mk (Preorder.frestrictLe n (fun _ : ℕ => y))) ⁻¹' E) = _
    rw [Measure.dirac_apply' y (measurable_prodMk_left hE),Measure.dirac_apply' _ hE]
    rfl

theorem constant_path_law (π : ProbabilityMeasure Interval) :
    canonicalPathLaw identityKernel π.toMeasure = π.toMeasure.map (fun y : Interval => fun _ : ℕ => y) := by
  rw [pathLaw_eq_point_comp]
  have hk : pointPathKernel identityKernel = Kernel.deterministic
      (fun y : Interval => fun _ : ℕ => y) (by fun_prop) := by
    ext y : 1
    rw [pointPathKernel_apply,constant_point_law,Kernel.deterministic_apply]
  rw [hk,Measure.deterministic_comp_eq_map]

theorem constant_empirical (y : Interval) (n : ℕ) :
    empiricalOccupation (fun _ : ℕ => y) (n+1) (Nat.succ_pos n) =
      (⟨Measure.dirac y,by infer_instance⟩ : ProbabilityMeasure Interval) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp [empiricalOccupation,ProbabilityMeasure.toMeasure_map,Measure.map_const]

/-- For a nonergodic identity process, the actual conditional random limit
is the random point mass at Y0, not the stationary initial mixture. -/
theorem identity_randomLaw (π : ProbabilityMeasure Interval) :
    ∀ᵐ w ∂canonicalPathLaw identityKernel π.toMeasure,
      randomLaw identityKernel π w = ⟨Measure.dirac (w 0),by infer_instance⟩ := by
  have hc : ∀ᵐ w ∂canonicalPathLaw identityKernel π.toMeasure,
      Tendsto (fun n => empiricalOccupation w (n+1) (Nat.succ_pos n)) atTop
        (𝓝 (⟨Measure.dirac (w 0),by infer_instance⟩ : ProbabilityMeasure Interval)) := by
    rw [constant_path_law]
    have hc : Continuous (fun y : Interval => fun _ : ℕ => y) := by fun_prop
    have hr : MeasurableSet (Set.range (fun y : Interval => fun _ : ℕ => y)) :=
      (isCompact_range hc).isClosed.measurableSet
    have ha := ae_map_mem_range (μ := π.toMeasure) hr hc.measurable.aemeasurable
    filter_upwards [ha] with w hw
    obtain ⟨y,rfl⟩ := hw
    let ν : ProbabilityMeasure Interval := ⟨Measure.dirac y,by infer_instance⟩
    have ht : Tendsto (fun _ : ℕ => ν) atTop (𝓝 ν) := tendsto_const_nhds
    simpa only [constant_empirical] using
      ht
  filter_upwards [empirical_tendsto_randomLaw identityKernel π (identity_invariant π),hc] with w hr hd
  exact tendsto_nhds_unique hr hd

def mixedLaw : ProbabilityMeasure Interval := ⟨bernoulliMeasure zero one half,by infer_instance⟩

theorem mixed_mass_zero : mixedLaw.toMeasure {zero} = (1/2 : ℝ≥0∞) := by
  have h01 : zero ≠ one := by intro he; have := congrArg Subtype.val he; norm_num [zero,one] at this
  norm_num [mixedLaw,bernoulliMeasure,half,h01,Ne.symm h01]
  rw [← ENNReal.ofReal_coe_nnreal]
  norm_num [unitInterval.toNNReal]
  change ENNReal.ofReal (1/2 : ℝ) = (2 : ℝ≥0∞)⁻¹
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2)]
  norm_num

theorem pointLaw_ne_mixed (y : Interval) :
    (⟨Measure.dirac y,by infer_instance⟩ : ProbabilityMeasure Interval) ≠ mixedLaw := by
  intro he
  have hm := congrArg (fun ν : ProbabilityMeasure Interval => ν.toMeasure {zero}) he
  rw [mixed_mass_zero] at hm
  have hr := congrArg ENNReal.toReal hm
  by_cases hy : y = zero
  · subst y
    norm_num at hr
  · norm_num [hy,Ne.symm hy] at hr

example : ∀ᵐ w ∂canonicalPathLaw identityKernel mixedLaw.toMeasure,
    randomLaw identityKernel mixedLaw w ≠ mixedLaw := by
  filter_upwards [identity_randomLaw mixedLaw] with w hw
  rw [hw]
  exact pointLaw_ne_mixed _

/-- The density statement concerns whole infinite path measures. -/
example (μ π : ProbabilityMeasure Interval) (h : μ.toMeasure ≪ π.toMeasure) :
    canonicalPathLaw identityKernel μ.toMeasure =
      (canonicalPathLaw identityKernel π.toMeasure).withDensity
        (fun w : ℕ → Interval => μ.toMeasure.rnDeriv π.toMeasure (w 0)) :=
  pathLaw_eq_withDensity identityKernel μ.toMeasure π.toMeasure h

def realIdentity : Kernel ℝ ℝ := Kernel.deterministic id measurable_id
instance : IsMarkovKernel realIdentity := by unfold realIdentity; infer_instance

/-- The general stationary theorem also applies to the noncompact Polish
state space R, without a compactness or Feller premise. -/
example (π : ProbabilityMeasure ℝ) :
    ∀ᵐ w ∂canonicalPathLaw realIdentity π.toMeasure,
      Tendsto (fun n => empiricalOccupation w (n+1) (Nat.succ_pos n)) atTop
        (𝓝 (randomLaw realIdentity π w)) := by
  apply MultipleLimit.PolishStationaryRandom.empirical_tendsto_randomLaw
  rw [realIdentity,Measure.deterministic_comp_eq_map]
  simp

end
end PermanssonResearch.StationaryRandomTests
