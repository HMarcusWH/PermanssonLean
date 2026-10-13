import PermanssonResearch.MultipleLimit.ExactGRObservedEventExtremality
import PermanssonResearch.MultipleLimit.FiniteObservedBadClassReachability
import PermanssonResearch.MultipleLimit.FiniteObservedUniformMargin
import Mathlib.Tactic

/-!
# C8-05 — opposing recurrent destinations, exact effects and original PR

A baseline ORIGINAL Exact Generated Regime with literal almostSureWeak
mode has a 0/1 frozen eventual-true event probability throughout its
original basin. Under a genuine typed admissible strategic intervention,
the original constitution effect therefore equals exactly the probability
of selecting a recurrent class opposing the baseline target. The original
nonempty finite comparison set attains the same minimum. Positive
opposition is classified by G1/G2 positive-edge reachability.

No new PR definition, intervention admissibility assumption, cross-kernel
class-selector identity or empirical efficacy claim is introduced.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace OppositeClassConstitutiveMargin

set_option autoImplicit false
attribute [local instance] Classical.propDecidable

open KernelCommunication
open PermanssonLean
open PermanssonLean.RegimeSpecification
open FiniteCanonicalPath
open CanonicalClassSelector
open FiniteObservedClassSupport
open FiniteObservedSupportReachability
open FiniteObservedBadClassReachability
open FiniteObservedEventMass
open TypedObservedEventConstitution
open FiniteObservedUniformMargin
open ExactGRObservedEventExtremality
open FrozenObservedEvent

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [Nonempty Y]
variable [DecidableEq Y] [StandardBorelSpace Y]

/-- The recurrent classes of the INTERVENED kernel opposing the
baseline target: bad classes when target is delta_true; good otherwise. -/
noncomputable def opposingClassMass
    (L : Kernel Y Y) [IsMarkovKernel L]
    (h : Y → Bool) (ν : ProbabilityMeasure Bool) (y : Y) : ℝ≥0∞ :=
  if ν = diracProba true then
    ∑ i ∈ badRecurrentRepresentatives L h,
      canonicalPathLaw L (Measure.dirac y)
        ((selectedRepresentative L) ⁻¹' ({i} : Set Y))
  else
    pointGoodMass L h y

/-- Strictly qualitative opposite-recurrent graph reachability.
Class labels and class representatives are computed from L itself. -/
def OpposingClassReachable
    (L : Kernel Y Y) [IsMarkovKernel L]
    (h : Y → Bool) (ν : ProbabilityMeasure Bool) (y : Y) : Prop :=
  if ν = diracProba true then
    ∃ i ∈ badRecurrentRepresentatives L h, Reachable L y i
  else
    ∃ i ∈ goodRecurrentRepresentatives L h, Reachable L y i

/-- The class-weight mass is always an ACTUAL event probability,
of the eventual-true event or its complement. -/
theorem opposingMass_eq_event_probability
    (L : Kernel Y Y) [IsMarkovKernel L]
    (h : Y → Bool) (ν : ProbabilityMeasure Bool) (y : Y) :
    opposingClassMass L h ν y =
      if ν = diracProba true then
        (canonicalPathLaw L (Measure.dirac y))
          (eventuallyObserved h true)ᶜ
      else
        (canonicalPathLaw L (Measure.dirac y))
          (eventuallyObserved h true) := by
  by_cases ht : ν = diracProba true
  · simp only [opposingClassMass, if_pos ht]
    exact (eventual_true_complement_mass_eq_bad_sum L h
      (diracProba y)).symm
  · simp only [opposingClassMass, if_neg ht]
    exact pointGoodMass_eq_event_probability L h y

/-- Opposing mass is finite, normalized, and nonzero iff its real
value is positive. No floating-point positivity cutoff. -/
theorem opposingMass_ne_top
    (L : Kernel Y Y) [IsMarkovKernel L]
    (h : Y → Bool) (ν : ProbabilityMeasure Bool) (y : Y) :
    opposingClassMass L h ν y ≠ ⊤ := by
  rw [opposingMass_eq_event_probability]
  split_ifs <;> exact measure_ne_top _ _

/-- G1/G2 together: exact opposing mass is positive iff some
opposite recurrent representative is positive-edge reachable. -/
theorem opposingMass_real_pos_iff_reachable
    (L : Kernel Y Y) [IsMarkovKernel L]
    (h : Y → Bool) (ν : ProbabilityMeasure Bool) (y : Y) :
    0 < (opposingClassMass L h ν y).toReal ↔
      OpposingClassReachable L h ν y := by
  have hfinite := opposingMass_ne_top L h ν y
  have hbridge :
      (0 : ℝ) < (opposingClassMass L h ν y).toReal ↔
        (0 : ℝ≥0∞) < opposingClassMass L h ν y := by
    constructor
    · intro hreal
      by_contra hnot
      have hzero : opposingClassMass L h ν y = 0 :=
        le_antisymm (le_of_not_gt hnot) bot_le
      simpa [hzero] using hreal
    · intro hpos
      exact ENNReal.toReal_pos hpos.ne' hfinite
  rw [hbridge, opposingMass_eq_event_probability]
  by_cases ht : ν = diracProba true
  · simp only [if_pos ht, OpposingClassReachable]
    simpa only [if_pos ht] using
      (eventual_true_complement_positive_iff_reachable_bad L h y)
  · simp only [if_neg ht, OpposingClassReachable]
    simpa only [if_neg ht] using
      (eventual_true_positive_iff_reachable_good L h y)

variable {S X A : Type*}
variable [MeasurableSpace S] [MeasurableSpace X]
variable [MeasurableSpace A]
variable [TopologicalSpace S] [TopologicalSpace X]
variable [Fintype (JointState S X)] [Nonempty (JointState S X)]
variable [DecidableEq (JointState S X)]
variable [MeasurableSingletonClass (JointState S X)]
variable [DiscreteTopology (JointState S X)]
variable [OpensMeasurableSpace (JointState S X)]
variable [StandardBorelSpace (JointState S X)]

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- G4: original real-valued constitutive effect equals the
opposite-class probability in the TRUE intervened kernel, under
independent baseline Exact GR and the literal convergence-mode gate. -/
theorem effect_eq_opposingMass
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    (m : Measure (JointState S X))
    {Component : Type*}
    (F : InterventionFamily M Component)
    (J : AdmissibleStrategicIntervention F)
    (hGR : IsExactGeneratedRegime M spec m)
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) Bool)
    (y : JointState S X) (hy : y ∈ spec.basin) :
    constitutiveEffect M
      (eventuallyObservedProperty spec.descriptor true) J y =
      (opposingClassMass J.intervention.apply.inducedKernel
        spec.descriptor spec.target y).toReal := by
  let L := J.intervention.apply.inducedKernel
  let a := pointGoodMass M.inducedKernel spec.descriptor y
  let b := pointGoodMass L spec.descriptor y
  have hbase : a =
      if spec.target = diracProba true then 1 else 0 := by
    change pointGoodMass M.inducedKernel spec.descriptor y = _
    rw [pointGoodMass_eq_event_probability]
    exact baseline_event_probability_extremal
      M spec m hGR hmode y hy
  have hb : b ≤ (1 : ℝ≥0∞) := by
    change pointGoodMass L spec.descriptor y ≤ 1
    rw [pointGoodMass_eq_event_probability]
    calc
      (canonicalPathLaw L (Measure.dirac y))
        (eventuallyObserved spec.descriptor true) ≤
          (canonicalPathLaw L (Measure.dirac y)) Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hfinite : b ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hb
  have hbReal : b.toReal ≤ (1 : ℝ) := by
    have hb' := (ENNReal.toReal_le_toReal
      hfinite ENNReal.one_ne_top).2 hb
    simpa using hb'
  have hb0 : 0 ≤ b.toReal := ENNReal.toReal_nonneg
  rw [effect_eq_abs_goodMass_difference M F J spec.descriptor y]
  change |a.toReal - b.toReal| =
    (opposingClassMass L spec.descriptor spec.target y).toReal
  by_cases ht : spec.target = diracProba true
  · have ha : a.toReal = 1 := by
      rw [hbase, if_pos ht]
      rfl
    rw [ha, abs_of_nonneg (sub_nonneg.mpr hbReal)]
    have hmeas :
        MeasurableSet (eventuallyObserved spec.descriptor true) :=
      eventuallyObserved_measurable spec.descriptor true
        (measurable_of_finite spec.descriptor)
    have hcomp :
        (canonicalPathLaw L (Measure.dirac y))
          (eventuallyObserved spec.descriptor true)ᶜ =
          1 - (canonicalPathLaw L (Measure.dirac y))
            (eventuallyObserved spec.descriptor true) :=
      prob_compl_eq_one_sub hmeas
    calc
      1 - b.toReal =
          (1 - b).toReal := by
        rw [ENNReal.toReal_sub_of_le hb ENNReal.one_ne_top]
        simp
      _ = ((canonicalPathLaw L (Measure.dirac y))
        (eventuallyObserved spec.descriptor true)ᶜ).toReal := by
        rw [hcomp]
        rw [← pointGoodMass_eq_event_probability L
          spec.descriptor y]
      _ = (opposingClassMass L spec.descriptor spec.target y).toReal := by
        rw [opposingMass_eq_event_probability, if_pos ht]
  · have ha : a.toReal = 0 := by
      rw [hbase, if_neg ht]
      rfl
    rw [ha]
    simp only [zero_sub, abs_neg, abs_of_nonneg hb0]
    rw [opposingMass_eq_event_probability, if_neg ht]
    exact congrArg ENNReal.toReal
      (pointGoodMass_eq_event_probability L spec.descriptor y)

/-- G5: the actual ORIGINAL uniform margin is attained at a
comparison state and equals the corresponding exact opposing mass;
every other comparison effect is at least that value. -/
theorem finite_opposingMargin_attained
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    (m : Measure (JointState S X))
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (hGR : IsExactGeneratedRegime M spec m)
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) Bool) :
    ∃ y ∈ B₁.states,
      constitutiveMargin M spec F
        (eventuallyObservedProperty spec.descriptor true) B₁ J =
        (opposingClassMass J.intervention.apply.inducedKernel
          spec.descriptor spec.target y).toReal ∧
      ∀ z ∈ B₁.states,
        constitutiveMargin M spec F
          (eventuallyObservedProperty spec.descriptor true) B₁ J ≤
        (opposingClassMass J.intervention.apply.inducedKernel
          spec.descriptor spec.target z).toReal := by
  obtain ⟨y, hy, hmin⟩ := finite_margin_attained M spec F
    (eventuallyObservedProperty spec.descriptor true) B₁ J
  refine ⟨y, hy, ?_, ?_⟩
  · calc
      constitutiveMargin M spec F
          (eventuallyObservedProperty spec.descriptor true) B₁ J =
        constitutiveEffect M
          (eventuallyObservedProperty spec.descriptor true) J y := hmin
      _ = (opposingClassMass J.intervention.apply.inducedKernel
          spec.descriptor spec.target y).toReal :=
        effect_eq_opposingMass M spec m F J hGR hmode y
          (B₁.states_subset_basin hy)
  · intro z hz
    calc
      constitutiveMargin M spec F
        (eventuallyObservedProperty spec.descriptor true) B₁ J ≤
        constitutiveEffect M
          (eventuallyObservedProperty spec.descriptor true) J z :=
        constitutiveMargin_le_effect M spec F
          (eventuallyObservedProperty spec.descriptor true) B₁ J hz
      _ = (opposingClassMass J.intervention.apply.inducedKernel
          spec.descriptor spec.target z).toReal :=
        effect_eq_opposingMass M spec m F J hGR hmode z
          (B₁.states_subset_basin hz)

/-- G6: the ORIGINAL unweakened uniform relative PR definition
iff baseline ORIGINAL Exact GR and every frozen comparison start
has a finite positive-edge path to an OPPOSING recurrent class
of the actual intervened kernel. This uses a separately supplied
literal convergence-mode equality. -/
theorem original_uniformRelativePR_iff_opposingReachability
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    (m : Measure (JointState S X))
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) Bool) :
    IsUniformGeneralizedPermanssonRegimeRelative M spec m F
      (eventuallyObservedProperty spec.descriptor true) B₁ J ↔
      IsExactGeneratedRegime M spec m ∧
        ∀ y ∈ B₁.states,
          OpposingClassReachable J.intervention.apply.inducedKernel
            spec.descriptor spec.target y := by
  constructor
  · rintro ⟨hGR, hUniform⟩
    refine ⟨hGR, ?_⟩
    have hpos :=
      (uniformlyConstitutive_iff_margin_pos M spec F
        (eventuallyObservedProperty spec.descriptor true) B₁ J).mp
          hUniform
    have hpoint := (finite_margin_pos_iff_pointwise M spec F
      (eventuallyObservedProperty spec.descriptor true) B₁ J).mp hpos
    intro y hy
    have heffect := hpoint y hy
    rw [effect_eq_opposingMass M spec m F J hGR hmode y
      (B₁.states_subset_basin hy)] at heffect
    exact (opposingMass_real_pos_iff_reachable
      J.intervention.apply.inducedKernel
      spec.descriptor spec.target y).mp heffect
  · rintro ⟨hGR, hOpp⟩
    refine ⟨hGR, ?_⟩
    apply (uniformlyConstitutive_iff_margin_pos M spec F
      (eventuallyObservedProperty spec.descriptor true) B₁ J).mpr
    apply (finite_margin_pos_iff_pointwise M spec F
      (eventuallyObservedProperty spec.descriptor true) B₁ J).mpr
    intro y hy
    rw [effect_eq_opposingMass M spec m F J hGR hmode y
      (B₁.states_subset_basin hy)]
    exact (opposingMass_real_pos_iff_reachable
      J.intervention.apply.inducedKernel
      spec.descriptor spec.target y).mpr (hOpp y hy)

end OppositeClassConstitutiveMargin
end MultipleLimit
end PermanssonResearch
