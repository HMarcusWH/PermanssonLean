import PermanssonResearch.ConstitutiveQuasi.Certificate
import PermanssonResearch.ConstitutiveQuasi.BoundedTV

/-!
# CQ-1 model and output error accounting

The approximation profile is tied to the actual approximate baseline and
strategic intervention finite-prefix expectations. No arbitrary profile is
called model-correct without these explicit output error witnesses.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace PermanssonResearch
namespace ConstitutiveQuasi

universe uS uX uA uH uC
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- The finite-prefix property of an intervened model is exactly the frozen
intervention-property API evaluated on the same path law. -/
theorem finitePathExpectation_eq_intervenedProperty
    {M : PermanssonLean.StrategicWorldModel S X A}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    (J : PermanssonLean.AdmissibleStrategicIntervention F)
    (y : PermanssonLean.JointState S X) (L : ℕ)
    (f : FinitePathProperty (PermanssonLean.JointState S X) L) :
    f.fromKernel L J.intervention.apply.inducedKernel y =
      PermanssonLean.RegimeSpecification.intervenedPropertyValue
        (f.toRegimeProperty L) J.intervention y := by
  simpa only [PermanssonLean.RegimeSpecification.baselinePropertyValue,
    PermanssonLean.RegimeSpecification.intervenedPropertyValue] using
    (finitePathExpectation_eq_baselineProperty
      J.intervention.apply y L f)

/-- Audited model and output errors: both models share the original P by
the StrategicApproximationPair type, and approximation profiles are bound to
their *actual* finite-horizon expectations on the same frozen B₁. -/
structure FinitePathModelErrors
    (M : PermanssonLean.StrategicWorldModel S X A)
    (spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H)
    {Component : Type uC}
    (F : PermanssonLean.InterventionFamily M Component)
    (B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec)
    (J : PermanssonLean.AdmissibleStrategicIntervention F)
    (pair : StrategicApproximationPair M F J)
    (L : ℕ) (f : FinitePathProperty (PermanssonLean.JointState S X) L)
    (profile : PermanssonLean.RegimeSpecification.PerturbedPropertyProfile
      (PermanssonLean.JointState S X) ℝ)
    (δ₀ δJ b₀ bJ : ℝ) : Prop where
  δ₀_nonneg : 0 ≤ δ₀
  δ₀_le_one : δ₀ ≤ 1
  δJ_nonneg : 0 ≤ δJ
  δJ_le_one : δJ ≤ 1
  b₀_nonneg : 0 ≤ b₀
  bJ_nonneg : 0 ≤ bJ
  tv_baseline :
    PermanssonLean.ProbabilitySupport.HasUniformEventTVBound
      M.inducedKernel pair.approx.inducedKernel δ₀
  tv_intervention :
    PermanssonLean.ProbabilitySupport.HasUniformEventTVBound
      J.intervention.apply.inducedKernel
      pair.approxIntervention.intervention.apply.inducedKernel δJ
  output_baseline :
    ∀ y ∈ B₁.states,
      dist (f.fromKernel L pair.approx.inducedKernel y) (profile.baseline y) ≤ b₀
  output_intervention :
    ∀ y ∈ B₁.states,
      dist (f.fromKernel L pair.approxIntervention.intervention.apply.inducedKernel y)
        (profile.intervention y) ≤ bJ

/-- Kernel TV budgets and separately verified numerical output errors satisfy
the original Proposition 5.2 error interface exactly. -/
theorem FinitePathModelErrors.toConstitutiveOutputErrors
    [MeasurableSpace.CountableOrCountablyGenerated
      (PermanssonLean.JointState S X) (PermanssonLean.JointState S X)]
    {M : PermanssonLean.StrategicWorldModel S X A}
    {spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    {pair : StrategicApproximationPair M F J}
    {L : ℕ} {f : FinitePathProperty (PermanssonLean.JointState S X) L}
    {profile : PermanssonLean.RegimeSpecification.PerturbedPropertyProfile
      (PermanssonLean.JointState S X) ℝ}
    {δ₀ δJ b₀ bJ : ℝ}
    (h : FinitePathModelErrors M spec F B₁ J pair L f profile δ₀ δJ b₀ bJ) :
    PermanssonLean.RegimeSpecification.HasConstitutiveOutputErrors
      M spec F (f.toRegimeProperty L) B₁ J profile
      (PermanssonLean.ProbabilitySupport.geometricTVEnvelope δ₀ L + b₀)
      (PermanssonLean.ProbabilitySupport.geometricTVEnvelope δJ L + bJ) := by
  refine ⟨add_nonneg
      (PermanssonLean.ProbabilitySupport.geometricTVEnvelope_nonneg
        h.δ₀_nonneg h.δ₀_le_one L) h.b₀_nonneg,
    add_nonneg
      (PermanssonLean.ProbabilitySupport.geometricTVEnvelope_nonneg
        h.δJ_nonneg h.δJ_le_one L) h.bJ_nonneg, ?_, ?_⟩
  · intro y hy
    have htv := finitePathExpectation_abs_le_geometric M.inducedKernel
      pair.approx.inducedKernel h.δ₀_nonneg h.δ₀_le_one
      h.tv_baseline y L f
    have hdist :
        dist
          (PermanssonLean.RegimeSpecification.baselinePropertyValue
            (f.toRegimeProperty L) M y)
          (f.fromKernel L pair.approx.inducedKernel y) ≤
          PermanssonLean.ProbabilitySupport.geometricTVEnvelope δ₀ L := by
      rw [← finitePathExpectation_eq_baselineProperty M y L f, Real.dist_eq]
      exact htv
    exact (dist_triangle _ _ _).trans
      (add_le_add hdist (h.output_baseline y hy))
  · intro y hy
    have htv := finitePathExpectation_abs_le_geometric
      J.intervention.apply.inducedKernel
      pair.approxIntervention.intervention.apply.inducedKernel
      h.δJ_nonneg h.δJ_le_one h.tv_intervention y L f
    have hdist :
        dist
          (PermanssonLean.RegimeSpecification.intervenedPropertyValue
            (f.toRegimeProperty L) J.intervention y)
          (f.fromKernel L pair.approxIntervention.intervention.apply.inducedKernel y) ≤
          PermanssonLean.ProbabilitySupport.geometricTVEnvelope δJ L := by
      rw [← finitePathExpectation_eq_intervenedProperty J y L f, Real.dist_eq]
      exact htv
    exact (dist_triangle _ _ _).trans
      (add_le_add hdist (h.output_intervention y hy))

end ConstitutiveQuasi
end PermanssonResearch
