import PermanssonResearch.Perturbation.PrimitiveMargin
import PermanssonResearch.Perturbation.PrimitiveLipschitz
import PermanssonResearch.ConstitutiveQuasi.AdversarialExamples
import PermanssonLean.Examples.QSDCounterexample

/-!
# A2 destructive theorem witnesses (compiled, not merely Python checks)

These are source-checked non-implication witnesses:
* a common point-start at T=0 cannot have a positive finite-score effect;
* altered structural P cannot be laundered into the older same-P CQ-1 pair;
* an actual finite typed QSD witness does not imply uniform finite retention.

The small-leak exact-invariance counterexample in the v0.2.0 plan remains an
independent mathematical nonclaim: no A2 theorem may transfer Exact GR from
positive one-step TV proximity alone.
-/

namespace PermanssonResearch
namespace Perturbation

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

universe uS uX uA uH uC

variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]

/-- Zero transitions record only the common initial state. The action/world/
update primitives cannot affect the same point-started finite-prefix score. -/
theorem zeroHorizon_score_independent
    (M N : PermanssonLean.StrategicWorldModel S X A)
    (y : PermanssonLean.JointState S X)
    (f : PermanssonResearch.ConstitutiveQuasi.FinitePathProperty
      (PermanssonLean.JointState S X) 0) :
    f.fromKernel 0 M.inducedKernel y =
      f.fromKernel 0 N.inducedKernel y :=
  PermanssonResearch.ConstitutiveQuasi.expected_zero_independent_of_kernel
    M.inducedKernel N.inducedKernel y f

/-- The existing CQ-1 gate is nontrivial: no positive finite-con-stitutive
certificate exists at horizon zero under a common point start. -/
theorem noZeroHorizonConstitutiveCertificate
    (M : PermanssonLean.StrategicWorldModel S X A)
    (spec : PermanssonLean.RegimeSpecification
      (PermanssonLean.JointState S X) H)
    {Component : Type uC}
    (F : PermanssonLean.InterventionFamily M Component)
    (B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec)
    (J : PermanssonLean.AdmissibleStrategicIntervention F)
    (f : PermanssonResearch.ConstitutiveQuasi.FinitePathProperty
      (PermanssonLean.JointState S X) 0)
    (eta : ℝ≥0∞) (κ : ℝ) :
    ¬ PermanssonResearch.ConstitutiveQuasi.FiniteConstitutiveCertificate
      M spec F B₁ J 0 f eta κ :=
  PermanssonResearch.ConstitutiveQuasi.noZeroHorizonFiniteConstitutiveCertificate
    M spec F B₁ J f eta κ

/-- Existing exact typed counterexample: even a legitimate QSD is not a
certificate of region-wide one-step finite persistence. -/
theorem qsd_is_not_uniform_persistence_witness :
    PermanssonLean.RegimeSpecification.IsQuasiStationaryDistribution
      PermanssonLean.QSDCounterexample.model
      PermanssonLean.QSDCounterexample.spec
      PermanssonLean.QSDCounterexample.qsdLaw 1 ∧
    ¬ PermanssonLean.RegimeSpecification.IsFinitePersistent
      PermanssonLean.QSDCounterexample.model
      PermanssonLean.QSDCounterexample.spec 1 0 :=
  PermanssonLean.QSDCounterexample.qsd_does_not_imply_uniform_finitePersistence

end Perturbation
end PermanssonResearch
