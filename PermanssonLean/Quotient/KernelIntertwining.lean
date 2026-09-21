import PermanssonLean.Quotient.Compression
import PermanssonLean.Intervention.Signature
import Mathlib.Probability.Kernel.Composition.MapComap

open MeasureTheory ProbabilityTheory

namespace PermanssonLean

universe uS uX uA uSbar uXbar uAbar uK₁ uK₂ uL₁ uL₂

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {Sbar : Type uSbar} {Xbar : Type uXbar} {Abar : Type uAbar}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace Sbar] [MeasurableSpace Xbar] [MeasurableSpace Abar]

/-- Kernel intertwining through a state compression:
mapping the original next-state kernel through q equals evaluating the
compressed kernel at q(y). -/
def KernelIntertwines
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (K : Kernel (JointState S X) (JointState S X))
    (Kbar : Kernel (JointState Sbar Xbar) (JointState Sbar Xbar)) : Prop :=
  K.map Q.stateMap =
    Kbar.comap Q.stateMap Q.stateMap_measurable

theorem kernelIntertwines_apply
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (K : Kernel (JointState S X) (JointState S X))
    (Kbar : Kernel (JointState Sbar Xbar) (JointState Sbar Xbar))
    (h : KernelIntertwines Q K Kbar)
    (y : JointState S X) :
    (K y).map Q.stateMap = Kbar (Q.stateMap y) := by
  have hy := congrArg (fun κ => κ y) h
  simpa [Kernel.map_apply _ Q.stateMap_measurable,
    Kernel.comap_apply] using hy

theorem kernelIntertwines_apply_preimage
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (K : Kernel (JointState S X) (JointState S X))
    (Kbar : Kernel (JointState Sbar Xbar) (JointState Sbar Xbar))
    (h : KernelIntertwines Q K Kbar)
    (y : JointState S X)
    (C : Set (JointState Sbar Xbar))
    (hC : MeasurableSet C) :
    K y (Q.stateMap ⁻¹' C) = Kbar (Q.stateMap y) C := by
  have hy := kernelIntertwines_apply Q K Kbar h y
  have hc := congrArg (fun μ : Measure (JointState Sbar Xbar) => μ C) hy
  simpa [Measure.map_apply Q.stateMap_measurable hC] using hc

/-- Cross-state matching of two frozen intervention families. -/
structure QuotientFamilyMatching
    {M : StrategicWorldModel S X A}
    {Mbar : StrategicWorldModel Sbar Xbar Abar}
    {Component : Type uK₁} {ComponentBar : Type uK₂}
    {Label : Type uL₁} {LabelBar : Type uL₂}
    (F : InterventionFamily M Component)
    (Fbar : InterventionFamily Mbar ComponentBar)
    (J : FrozenStrategicInterventionFamily F Label)
    (Jbar : FrozenStrategicInterventionFamily Fbar LabelBar) where
  labelEquiv : Label ≃ LabelBar
  target_eq :
    ∀ l : Label,
      F.targetOf (J.intervention l).intervention.component =
        Fbar.targetOf
          (Jbar.intervention (labelEquiv l)).intervention.component

/-- Baseline and every frozen strategic intervention commute with the same
type-respecting state compression. -/
structure InterventionCompatibleKernelQuotient
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    {M : StrategicWorldModel S X A}
    {Mbar : StrategicWorldModel Sbar Xbar Abar}
    {Component : Type uK₁} {ComponentBar : Type uK₂}
    {Label : Type uL₁} {LabelBar : Type uL₂}
    (F : InterventionFamily M Component)
    (Fbar : InterventionFamily Mbar ComponentBar)
    (J : FrozenStrategicInterventionFamily F Label)
    (Jbar : FrozenStrategicInterventionFamily Fbar LabelBar) where
  matching : QuotientFamilyMatching F Fbar J Jbar
  baseline_intertwines :
    KernelIntertwines Q M.inducedKernel Mbar.inducedKernel
  intervention_intertwines :
    ∀ l : Label,
      KernelIntertwines Q
        (J.intervention l).intervention.apply.inducedKernel
        (Jbar.intervention (matching.labelEquiv l)).intervention.apply.inducedKernel

end PermanssonLean
