import PermanssonLean.Intervention.FrozenFamily

namespace PermanssonLean

universe uS uX uA uK uL₁ uL₂

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

/-- Equation (18a): baseline induced kernel together with the family of
post-intervention induced kernels. -/
structure InterventionKernelSignature
    (Y : Type uS) [MeasurableSpace Y]
    (Label : Type uL₁) where
  baseline : Kernel Y Y
  intervened : Label → Kernel Y Y

namespace FrozenStrategicInterventionFamily

/-- Kernel signature of a frozen family. -/
noncomputable def signature
    {M : StrategicWorldModel S X A}
    {Component : Type uK}
    {Label : Type uL₁}
    {F : InterventionFamily M Component}
    (J : FrozenStrategicInterventionFamily F Label) :
    InterventionKernelSignature (JointState S X) Label where
  baseline := M.inducedKernel
  intervened := fun l => (J.intervention l).intervention.apply.inducedKernel

end FrozenStrategicInterventionFamily

namespace InterventionKernelSignature

/-- Equality of signatures under a frozen relabeling. -/
def Matches
    {Y : Type uS} [MeasurableSpace Y]
    {Label₁ : Type uL₁} {Label₂ : Type uL₂}
    (σ₁ : InterventionKernelSignature Y Label₁)
    (σ₂ : InterventionKernelSignature Y Label₂)
    (φ : Label₁ ≃ Label₂) : Prop :=
  σ₁.baseline = σ₂.baseline ∧
    ∀ l : Label₁, σ₁.intervened l = σ₂.intervened (φ l)

theorem matches_baseline
    {Y : Type uS} [MeasurableSpace Y]
    {Label₁ : Type uL₁} {Label₂ : Type uL₂}
    {σ₁ : InterventionKernelSignature Y Label₁}
    {σ₂ : InterventionKernelSignature Y Label₂}
    {φ : Label₁ ≃ Label₂}
    (h : Matches σ₁ σ₂ φ) :
    σ₁.baseline = σ₂.baseline :=
  h.1

theorem matches_intervened
    {Y : Type uS} [MeasurableSpace Y]
    {Label₁ : Type uL₁} {Label₂ : Type uL₂}
    {σ₁ : InterventionKernelSignature Y Label₁}
    {σ₂ : InterventionKernelSignature Y Label₂}
    {φ : Label₁ ≃ Label₂}
    (h : Matches σ₁ σ₂ φ)
    (l : Label₁) :
    σ₁.intervened l = σ₂.intervened (φ l) :=
  h.2 l

end InterventionKernelSignature

/-- A source-faithful certificate of intervention-compatible equivalence:
target-preserving label matching plus equality of the complete kernel
signatures under that matching. -/
structure InterventionCompatibleFamilyEquivalence
    {M₁ M₂ : StrategicWorldModel S X A}
    {Component₁ : Type uK} {Component₂ : Type uK}
    {Label₁ : Type uL₁} {Label₂ : Type uL₂}
    (F₁ : InterventionFamily M₁ Component₁)
    (F₂ : InterventionFamily M₂ Component₂)
    (J₁ : FrozenStrategicInterventionFamily F₁ Label₁)
    (J₂ : FrozenStrategicInterventionFamily F₂ Label₂) where
  matching : FrozenFamilyMatching F₁ F₂ J₁ J₂
  signatures_match :
    InterventionKernelSignature.Matches
      J₁.signature
      J₂.signature
      matching.labelEquiv

end PermanssonLean
