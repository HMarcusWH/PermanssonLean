import PermanssonResearch.MultiAgent.MeasurableFiniteProduct

namespace PermanssonResearch.MultiAgent.MeasurableProduct

open MeasureTheory ProbabilityTheory Set PermanssonLean PermanssonLean.RegimeSpecification
open scoped ENNReal ProbabilityTheory

noncomputable section

universe uI u0 uS uX uA
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable {S0 : Type u0} {S : I → Type uS} {X : Type uX} {A : I → Type uA}
variable [MeasurableSpace S0] [∀ i, MeasurableSpace (S i)]
variable [MeasurableSpace X] [∀ i, MeasurableSpace (A i)]

def closedLoop (G : FiniteProduct.Generator S0 S X A) (i : I)
    (r : FiniteProduct.Mechanism S0 S X A i) : FiniteProduct.Generator S0 S X A :=
  {G with component := Function.update G.component i r}

def openLoop (G : FiniteProduct.Generator S0 S X A) (i : I)
    (r : FiniteProduct.Mechanism S0 S X A i)
    (anchor : ∀ j, FiniteProduct.Mechanism S0 S X A j) : FiniteProduct.Generator S0 S X A :=
  {G with component := Function.update anchor i r}

theorem closedLoop_treated (G : FiniteProduct.Generator S0 S X A) (i : I)
    (r : FiniteProduct.Mechanism S0 S X A i) : (closedLoop G i r).component i = r := by
  simp [closedLoop]

theorem closedLoop_other (G : FiniteProduct.Generator S0 S X A) (i j : I) (h : j ≠ i)
    (r : FiniteProduct.Mechanism S0 S X A i) : (closedLoop G i r).component j = G.component j := by
  simp [closedLoop,h]

theorem openLoop_treated (G : FiniteProduct.Generator S0 S X A) (i : I)
    (r : FiniteProduct.Mechanism S0 S X A i)
    (anchor : ∀ j, FiniteProduct.Mechanism S0 S X A j) : (openLoop G i r anchor).component i = r := by
  simp [openLoop]

theorem openLoop_other (G : FiniteProduct.Generator S0 S X A) (i j : I) (h : j ≠ i)
    (r : FiniteProduct.Mechanism S0 S X A i)
    (anchor : ∀ j, FiniteProduct.Mechanism S0 S X A j) :
    (openLoop G i r anchor).component j = anchor j := by
  simp [openLoop,h]

def protocolFamily (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] (i : I) (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j)) :
    InterventionFamily (model G P) Protocol where
  targetOf _ := .jointStrategic
  admissible
    | .closedLoop, gen => gen = assemble (closedLoop G i r)
    | .openLoop, gen => ∃ a ∈ anchors, gen = assemble (openLoop G i r a)

def closedLoopIntervention (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] (i : I) (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j)) :
    AdmissibleStrategicIntervention (protocolFamily G P i r anchors) where
  intervention := ⟨.closedLoop,assemble (closedLoop G i r)⟩
  accepted := rfl
  strategic := InterventionTarget.isStrategic_jointStrategic

def openLoopIntervention (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] (i : I) (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j))
    (a : ∀ j, FiniteProduct.Mechanism S0 S X A j) (ha : a ∈ anchors) :
    AdmissibleStrategicIntervention (protocolFamily G P i r anchors) where
  intervention := ⟨.openLoop,assemble (openLoop G i r a)⟩
  accepted := ⟨a,ha,rfl⟩
  strategic := InterventionTarget.isStrategic_jointStrategic

theorem protocol_world_eq (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] (i : I) (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j))
    (J : AdmissibleStrategicIntervention (protocolFamily G P i r anchors)) :
    J.intervention.apply.world = P := J.world_eq

theorem original_margin_comparison {H Z : Type*} [MeasurableSpace H] [MetricSpace Z]
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] (i : I) (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j))
    (a : ∀ j, FiniteProduct.Mechanism S0 S X A j) (ha : a ∈ anchors)
    (spec : RegimeSpecification (JointState (FiniteProduct.StrategicState S0 S) X) H)
    (ψ : RegimePropertyMap (JointState (FiniteProduct.StrategicState S0 S) X) Z)
    (B : ConstitutiveComparisonSet (model G P) spec) (δ : ℝ)
    (hδ : ∀ y ∈ B.states, protocolGap ψ (closedLoopIntervention G P i r anchors)
      (openLoopIntervention G P i r anchors a ha) y ≤ δ) :
    |constitutiveMargin (model G P) spec (protocolFamily G P i r anchors) ψ B
        (closedLoopIntervention G P i r anchors) -
      constitutiveMargin (model G P) spec (protocolFamily G P i r anchors) ψ B
        (openLoopIntervention G P i r anchors a ha)| ≤ δ :=
  abs_constitutiveMargin_sub_le_of_protocolGap _ _ _ _ _ _ _ hδ

/-- The actual product kernel reduces to the original binary product under
the measurable coordinate equivalence, with arbitrary measurable coordinates. -/
theorem productKernel_two {Y : Type*} [MeasurableSpace Y]
    {Z : Fin 2 → Type*} [∀ i, MeasurableSpace (Z i)]
    (κ : ∀ i, Kernel Y (Z i)) [∀ i, IsMarkovKernel (κ i)] (y : Y) :
    (productKernel κ y).map (MeasurableEquiv.piFinTwo Z) = (κ 0 y).prod (κ 1 y) :=
  (measurePreserving_piFinTwo (fun i => κ i y)).map_eq

end
end PermanssonResearch.MultiAgent.MeasurableProduct
