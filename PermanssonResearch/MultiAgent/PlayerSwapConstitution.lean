import PermanssonResearch.MultiAgent.PlayerSwapTransport

/-! The same swap transports a pair of declared protocols, their pulled-back
property, and the ORIGINAL constitutive margin on corresponding certified
comparison sets. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultiAgent.PlayerSwap

set_option autoImplicit false
open PermanssonLean PermanssonLean.RegimeSpecification

variable {S0 S1 S2 X A1 A2 : Type*}
variable [MeasurableSpace S0] [MeasurableSpace S1] [MeasurableSpace S2]
variable [MeasurableSpace X] [MeasurableSpace A1] [MeasurableSpace A2]

noncomputable def directPair (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (r : PlayerTwoMechanism S0 S1 S2 X A1 A2)
    (a : PlayerOneMechanism S0 S1 S2 X A1 A2) :
    FrozenStrategicInterventionFamily (PlayerTwoProtocols.protocolFamily G P r {a}) Protocol where
  intervention
    | .closedLoop => PlayerTwoProtocols.closedLoopIntervention G P r {a}
    | .openLoop => PlayerTwoProtocols.openLoopIntervention G P r {a} a (by simp)
  label_nonempty := ⟨.closedLoop⟩

noncomputable def swappedPair (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (r : PlayerTwoMechanism S0 S1 S2 X A1 A2)
    (a : PlayerOneMechanism S0 S1 S2 X A1 A2) :
    FrozenStrategicInterventionFamily
      (protocolFamily (generator G) (physical P) (first r) {second a}) Protocol where
  intervention
    | .closedLoop => closedLoopIntervention (generator G) (physical P) (first r) {second a}
    | .openLoop => openLoopIntervention (generator G) (physical P) (first r)
        {second a} (second a) (by simp)
  label_nonempty := ⟨.closedLoop⟩

section Finite
variable [Fintype S0] [Fintype S1] [Fintype S2] [Fintype X] [Fintype A1] [Fintype A2]
variable [MeasurableSingletonClass S0] [MeasurableSingletonClass S1]
variable [MeasurableSingletonClass S2] [MeasurableSingletonClass X]
variable [MeasurableSingletonClass A1] [MeasurableSingletonClass A2]

noncomputable def pairQuotient (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (r : PlayerTwoMechanism S0 S1 S2 X A1 A2)
    (a : PlayerOneMechanism S0 S1 S2 X A1 A2) :
    InterventionCompatibleKernelQuotient compression
      (PlayerTwoProtocols.protocolFamily G P r {a})
      (protocolFamily (generator G) (physical P) (first r) {second a})
      (directPair G P r a) (swappedPair G P r a) where
  matching :=
    { labelEquiv := Equiv.refl _
      target_eq := fun l => by cases l <;> rfl }
  baseline_intertwines := actual_intertwines G P
  intervention_intertwines := by
    intro l
    cases l with
    | closedLoop =>
        change KernelIntertwines compression
          ((PlayerTwoProtocols.closedLoop G r).toModel P).inducedKernel
          (((generator G).closedLoop (first r)).toModel (physical P)).inducedKernel
        rw [← generator_closedLoop]
        exact actual_intertwines _ P
    | openLoop =>
        change KernelIntertwines compression
          ((PlayerTwoProtocols.openLoop G r a).toModel P).inducedKernel
          (((generator G).openLoop (first r) (second a)).toModel (physical P)).inducedKernel
        rw [← generator_openLoop]
        exact actual_intertwines _ P

/-- Both labels preserve the original metric effect under player relabelling. -/
theorem original_effect {Z : Type*} [MetricSpace Z]
    (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (r : PlayerTwoMechanism S0 S1 S2 X A1 A2)
    (a : PlayerOneMechanism S0 S1 S2 X A1 A2)
    (ψ : RegimePropertyMap (JointState (GameState S0 S1 S2) X) Z)
    (ψbar : RegimePropertyMap (JointState (GameState S0 S2 S1) X) Z)
    (hψ : PropertyFactorsThroughCompression compression ψ ψbar)
    (l : Protocol) (y : JointState (GameState S0 S1 S2) X) :
    constitutiveEffect (G.toModel P) ψ ((directPair G P r a).intervention l) y =
      constitutiveEffect ((generator G).toModel (physical P)) ψbar
        ((swappedPair G P r a).intervention l) (state y) := by
  exact constitutiveEffect_eq_under_quotient compression _ _ _ _
    (pairQuotient G P r a) ψ ψbar hψ l y

/-- Exact original `sInf` margin equality; comparison sets are certified on
both models and correspond by the same coordinate map used for the laws. -/
theorem original_margin {H Z : Type*} [MeasurableSpace H] [MetricSpace Z]
    (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (r : PlayerTwoMechanism S0 S1 S2 X A1 A2)
    (a : PlayerOneMechanism S0 S1 S2 X A1 A2)
    (spec : RegimeSpecification (JointState (GameState S0 S1 S2) X) H)
    (specbar : RegimeSpecification (JointState (GameState S0 S2 S1) X) H)
    (ψ : RegimePropertyMap (JointState (GameState S0 S1 S2) X) Z)
    (ψbar : RegimePropertyMap (JointState (GameState S0 S2 S1) X) Z)
    (hψ : PropertyFactorsThroughCompression compression ψ ψbar)
    (B : ConstitutiveComparisonSet (G.toModel P) spec)
    (Bbar : ConstitutiveComparisonSet ((generator G).toModel (physical P)) specbar)
    (hB : QuotientCompatibleComparisonSets compression B Bbar) (l : Protocol) :
    constitutiveMargin (G.toModel P) spec (PlayerTwoProtocols.protocolFamily G P r {a})
      ψ B ((directPair G P r a).intervention l) =
      constitutiveMargin ((generator G).toModel (physical P)) specbar
        (protocolFamily (generator G) (physical P) (first r) {second a}) ψbar Bbar
        ((swappedPair G P r a).intervention l) := by
  exact constitutiveMargin_eq_under_quotient compression spec specbar _ _ _ _
    (pairQuotient G P r a) ψ ψbar hψ B Bbar hB l

end Finite
end PermanssonResearch.MultiAgent.PlayerSwap
