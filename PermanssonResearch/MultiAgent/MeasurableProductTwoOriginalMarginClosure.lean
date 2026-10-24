import PermanssonResearch.MultiAgent.MeasurableProductTwoMatchedProtocols
import PermanssonResearch.MultiAgent.MeasurableProductTwoMargin
import Mathlib.Tactic

/-!
# Original constitutive-margin closure for both matched two-player protocols

The admissible binary intervention and kernel intertwining are constructed
from the source generator, player, replacement mechanism and the frozen source
anchor set. The entire original B₁ and a single pulled-back whole-path property
are retained. The original formal Exact-GR/PR gate is NOT inferred here.
-/

open MeasureTheory ProbabilityTheory Set
namespace PermanssonResearch.MultiAgent.MeasurableProduct.Two

open PermanssonLean
open PermanssonLean.RegimeSpecification
open PermanssonResearch.MultiAgent
open PermanssonResearch.MultiAgent.FiniteProduct
open PermanssonResearch.MultiAgent.MeasurableProduct

set_option autoImplicit false
universe u0 uS uX uA uH uHb uZ
variable {S0 : Type u0} {S : Fin 2 → Type uS}
variable {X : Type uX} {A : Fin 2 → Type uA}
variable [MeasurableSpace S0] [∀ i, MeasurableSpace (S i)]
variable [MeasurableSpace X] [∀ i, MeasurableSpace (A i)]
variable {H : Type uH} {Hb : Type uHb} {Z : Type uZ}
variable [MeasurableSpace H] [MeasurableSpace Hb] [MetricSpace Z]

theorem matched_closed_loop_original_margin
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P]
    (i : Fin 2) (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j))
    (spec : RegimeSpecification (JointState (FiniteProduct.StrategicState S0 S) X) H)
    (specBar : RegimeSpecification (JointState (GameState S0 (S 0) (S 1)) X) Hb)
    (B₁ : ConstitutiveComparisonSet (MeasurableProduct.model G P) spec)
    (Bbar₁ : ConstitutiveComparisonSet ((binary G).toModel (physical P)) specBar)
    (hB : Bbar₁.states =
      (compression_two (S0 := S0) (S := S) (X := X)).stateMap '' B₁.states)
    (ψbar : RegimePropertyMap (JointState (GameState S0 (S 0) (S 1)) X) Z) :
    constitutiveMargin (MeasurableProduct.model G P) spec
      (MeasurableProduct.protocolFamily G P i r anchors)
      (pullbackWholePathProperty
        (compression_two (S0 := S0) (S := S) (X := X)) ψbar)
      B₁ (MeasurableProduct.closedLoopIntervention G P i r anchors) =
    constitutiveMargin ((binary G).toModel (physical P)) specBar
      (matchedBinaryFamily G P i r anchors) ψbar Bbar₁
      (matchedBinaryClosed G P i r anchors) := by
  exact original_margin_transport_two
    G P spec specBar
    (MeasurableProduct.protocolFamily G P i r anchors)
    (matchedBinaryFamily G P i r anchors)
    B₁ Bbar₁ hB
    (MeasurableProduct.closedLoopIntervention G P i r anchors)
    (matchedBinaryClosed G P i r anchors)
    (matched_closed_kernel_two G P i r anchors)
    ψbar

theorem matched_open_loop_original_margin
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P]
    (i : Fin 2) (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j))
    (a : ∀ j, FiniteProduct.Mechanism S0 S X A j)
    (ha : a ∈ anchors)
    (spec : RegimeSpecification (JointState (FiniteProduct.StrategicState S0 S) X) H)
    (specBar : RegimeSpecification (JointState (GameState S0 (S 0) (S 1)) X) Hb)
    (B₁ : ConstitutiveComparisonSet (MeasurableProduct.model G P) spec)
    (Bbar₁ : ConstitutiveComparisonSet ((binary G).toModel (physical P)) specBar)
    (hB : Bbar₁.states =
      (compression_two (S0 := S0) (S := S) (X := X)).stateMap '' B₁.states)
    (ψbar : RegimePropertyMap (JointState (GameState S0 (S 0) (S 1)) X) Z) :
    constitutiveMargin (MeasurableProduct.model G P) spec
      (MeasurableProduct.protocolFamily G P i r anchors)
      (pullbackWholePathProperty
        (compression_two (S0 := S0) (S := S) (X := X)) ψbar)
      B₁ (MeasurableProduct.openLoopIntervention G P i r anchors a ha) =
    constitutiveMargin ((binary G).toModel (physical P)) specBar
      (matchedBinaryFamily G P i r anchors) ψbar Bbar₁
      (matchedBinaryOpen G P i r anchors a ha) := by
  exact original_margin_transport_two
    G P spec specBar
    (MeasurableProduct.protocolFamily G P i r anchors)
    (matchedBinaryFamily G P i r anchors)
    B₁ Bbar₁ hB
    (MeasurableProduct.openLoopIntervention G P i r anchors a ha)
    (matchedBinaryOpen G P i r anchors a ha)
    (matched_open_kernel_two G P i r anchors a ha)
    ψbar

/-- Actual all-initial canonical entire-path equality after transport of a
closed-loop intervention, with the admitted source side, not a fresh binary
choice selected after observing the effect. -/
theorem matched_closed_loop_all_initial_paths
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P]
    (i : Fin 2) (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j))
    (μ : Measure (JointState (FiniteProduct.StrategicState S0 S) X))
    [IsProbabilityMeasure μ] :
    (((MeasurableProduct.closedLoopIntervention G P i r anchors).intervention.apply).pathLaw μ).map
      (compression_two (S0 := S0) (S := S) (X := X)).pathMap =
    ((matchedBinaryClosed G P i r anchors).intervention.apply).pathLaw
      (μ.map (compression_two (S0 := S0) (S := S) (X := X)).stateMap) := by
  rw [matchedBinaryClosed_apply]
  exact closed_loop_path_law_two G P i r anchors μ

theorem matched_open_loop_all_initial_paths
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P]
    (i : Fin 2) (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j))
    (a : ∀ j, FiniteProduct.Mechanism S0 S X A j)
    (ha : a ∈ anchors)
    (μ : Measure (JointState (FiniteProduct.StrategicState S0 S) X))
    [IsProbabilityMeasure μ] :
    (((MeasurableProduct.openLoopIntervention G P i r anchors a ha).intervention.apply).pathLaw μ).map
      (compression_two (S0 := S0) (S := S) (X := X)).pathMap =
    ((matchedBinaryOpen G P i r anchors a ha).intervention.apply).pathLaw
      (μ.map (compression_two (S0 := S0) (S := S) (X := X)).stateMap) := by
  rw [matchedBinaryOpen_apply]
  exact open_loop_path_law_two G P i r anchors a ha μ

end PermanssonResearch.MultiAgent.MeasurableProduct.Two
