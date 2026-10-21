import PermanssonResearch.MultiAgent.MeasurableProductTwoOriginalMarginClosure
import PermanssonResearch.MultiAgent.AsymmetricCommonSwapFixture
import Mathlib.Tactic

/-!
Mixed-direction admissibility regression: the same frozen physical kernel
persists on both sides of any Fin 2 treated-player protocol. Existing
asymmetric swap fixture independently catches physical/action and common
update input mistakes; its use does not identify a correlated generator.
-/
open MeasureTheory ProbabilityTheory
namespace PermanssonResearch.MultiAgent.MeasurableProduct.Two
open PermanssonLean
open PermanssonResearch.MultiAgent
open PermanssonResearch.MultiAgent.FiniteProduct
open PermanssonResearch.MultiAgent.MeasurableProduct

set_option autoImplicit false
universe u0 uS uX uA
variable {S0 : Type u0} {S : Fin 2 → Type uS}
variable {X : Type uX} {A : Fin 2 → Type uA}
variable [MeasurableSpace S0] [∀ i, MeasurableSpace (S i)]
variable [MeasurableSpace X] [∀ i, MeasurableSpace (A i)]

theorem matched_closed_worlds_both_frozen
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P]
    (i : Fin 2) (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j)) :
    (MeasurableProduct.closedLoopIntervention G P i r anchors).intervention.apply.world = P ∧
    (matchedBinaryClosed G P i r anchors).intervention.apply.world =
      physical P := by
  constructor
  · exact closed_loop_world_frozen G P i r anchors
  · exact matched_binary_closed_world_frozen G P i r anchors

theorem matched_open_worlds_both_frozen
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P]
    (i : Fin 2) (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j))
    (a : ∀ j, FiniteProduct.Mechanism S0 S X A j)
    (ha : a ∈ anchors) :
    (MeasurableProduct.openLoopIntervention G P i r anchors a ha).intervention.apply.world = P ∧
    (matchedBinaryOpen G P i r anchors a ha).intervention.apply.world =
      physical P := by
  constructor
  · exact open_loop_world_frozen G P i r anchors a ha
  · exact matched_binary_open_world_frozen G P i r anchors a ha

end PermanssonResearch.MultiAgent.MeasurableProduct.Two

namespace PermanssonResearch.MultiAgent.FinalMatchedAsymmetry

open PermanssonResearch.MultiAgent.AsymmetricCommonSwapFixture
open PermanssonResearch.MultiAgent.PlayerSwap

theorem wrong_asymmetric_input_change_is_detectable :
    ((PlayerSwap.physical physicalFromFirstAction) liveWorldInput {true} = 1 ∧
      physicalFromFirstAction liveWorldInput {true} = 0) ∧
    ((PlayerSwap.generator generator).common liveUpdateInput {true} = 1 ∧
      generator.common liveUpdateInput {true} = 0) :=
  ⟨real_physical_pullback_changes_asymmetric_input,
   real_common_update_pullback_changes_input⟩

end PermanssonResearch.MultiAgent.FinalMatchedAsymmetry
