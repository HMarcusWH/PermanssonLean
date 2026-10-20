import PermanssonResearch.MultiAgent.MeasurableProductTwoKernel
import PermanssonResearch.MultiAgent.MeasurableProductProtocols
import Mathlib.Tactic

/-!
NEXT-05.2: genuine legal source CL/OL interventions for either player.
The model's physical P remains literally fixed and open-loop anchors are
admitted before comparison. Kernel results use the measurable all-event
alpha -> P -> U theorem, never finite singleton enumeration.
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

theorem closed_loop_application
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] (i : Fin 2)
    (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j)) :
    (MeasurableProduct.closedLoopIntervention G P i r anchors).intervention.apply =
      MeasurableProduct.model (MeasurableProduct.closedLoop G i r) P := rfl

theorem open_loop_application
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] (i : Fin 2)
    (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j))
    (anchor : ∀ j, FiniteProduct.Mechanism S0 S X A j)
    (ha : anchor ∈ anchors) :
    (MeasurableProduct.openLoopIntervention G P i r anchors anchor ha).intervention.apply =
      MeasurableProduct.model (MeasurableProduct.openLoop G i r anchor) P := rfl

theorem closed_loop_world_frozen
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] (i : Fin 2)
    (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j)) :
    (MeasurableProduct.closedLoopIntervention G P i r anchors).intervention.apply.world = P := by
  rw [closed_loop_application]
  rfl

theorem open_loop_world_frozen
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] (i : Fin 2)
    (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j))
    (anchor : ∀ j, FiniteProduct.Mechanism S0 S X A j)
    (ha : anchor ∈ anchors) :
    (MeasurableProduct.openLoopIntervention G P i r anchors anchor ha).intervention.apply.world = P := by
  rw [open_loop_application]
  rfl

theorem closed_loop_kernel_two
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] (i : Fin 2)
    (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j)) :
    KernelIntertwines
      (compression_two (S0 := S0) (S := S) (X := X))
      (MeasurableProduct.closedLoopIntervention G P i r anchors).intervention.apply.inducedKernel
      ((binary (MeasurableProduct.closedLoop G i r)).toModel (physical P)).inducedKernel := by
  rw [closed_loop_application]
  exact induced_kernel_intertwines_two (MeasurableProduct.closedLoop G i r) P

theorem open_loop_kernel_two
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] (i : Fin 2)
    (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j))
    (anchor : ∀ j, FiniteProduct.Mechanism S0 S X A j)
    (ha : anchor ∈ anchors) :
    KernelIntertwines
      (compression_two (S0 := S0) (S := S) (X := X))
      (MeasurableProduct.openLoopIntervention G P i r anchors anchor ha).intervention.apply.inducedKernel
      ((binary (MeasurableProduct.openLoop G i r anchor)).toModel (physical P)).inducedKernel := by
  rw [open_loop_application]
  exact induced_kernel_intertwines_two (MeasurableProduct.openLoop G i r anchor) P

end PermanssonResearch.MultiAgent.MeasurableProduct.Two
