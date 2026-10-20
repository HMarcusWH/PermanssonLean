import PermanssonResearch.MultiAgent.MeasurableProductTwoProtocols
import PermanssonLean.Quotient.PathLaw
import Mathlib.Tactic

/-!
NEXT-05.2: entire original infinite canonical path law for arbitrary
initial probabilities, including non-Dirac laws. Both typed legal source
CL/OL protocols transport under the same physical P. The original
constitutive property and B1 margin are separate from kernel transport.
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

theorem path_law_map_two
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P]
    (μ : Measure (JointState (FiniteProduct.StrategicState S0 S) X))
    [IsProbabilityMeasure μ] :
    ((MeasurableProduct.model G P).pathLaw μ).map
      (compression_two (S0 := S0) (S := S) (X := X)).pathMap =
      ((binary G).toModel (physical P)).pathLaw
        (μ.map (compression_two (S0 := S0) (S := S) (X := X)).stateMap) :=
  StrategicWorldModel.pathLaw_map_eq_of_kernelIntertwines
    (compression_two (S0 := S0) (S := S) (X := X))
    (MeasurableProduct.model G P)
    ((binary G).toModel (physical P))
    (induced_kernel_intertwines_two G P) μ

theorem closed_loop_path_law_two
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] (i : Fin 2)
    (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j))
    (μ : Measure (JointState (FiniteProduct.StrategicState S0 S) X))
    [IsProbabilityMeasure μ] :
    (((MeasurableProduct.closedLoopIntervention G P i r anchors).intervention.apply).pathLaw μ).map
      (compression_two (S0 := S0) (S := S) (X := X)).pathMap =
      ((binary (MeasurableProduct.closedLoop G i r)).toModel (physical P)).pathLaw
        (μ.map (compression_two (S0 := S0) (S := S) (X := X)).stateMap) := by
  rw [closed_loop_application]
  exact path_law_map_two (MeasurableProduct.closedLoop G i r) P μ

theorem open_loop_path_law_two
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] (i : Fin 2)
    (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j))
    (anchor : ∀ j, FiniteProduct.Mechanism S0 S X A j)
    (ha : anchor ∈ anchors)
    (μ : Measure (JointState (FiniteProduct.StrategicState S0 S) X))
    [IsProbabilityMeasure μ] :
    (((MeasurableProduct.openLoopIntervention G P i r anchors anchor ha).intervention.apply).pathLaw μ).map
      (compression_two (S0 := S0) (S := S) (X := X)).pathMap =
      ((binary (MeasurableProduct.openLoop G i r anchor)).toModel (physical P)).pathLaw
        (μ.map (compression_two (S0 := S0) (S := S) (X := X)).stateMap) := by
  rw [open_loop_application]
  exact path_law_map_two (MeasurableProduct.openLoop G i r anchor) P μ

end PermanssonResearch.MultiAgent.MeasurableProduct.Two
