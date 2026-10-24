import PermanssonResearch.MultiAgent.MeasurableProductTwoPathLaw
import PermanssonResearch.MultiAgent.MeasurableProductProtocols
import Mathlib.Tactic

/-!
# Final closure: matched binary two-player interventions

The binary family is constructed from the *same* source generator, treated
player and admitted original opponent anchors. It is not an independently
chosen binary intervention. All physical changes are within-model forbidden:
the source model retains P, and the binary model retains physical P.
-/

open MeasureTheory ProbabilityTheory Set
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

/-- Exact binary-side family induced by a single frozen source protocol. -/
noncomputable def matchedBinaryFamily
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] (i : Fin 2)
    (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j)) :
    InterventionFamily ((binary G).toModel (physical P)) Protocol where
  targetOf _ := .jointStrategic
  admissible
    | .closedLoop, gen =>
        gen = (binary (MeasurableProduct.closedLoop G i r)).toGenerator
    | .openLoop, gen =>
        ∃ a ∈ anchors,
          gen = (binary (MeasurableProduct.openLoop G i r a)).toGenerator

/-- Closed loop on the binary side: exactly the transported original choice. -/
noncomputable def matchedBinaryClosed
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] (i : Fin 2)
    (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j)) :
    AdmissibleStrategicIntervention (matchedBinaryFamily G P i r anchors) where
  intervention :=
    ⟨.closedLoop, (binary (MeasurableProduct.closedLoop G i r)).toGenerator⟩
  accepted := rfl
  strategic := InterventionTarget.isStrategic_jointStrategic

/-- Open loop on the binary side: the anchor is the actual admitted source anchor. -/
noncomputable def matchedBinaryOpen
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] (i : Fin 2)
    (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j))
    (a : ∀ j, FiniteProduct.Mechanism S0 S X A j)
    (ha : a ∈ anchors) :
    AdmissibleStrategicIntervention (matchedBinaryFamily G P i r anchors) where
  intervention :=
    ⟨.openLoop, (binary (MeasurableProduct.openLoop G i r a)).toGenerator⟩
  accepted := ⟨a, ha, rfl⟩
  strategic := InterventionTarget.isStrategic_jointStrategic

theorem matchedBinaryClosed_apply
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] (i : Fin 2)
    (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j)) :
    (matchedBinaryClosed G P i r anchors).intervention.apply =
      ((binary (MeasurableProduct.closedLoop G i r)).toModel (physical P)) := rfl

theorem matchedBinaryOpen_apply
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] (i : Fin 2)
    (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j))
    (a : ∀ j, FiniteProduct.Mechanism S0 S X A j)
    (ha : a ∈ anchors) :
    (matchedBinaryOpen G P i r anchors a ha).intervention.apply =
      ((binary (MeasurableProduct.openLoop G i r a)).toModel (physical P)) := rfl

/-- The complete original source protocol and the admitted binary choice
commute with the same typed state compression, for either treated player. -/
theorem matched_closed_kernel_two
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] (i : Fin 2)
    (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j)) :
    KernelIntertwines
      (compression_two (S0 := S0) (S := S) (X := X))
      (MeasurableProduct.closedLoopIntervention G P i r anchors).intervention.apply.inducedKernel
      (matchedBinaryClosed G P i r anchors).intervention.apply.inducedKernel := by
  rw [matchedBinaryClosed_apply]
  exact closed_loop_kernel_two G P i r anchors

theorem matched_open_kernel_two
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] (i : Fin 2)
    (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j))
    (a : ∀ j, FiniteProduct.Mechanism S0 S X A j)
    (ha : a ∈ anchors) :
    KernelIntertwines
      (compression_two (S0 := S0) (S := S) (X := X))
      (MeasurableProduct.openLoopIntervention G P i r anchors a ha).intervention.apply.inducedKernel
      (matchedBinaryOpen G P i r anchors a ha).intervention.apply.inducedKernel := by
  rw [matchedBinaryOpen_apply]
  exact open_loop_kernel_two G P i r anchors a ha

theorem matched_binary_closed_world_frozen
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] (i : Fin 2)
    (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j)) :
    (matchedBinaryClosed G P i r anchors).intervention.apply.world = physical P := by
  rw [matchedBinaryClosed_apply]
  rfl

theorem matched_binary_open_world_frozen
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] (i : Fin 2)
    (r : FiniteProduct.Mechanism S0 S X A i)
    (anchors : Set (∀ j, FiniteProduct.Mechanism S0 S X A j))
    (a : ∀ j, FiniteProduct.Mechanism S0 S X A j)
    (ha : a ∈ anchors) :
    (matchedBinaryOpen G P i r anchors a ha).intervention.apply.world = physical P := by
  rw [matchedBinaryOpen_apply]
  rfl

end PermanssonResearch.MultiAgent.MeasurableProduct.Two
