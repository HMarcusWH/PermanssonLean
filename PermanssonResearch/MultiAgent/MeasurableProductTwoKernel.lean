import PermanssonResearch.MultiAgent.MeasurableProductTwoUpdate
import PermanssonLean.Quotient.KernelIntertwining
import Mathlib.Tactic

/-!
# NEXT-05.1 — typed two-player physical, action and update kernel bridges

Source definitions are the genuine arbitrary-measurable conditional-product
generator. All pushforwards use the correct output type; no finite state
assumptions or singleton-event theorem appears here.

The remaining actual induced-kernel intertwining must follow from these
component identities through alpha → P → U. Until that proof is compiled,
this module is a scoped intermediate and is NOT P-05.1 acceptance.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultiAgent.MeasurableProduct.Two

open PermanssonLean
open PermanssonResearch.MultiAgent.FiniteProduct
open PermanssonResearch.MultiAgent.MeasurableProduct

set_option autoImplicit false

universe u0 uS uX uA
variable {S0 : Type u0} {S : Fin 2 → Type uS}
variable {X : Type uX} {A : Fin 2 → Type uA}
variable [MeasurableSpace S0] [∀ i, MeasurableSpace (S i)]
variable [MeasurableSpace X] [∀ i, MeasurableSpace (A i)]

/-- Complete original world input, with both realized actions kept. -/
def forwardWorld
    (v : WorldInput (StrategicState S0 S) X (∀ i, A i)) :
    WorldInput (GameState S0 (S 0) (S 1)) X (A 0 × A 1) :=
  (state v.1, (MeasurableEquiv.piFinTwo A) v.2)

/-- Complete update input, including the realized next-world value. -/
def forwardUpdate
    (v : UpdateInput (StrategicState S0 S) X (∀ i, A i)) :
    UpdateInput (GameState S0 (S 0) (S 1)) X (A 0 × A 1) :=
  (forwardWorld v.1, v.2)

theorem measurable_forwardWorld :
    Measurable (forwardWorld (S0 := S0) (S := S) (X := X) (A := A)) := by
  have hstate := measurable_state (S0 := S0) (S := S) (X := X)
  have haction : Measurable (MeasurableEquiv.piFinTwo A) :=
    (MeasurableEquiv.piFinTwo A).measurable
  unfold forwardWorld
  fun_prop

theorem measurable_forwardUpdate :
    Measurable (forwardUpdate (S0 := S0) (S := S) (X := X) (A := A)) := by
  have hworld := measurable_forwardWorld (S0 := S0) (S := S) (X := X) (A := A)
  unfold forwardUpdate
  fun_prop

@[simp] theorem inverse_forwardWorld
    (v : WorldInput (StrategicState S0 S) X (∀ i, A i)) :
    inverseWorld (forwardWorld v) = v := by
  rcases v with ⟨y, a⟩
  simpa only [forwardWorld] using inverse_world_at_original y a

@[simp] theorem inverse_forwardUpdate
    (v : UpdateInput (StrategicState S0 S) X (∀ i, A i)) :
    inverseInput (forwardUpdate v) = v := by
  rcases v with ⟨⟨y, a⟩, x⟩
  simpa only [forwardUpdate, forwardWorld] using inverse_input_at_original y a x

/-- Actual original type-respecting strategic reindexing; world is unchanged. -/
noncomputable def compression_two :
    TypeRespectingStateCompression (StrategicState S0 S) X
      (GameState S0 (S 0) (S 1)) X where
  strategic := strategicMap
  world := id
  strategic_measurable := measurable_strategicMap
  world_measurable := measurable_id
  strategic_surjective := by
    intro s
    exact ⟨inverseStrategicMap s, strategicMap_inverse s⟩
  world_surjective := Function.surjective_id

@[simp] theorem compression_two_state
    (y : JointState (StrategicState S0 S) X) :
    (compression_two (S0 := S0) (S := S) (X := X)).stateMap y =
      state y := rfl

/-- Actual measurable action-kernel correspondence at every input. -/
theorem action_kernel_map_two (G : Generator S0 S X A) :
    ((assemble G).action).map (MeasurableEquiv.piFinTwo A) =
      (((binary G).toGenerator).action).comap state measurable_state := by
  apply Kernel.ext
  intro y
  simpa only [Kernel.map_apply, Kernel.comap_apply] using action_map_two G y

/-- Actual physical world kernel, at all inputs, with no action symmetry. -/
theorem world_kernel_pullback_two
    (P : Kernel (WorldInput (StrategicState S0 S) X (∀ i, A i)) X) :
    (physical P).comap forwardWorld measurable_forwardWorld = P := by
  apply Kernel.ext
  intro v
  simpa only [Kernel.comap_apply, inverse_forwardWorld, physical] using
    (show physical P (forwardWorld v) = P v from by
      rcases v with ⟨y, a⟩
      simpa only [forwardWorld] using world_pullback_two P y a)

/-- Complete strategic-output kernel law, not a joint-state output map. -/
theorem update_kernel_map_two (G : Generator S0 S X A) :
    ((assemble G).update).map strategicMap =
      (((binary G).toGenerator).update).comap forwardUpdate measurable_forwardUpdate := by
  apply Kernel.ext
  intro v
  rcases v with ⟨⟨y, a⟩, x⟩
  simpa only [Kernel.map_apply, Kernel.comap_apply, forwardUpdate, forwardWorld] using
    update_map_two G y a x

end PermanssonResearch.MultiAgent.MeasurableProduct.Two
