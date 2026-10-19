import PermanssonResearch.MultiAgent.MeasurableProductProtocols
import Mathlib.Tactic

/-!
# NEXT-05 (part 1) — measurable two-player coordinate recovery

The Fin 2 coordinate equivalence works for ARBITRARY measurable common,
private, action and world spaces, not only finite atomic state sets.
The pulled-back binary generator reads original physical world/update
inputs (including the asymmetric action/world arguments). Only the action
kernel conjugacy is certified here; full induced/path-law recovery still
requires separate product-kernel/trajectory transport theorems.
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

def state (y : JointState (StrategicState S0 S) X) :
    JointState (GameState S0 (S 0) (S 1)) X :=
  ((y.1.1, (y.1.2 0, y.1.2 1)), y.2)

def inverseState (y : JointState (GameState S0 (S 0) (S 1)) X) :
    JointState (StrategicState S0 S) X :=
  ((y.1.1, (MeasurableEquiv.piFinTwo S).symm y.1.2), y.2)

@[simp] theorem inverse_state (y : JointState (StrategicState S0 S) X) :
    inverseState (state y) = y := by
  change ((y.1.1, (MeasurableEquiv.piFinTwo S).symm
    ((MeasurableEquiv.piFinTwo S) y.1.2)), y.2) = y
  exact congrArg (fun s : ∀ i, S i => ((y.1.1, s), y.2))
    ((MeasurableEquiv.piFinTwo S).symm_apply_apply y.1.2)

@[simp] theorem state_inverse (y : JointState (GameState S0 (S 0) (S 1)) X) :
    state (inverseState y) = y := by
  change ((y.1.1, (MeasurableEquiv.piFinTwo S)
    ((MeasurableEquiv.piFinTwo S).symm y.1.2)), y.2) = y
  simp

theorem measurable_state :
    Measurable (state (S0 := S0) (S := S) (X := X)) := by
  unfold state
  fun_prop

theorem measurable_inverseState :
    Measurable (inverseState (S0 := S0) (S := S) (X := X)) := by
  unfold inverseState
  fun_prop

def inverseWorld
    (v : WorldInput (GameState S0 (S 0) (S 1)) X (A 0 × A 1)) :
    WorldInput (StrategicState S0 S) X (∀ i, A i) :=
  (inverseState v.1, (MeasurableEquiv.piFinTwo A).symm v.2)

def inverseInput
    (v : UpdateInput (GameState S0 (S 0) (S 1)) X (A 0 × A 1)) :
    UpdateInput (StrategicState S0 S) X (∀ i, A i) :=
  (inverseWorld v.1, v.2)

theorem measurable_inverseWorld :
    Measurable (inverseWorld (S0 := S0) (S := S) (X := X) (A := A)) := by
  unfold inverseWorld
  fun_prop

theorem measurable_inverseInput :
    Measurable (inverseInput (S0 := S0) (S := S) (X := X) (A := A)) := by
  unfold inverseInput
  fun_prop

@[simp] theorem inverse_world_at_original
    (y : JointState (StrategicState S0 S) X) (a : ∀ i, A i) :
    inverseWorld (state y, (MeasurableEquiv.piFinTwo A) a) = (y, a) := by
  simp [inverseWorld]

@[simp] theorem inverse_input_at_original
    (y : JointState (StrategicState S0 S) X)
    (a : ∀ i, A i) (x : X) :
    inverseInput ((state y, (MeasurableEquiv.piFinTwo A) a), x) =
      ((y, a), x) := by
  simp [inverseInput]

/-- Binary generator on the actual two-player coordinates. Common update,
private updates and physical world rows are all read through their COMPLETE
original inputs; no symmetric-world or independent-common-update premise. -/
noncomputable def binary (G : Generator S0 S X A) :
    TwoPlayerGenerator S0 (S 0) (S 1) X (A 0) (A 1) where
  player1 :=
    { action := (G.component 0).action.comap inverseState measurable_inverseState
      update := (G.component 0).update.comap inverseInput measurable_inverseInput
      action_isMarkov := by letI := (G.component 0).action_isMarkov; infer_instance
      update_isMarkov := by letI := (G.component 0).update_isMarkov; infer_instance }
  player2 :=
    { action := (G.component 1).action.comap inverseState measurable_inverseState
      update := (G.component 1).update.comap inverseInput measurable_inverseInput
      action_isMarkov := by letI := (G.component 1).action_isMarkov; infer_instance
      update_isMarkov := by letI := (G.component 1).update_isMarkov; infer_instance }
  common := G.common.comap inverseInput measurable_inverseInput
  common_isMarkov := by letI := G.common_isMarkov; infer_instance

noncomputable def physical
    (P : Kernel (WorldInput (StrategicState S0 S) X (∀ i, A i)) X) :
    Kernel (WorldInput (GameState S0 (S 0) (S 1)) X (A 0 × A 1)) X :=
  P.comap inverseWorld measurable_inverseWorld

instance physical_isMarkov
    (P : Kernel (WorldInput (StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] : IsMarkovKernel (physical P) := by
  unfold physical
  infer_instance

/-- Genuine measurable action-product conjugacy, without finite state,
action, world or common-memory assumptions. -/
theorem action_map_two (G : Generator S0 S X A)
    (y : JointState (StrategicState S0 S) X) :
    ((assemble G).action y).map (MeasurableEquiv.piFinTwo A) =
      ((binary G).toGenerator).action (state y) := by
  letI : ∀ i, IsMarkovKernel (G.component i).action :=
    fun i => (G.component i).action_isMarkov
  rw [action_apply, TwoPlayerGenerator.toGenerator_action_apply]
  simpa [binary, Kernel.comap_apply, inverse_state] using
    (productKernel_two (fun i => (G.component i).action) y)

end PermanssonResearch.MultiAgent.MeasurableProduct.Two
