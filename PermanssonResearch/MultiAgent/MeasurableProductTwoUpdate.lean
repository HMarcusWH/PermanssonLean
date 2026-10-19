import PermanssonResearch.MultiAgent.MeasurableProductTwo
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

/-!
# NEXT-05.1 — Arbitrary-measurable two-player strategic-update transport

The generic Fin 2 conditional-product generator has an independently sampled
common/private update. On the binary coordinate map, the FULL strategic
output distribution agrees, using Measure.map_prod_map and
MeasurableEquiv.piFinTwo rather than singleton enumeration.

This is a strategic-state output theorem, NOT a joint-state output map.
Physical world and realized-update inputs are explicitly transported.
The induced joint kernel, legal CL/OL protocol and entire-path transport
are separate acceptance obligations.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultiAgent.MeasurableProduct.Two

set_option autoImplicit false
open PermanssonLean
open PermanssonResearch.MultiAgent.FiniteProduct
open PermanssonResearch.MultiAgent.MeasurableProduct

universe u0 uS uX uA
variable {S0 : Type u0} {S : Fin 2 → Type uS}
variable {X : Type uX} {A : Fin 2 → Type uA}
variable [MeasurableSpace S0] [∀ i, MeasurableSpace (S i)]
variable [MeasurableSpace X] [∀ i, MeasurableSpace (A i)]

/-- The strategic output map φS is distinct from the joint-state map φY. -/
def strategicMap (s : StrategicState S0 S) :
    GameState S0 (S 0) (S 1) :=
  (s.1, (MeasurableEquiv.piFinTwo S) s.2)

/-- The inverse uses the genuine measurable two-coordinate equivalence. -/
def inverseStrategicMap (s : GameState S0 (S 0) (S 1)) :
    StrategicState S0 S :=
  (s.1, (MeasurableEquiv.piFinTwo S).symm s.2)

@[simp] theorem inverse_strategicMap (s : StrategicState S0 S) :
    inverseStrategicMap (strategicMap s) = s := by
  cases s with
  | mk common private =>
    simp [inverseStrategicMap, strategicMap]

@[simp] theorem strategicMap_inverse (s : GameState S0 (S 0) (S 1)) :
    strategicMap (inverseStrategicMap s) = s := by
  cases s with
  | mk common private =>
    simp [inverseStrategicMap, strategicMap]

theorem measurable_strategicMap :
    Measurable (strategicMap (S0 := S0) (S := S)) := by
  unfold strategicMap
  fun_prop

theorem measurable_inverseStrategicMap :
    Measurable (inverseStrategicMap (S0 := S0) (S := S)) := by
  have hs : Measurable ((MeasurableEquiv.piFinTwo S).symm) :=
    (MeasurableEquiv.piFinTwo S).symm.measurable
  unfold inverseStrategicMap
  fun_prop

@[simp] theorem strategicMap_joint_component
    (y : JointState (StrategicState S0 S) X) :
    strategicMap y.1 = (state y).1 := rfl

/-- Reconstructed physical P reads both actions from the exact original
world input; no symmetry or ignored-opponent hypothesis. -/
theorem world_pullback_two
    (P : Kernel (WorldInput (StrategicState S0 S) X (∀ i, A i)) X)
    (y : JointState (StrategicState S0 S) X)
    (a : ∀ i, A i) :
    physical P (state y, (MeasurableEquiv.piFinTwo A) a) = P (y,a) := by
  simp only [physical, Kernel.comap_apply, inverse_world_at_original]

/-- The common update sees the exact next-world value and the entire pair of
original realized actions after type-respecting reindexing. -/
theorem common_update_pullback_two
    (G : Generator S0 S X A)
    (y : JointState (StrategicState S0 S) X)
    (a : ∀ i, A i) (x' : X) :
    (binary G).common ((state y,(MeasurableEquiv.piFinTwo A) a),x') =
      G.common ((y,a),x') := by
  simp only [binary, Kernel.comap_apply, inverse_input_at_original]

/-- Both player-specific private updates preserve their own coordinate,
their common arguments, both actions and the realized next-world state. -/
theorem private_update_pullback_two
    (G : Generator S0 S X A)
    (y : JointState (StrategicState S0 S) X)
    (a : ∀ i, A i) (x' : X) (i : Fin 2) :
    (if i = 0 then (binary G).player1.update
       ((state y,(MeasurableEquiv.piFinTwo A) a),x')
     else (binary G).player2.update
       ((state y,(MeasurableEquiv.piFinTwo A) a),x')) =
    (if i = 0 then (G.component 0).update ((y,a),x')
     else (G.component 1).update ((y,a),x')) := by
  fin_cases i <;>
    simp only [binary, Kernel.comap_apply, inverse_input_at_original, dite_true, dite_false]
    <;> simp

/-- Full original common/private update measure pushed by φS equals the
reconstructed binary strategic-output update on all measurable events.
Arbitrary measurable coordinates: NO finiteness/singleton proof. -/
theorem update_map_two
    (G : Generator S0 S X A)
    (y : JointState (StrategicState S0 S) X)
    (a : ∀ i, A i) (x' : X) :
    ((assemble G).update ((y,a),x')).map strategicMap =
      ((binary G).toGenerator).update
        ((state y,(MeasurableEquiv.piFinTwo A) a),x') := by
  let v : UpdateInput (StrategicState S0 S) X (∀ i, A i) :=
    ((y,a),x')
  letI : IsMarkovKernel (G.common) := G.common_isMarkov
  letI : ∀ i : Fin 2, IsMarkovKernel (G.component i).update :=
    fun i => (G.component i).update_isMarkov
  have hprivate := productKernel_two (fun i : Fin 2 => (G.component i).update) v
  change (Measure.pi (fun i => (G.component i).update v)).map
      (MeasurableEquiv.piFinTwo S) =
      ((G.component 0).update v).prod ((G.component 1).update v) at hprivate
  have hpi : Measurable (MeasurableEquiv.piFinTwo S) :=
    (MeasurableEquiv.piFinTwo S).measurable
  calc
    ((assemble G).update ((y,a),x')).map strategicMap =
      ((G.common v).prod (Measure.pi (fun i => (G.component i).update v))).map
        (Prod.map id (MeasurableEquiv.piFinTwo S)) := by
          rw [update_apply]
          rfl
    _ = ((G.common v).map id).prod
          ((Measure.pi (fun i => (G.component i).update v)).map
            (MeasurableEquiv.piFinTwo S)) := by
            symm
            exact Measure.map_prod_map _ _ measurable_id hpi
    _ = (G.common v).prod
          (((G.component 0).update v).prod ((G.component 1).update v)) := by
          rw [Measure.map_id, hprivate]
    _ = ((binary G).toGenerator).update
          ((state y,(MeasurableEquiv.piFinTwo A) a),x') := by
          rw [TwoPlayerGenerator.toGenerator_update_apply]
          simp only [binary, Kernel.comap_apply, inverse_input_at_original]

end PermanssonResearch.MultiAgent.MeasurableProduct.Two
