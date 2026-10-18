import PermanssonResearch.MultiAgent.FiniteProductProtocols
import PermanssonLean.Quotient.PathLaw

/-! Reduction of the finite indexed construction at I = Fin 2 to the ORIGINAL
TwoPlayerGenerator, including the pullback of asymmetric physical inputs and
the equality of the original canonical full path laws. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultiAgent.FiniteProduct.Two

set_option autoImplicit false
open PermanssonLean

variable {S0 X : Type*} {S A : Fin 2 → Type*}
variable [MeasurableSpace S0] [MeasurableSpace X]
variable [∀ i, MeasurableSpace (S i)] [∀ i, MeasurableSpace (A i)]
variable [Fintype S0] [Fintype X] [∀ i, Fintype (S i)] [∀ i, Fintype (A i)]
variable [MeasurableSingletonClass S0] [MeasurableSingletonClass X]
variable [∀ i, MeasurableSingletonClass (S i)] [∀ i, MeasurableSingletonClass (A i)]

def state (y : JointState (StrategicState S0 S) X) : JointState (GameState S0 (S 0) (S 1)) X :=
  ((y.1.1,(y.1.2 0,y.1.2 1)),y.2)

def inverseState (y : JointState (GameState S0 (S 0) (S 1)) X) :
    JointState (StrategicState S0 S) X :=
  ((y.1.1,(MeasurableEquiv.piFinTwo S).symm y.1.2),y.2)

@[simp] theorem inverse_state (y : JointState (StrategicState S0 S) X) :
    inverseState (state y) = y := by
  change ((y.1.1,(MeasurableEquiv.piFinTwo S).symm
    ((MeasurableEquiv.piFinTwo S) y.1.2)),y.2) = y
  exact congrArg (fun s : ∀ i, S i => ((y.1.1,s),y.2))
    ((MeasurableEquiv.piFinTwo S).symm_apply_apply y.1.2)

@[simp] theorem state_inverse (y : JointState (GameState S0 (S 0) (S 1)) X) :
    state (inverseState y) = y := by
  change ((y.1.1,(MeasurableEquiv.piFinTwo S)
    ((MeasurableEquiv.piFinTwo S).symm y.1.2)),y.2) = y
  simp

def inverseWorld (v : WorldInput (GameState S0 (S 0) (S 1)) X (A 0 × A 1)) :
    WorldInput (StrategicState S0 S) X (∀ i, A i) :=
  (inverseState v.1,(MeasurableEquiv.piFinTwo A).symm v.2)

def inverseInput (v : UpdateInput (GameState S0 (S 0) (S 1)) X (A 0 × A 1)) :
    UpdateInput (StrategicState S0 S) X (∀ i, A i) := (inverseWorld v.1,v.2)

noncomputable def binary (G : Generator S0 S X A) :
    TwoPlayerGenerator S0 (S 0) (S 1) X (A 0) (A 1) where
  player1 :=
    { action := (G.component 0).action.comap inverseState (measurable_of_finite _)
      update := (G.component 0).update.comap inverseInput (measurable_of_finite _)
      action_isMarkov := by letI := (G.component 0).action_isMarkov; infer_instance
      update_isMarkov := by letI := (G.component 0).update_isMarkov; infer_instance }
  player2 :=
    { action := (G.component 1).action.comap inverseState (measurable_of_finite _)
      update := (G.component 1).update.comap inverseInput (measurable_of_finite _)
      action_isMarkov := by letI := (G.component 1).action_isMarkov; infer_instance
      update_isMarkov := by letI := (G.component 1).update_isMarkov; infer_instance }
  common := G.common.comap inverseInput (measurable_of_finite _)
  common_isMarkov := by letI := G.common_isMarkov; infer_instance

noncomputable def physical
    (P : Kernel (WorldInput (StrategicState S0 S) X (∀ i, A i)) X) :
    Kernel (WorldInput (GameState S0 (S 0) (S 1)) X (A 0 × A 1)) X :=
  P.comap inverseWorld (measurable_of_finite _)

instance physical_isMarkov
    (P : Kernel (WorldInput (StrategicState S0 S) X (∀ i, A i)) X) [IsMarkovKernel P] :
    IsMarkovKernel (physical P) := by unfold physical; infer_instance

noncomputable def compression :
    TypeRespectingStateCompression (StrategicState S0 S) X (GameState S0 (S 0) (S 1)) X where
  strategic := fun s => (s.1,(s.2 0,s.2 1))
  world := id
  strategic_measurable := measurable_of_finite _
  world_measurable := measurable_id
  strategic_surjective := by
    intro s
    refine ⟨(s.1,(MeasurableEquiv.piFinTwo S).symm s.2),?_⟩
    change (s.1,(MeasurableEquiv.piFinTwo S) ((MeasurableEquiv.piFinTwo S).symm s.2)) = s
    simp
  world_surjective := Function.surjective_id

@[simp] theorem compression_state (y : JointState (StrategicState S0 S) X) :
    compression.stateMap y = state y := rfl

theorem actual_atom (G : Generator S0 S X A)
    (P : Kernel (WorldInput (StrategicState S0 S) X (∀ i, A i)) X) [IsMarkovKernel P]
    (y z : JointState (StrategicState S0 S) X) :
    ((binary G).toModel (physical P)).inducedKernel (state y) {state z} =
      (G.toModel P).inducedKernel y {z} := by
  classical
  rw [Autonomous.product_transition_atom,Generator.actual_atom,← Fintype.sum_prod_type']
  symm
  apply Fintype.sum_equiv (MeasurableEquiv.piFinTwo A).toEquiv _ _
  intro a
  have ha : (MeasurableEquiv.piFinTwo A).symm (a 0,a 1) = a :=
    (MeasurableEquiv.piFinTwo A).symm_apply_apply a
  simp only [Fin.prod_univ_two,binary,Kernel.comap_apply,physical,
    inverseInput,inverseWorld,inverse_state]
  simp only [MeasurableEquiv.coe_toEquiv,MeasurableEquiv.piFinTwo_apply,ha,state]
  ring

theorem actual_intertwines (G : Generator S0 S X A)
    (P : Kernel (WorldInput (StrategicState S0 S) X (∀ i, A i)) X) [IsMarkovKernel P] :
    KernelIntertwines compression (G.toModel P).inducedKernel
      ((binary G).toModel (physical P)).inducedKernel := by
  classical
  apply Kernel.ext
  intro y
  rw [Kernel.map_apply _ compression.stateMap_measurable,Kernel.comap_apply]
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.map_apply compression.stateMap_measurable (measurableSet_singleton z)]
  have hset : compression.stateMap ⁻¹' ({z} : Set (JointState (GameState S0 (S 0) (S 1)) X)) =
      {inverseState z} := by
    ext w
    simp only [compression_state,Set.mem_preimage,Set.mem_singleton_iff]
    constructor
    · intro h
      simpa using congrArg inverseState h
    · intro h
      subst w
      exact state_inverse z
  rw [hset]
  simpa using (actual_atom G P y (inverseState z)).symm

theorem actual_pathLaw (G : Generator S0 S X A)
    (P : Kernel (WorldInput (StrategicState S0 S) X (∀ i, A i)) X) [IsMarkovKernel P]
    (μ : Measure (JointState (StrategicState S0 S) X)) [IsProbabilityMeasure μ] :
    ((G.toModel P).pathLaw μ).map compression.pathMap =
      ((binary G).toModel (physical P)).pathLaw (μ.map state) :=
  StrategicWorldModel.pathLaw_map_eq_of_kernelIntertwines compression _ _ (actual_intertwines G P) μ

end PermanssonResearch.MultiAgent.FiniteProduct.Two
