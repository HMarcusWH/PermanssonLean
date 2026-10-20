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
  rw [Kernel.map_apply _ (MeasurableEquiv.piFinTwo A).measurable,
    Kernel.comap_apply]
  exact action_map_two G y

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
  rw [Kernel.map_apply _ measurable_strategicMap,
    Kernel.comap_apply]
  simpa only [forwardUpdate, forwardWorld] using update_map_two G y a x


/-- The inner alpha-to-world-to-update expression is a genuine measurable
function of the realized action. Use the *actual* conditional kernels, not a
new hand-picked action probability or an atomwise finite restriction. -/
private theorem measurable_native_inner
    {S' X' A' : Type*} [MeasurableSpace S']
    [MeasurableSpace X'] [MeasurableSpace A']
    (M : StrategicWorldModel S' X' A')
    (y : JointState S' X')
    {E : Set (JointState S' X')} (hE : MeasurableSet E) :
    Measurable (fun a : A' =>
      ∫⁻ x, M.generator.update ((y, a), x)
          {s : S' | (s, x) ∈ E} ∂M.world (y, a)) := by
  letI : IsMarkovKernel M.world := M.world_isMarkov
  letI : IsMarkovKernel M.generator.update := M.generator.update_isMarkov
  let κ : Kernel A' X' :=
    M.world.comap (fun a => (y, a)) (by fun_prop)
  let η : Kernel (A' × X') S' :=
    M.generator.update.comap (fun ax => ((y, ax.1), ax.2)) (by fun_prop)
  let R : Set (X' × S') := {z | (z.2, z.1) ∈ E}
  have hR : MeasurableSet R :=
    hE.preimage (measurable_snd.prodMk measurable_fst)
  have hm : Measurable (fun a : A' => (κ ⊗ₖ η) a R) :=
    Kernel.measurable_coe _ hR
  have heq :
      (fun a : A' => (κ ⊗ₖ η) a R) =
      (fun a : A' => ∫⁻ x, M.generator.update ((y, a), x)
          {s : S' | (s, x) ∈ E} ∂M.world (y, a)) := by
    funext a
    rw [Kernel.compProd_apply hR κ η a]
    rfl
  rw [heq] at hm
  exact hm

/-- Native alpha-P-U transition law, not just equality of component kernels.
Every measurable joint event is transported through the true physical world
law, the complete common/private strategic update, and both action rows. -/
theorem induced_row_map_two (G : Generator S0 S X A)
    (P : Kernel (WorldInput (StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P]
    (y : JointState (StrategicState S0 S) X) :
    ((model G P).inducedKernel y).map state =
      ((binary G).toModel (physical P)).inducedKernel (state y) := by
  letI : IsMarkovKernel (physical P) := physical_isMarkov P
  let MF := model G P
  let MB := (binary G).toModel (physical P)
  apply Measure.ext
  intro E hE
  have hstate : Measurable (state (S0 := S0) (S := S) (X := X)) :=
    measurable_state
  have hpre : MeasurableSet (state ⁻¹' E) := hE.preimage hstate
  have hsection (x : X) :
      MeasurableSet {s : GameState S0 (S 0) (S 1) | (s, x) ∈ E} :=
    hE.preimage (measurable_id.prodMk measurable_const)
  have hinner (a : ∀ i, A i) (x : X) :
      MF.generator.update ((y, a), x)
        {s : StrategicState S0 S | state (s, x) ∈ E} =
      MB.generator.update
        ((state y, (MeasurableEquiv.piFinTwo A) a), x)
        {s : GameState S0 (S 0) (S 1) | (s, x) ∈ E} := by
    have hm := congrArg
      (fun μ : Measure (GameState S0 (S 0) (S 1)) =>
        μ {s : GameState S0 (S 0) (S 1) | (s, x) ∈ E})
      (update_map_two G y a x)
    rw [Measure.map_apply measurable_strategicMap (hsection x)] at hm
    change ((assemble G).update ((y, a), x))
        (strategicMap ⁻¹' {s : GameState S0 (S 0) (S 1) | (s, x) ∈ E}) =
      ((binary G).toGenerator).update
        ((state y, (MeasurableEquiv.piFinTwo A) a), x)
        {s : GameState S0 (S 0) (S 1) | (s, x) ∈ E}
    exact hm
  have hrow (a : ∀ i, A i) :
      (∫⁻ x, MF.generator.update ((y, a), x)
        {s : StrategicState S0 S | state (s, x) ∈ E} ∂MF.world (y, a)) =
      (∫⁻ x, MB.generator.update
        ((state y, (MeasurableEquiv.piFinTwo A) a), x)
        {s : GameState S0 (S 0) (S 1) | (s, x) ∈ E}
        ∂MB.world (state y, (MeasurableEquiv.piFinTwo A) a)) := by
    change (∫⁻ x, MF.generator.update ((y, a), x)
        {s : StrategicState S0 S | state (s, x) ∈ E} ∂P (y, a)) = _
    rw [show MB.world (state y, (MeasurableEquiv.piFinTwo A) a) = P (y, a) from
      world_pullback_two P y a]
    exact lintegral_congr fun x => hinner a x
  have hmeas :
      Measurable (fun ab : A 0 × A 1 =>
        ∫⁻ x, MB.generator.update ((state y, ab), x)
          {s : GameState S0 (S 0) (S 1) | (s, x) ∈ E}
          ∂MB.world (state y, ab)) :=
    measurable_native_inner MB (state y) hE
  calc
    ((MF.inducedKernel y).map state) E =
        ∫⁻ a, ∫⁻ x, MF.generator.update ((y, a), x)
          {s : StrategicState S0 S | state (s, x) ∈ E}
          ∂MF.world (y, a) ∂MF.generator.action y := by
      rw [Measure.map_apply hstate hE]
      rw [StrategicWorldModel.inducedKernel_apply MF y hpre]
      rfl
    _ = ∫⁻ a, (fun ab : A 0 × A 1 =>
          ∫⁻ x, MB.generator.update ((state y, ab), x)
            {s : GameState S0 (S 0) (S 1) | (s, x) ∈ E}
            ∂MB.world (state y, ab)) ((MeasurableEquiv.piFinTwo A) a)
            ∂MF.generator.action y :=
      lintegral_congr fun a => hrow a
    _ = ∫⁻ ab, ∫⁻ x, MB.generator.update ((state y, ab), x)
          {s : GameState S0 (S 0) (S 1) | (s, x) ∈ E}
          ∂MB.world (state y, ab)
          ∂(MF.generator.action y).map (MeasurableEquiv.piFinTwo A) := by
      exact (lintegral_map hmeas (MeasurableEquiv.piFinTwo A).measurable).symm
    _ = ∫⁻ ab, ∫⁻ x, MB.generator.update ((state y, ab), x)
          {s : GameState S0 (S 0) (S 1) | (s, x) ∈ E}
          ∂MB.world (state y, ab) ∂MB.generator.action (state y) := by
      rw [show (MF.generator.action y).map (MeasurableEquiv.piFinTwo A) =
        MB.generator.action (state y) from action_map_two G y]
    _ = MB.inducedKernel (state y) E :=
      (StrategicWorldModel.inducedKernel_apply MB (state y) hE).symm

/-- Full original type-respecting kernel intertwining, without atomwise
finite enumeration or additional independent physical-error premises. -/
theorem induced_kernel_intertwines_two (G : Generator S0 S X A)
    (P : Kernel (WorldInput (StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] :
    KernelIntertwines
      (compression_two (S0 := S0) (S := S) (X := X))
      (model G P).inducedKernel
      ((binary G).toModel (physical P)).inducedKernel := by
  unfold KernelIntertwines
  apply Kernel.ext
  intro y
  rw [Kernel.map_apply _ (compression_two
    (S0 := S0) (S := S) (X := X)).stateMap_measurable,
    Kernel.comap_apply]
  have hstateEq :
      (compression_two (S0 := S0) (S := S) (X := X)).stateMap =
        (state (S0 := S0) (S := S) (X := X)) := by
    funext z
    exact compression_two_state z
  rw [hstateEq]
  exact induced_row_map_two G P y

end PermanssonResearch.MultiAgent.MeasurableProduct.Two
