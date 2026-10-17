import PermanssonResearch.MultiAgent.ProductGame
import PermanssonLean.Intervention.Apply
import PermanssonLean.Regime.Property

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-!
# F1.2 — Closed-loop and opponent-locked protocols as typed interventions

Integration spec §6. Fix the treated player — in this formalization ALWAYS
player 1 (treating player 2 is not formalized) — and a declared replacement
`r = (α₁', U₁')`.

* `closedLoop G r` replaces player 1 ONLY; the opponent's functional kernels,
  the common update `U₀` and `P` are untouched, so the opponent's state and
  actions may respond to the counterfactual history (`J_CL`).
* `openLoop G r anchor` ALSO installs a declared opponent anchor `(ᾱ₂, Ū₂)`
  from an ex-ante declared menu (`J_OL`). `U₀` and `P` are still untouched.

Both protocols are frozen typed interventions of ONE `InterventionFamily` whose
single component kind is `jointStrategic`, so the frozen grammar guarantees that
`P` is held fixed (`protocol_world_eq`, from the frozen
`AdmissibleStrategicIntervention.world_eq`). Admissibility is EXACTLY: the CL
generator for `r`, or an OL generator for `r` and an anchor from the menu
(`protocol_admissible_cases`).

**Two readings of "non-reactive anchor".** The spec asks for a "frozen, ex-ante
declared non-reactive anchor".
* `protocolFamily G P r anchors` admits ANY declared anchor kernel (the "frozen
  declared kernel" reading). This is the reading under which MA2 is
  non-vacuous: anchors may differ off baseline support only if they can read
  coordinates whose reachable values the intervention changes. Under this
  reading non-reactivity is NOT enforced; it is the menu's responsibility, and
  if the menu contains the baseline opponent `G.player2` the OL label carries the
  CL generator (`openLoop_self`).
* `IsStrictlyNonReactive a` is the strict reading: the anchor's action reads only
  the common coordinate `S₀` and its OWN private state `S₂`, and its update reads
  only those and its OWN action. `protocolFamily G P r (strictAnchors anchors)` is
  the strict family. Even then `S₀` is updated by the common `U₀`, which may read
  player 1's action, so exogeneity of `S₀` is a separate modelling obligation.
  A nonstationary (clocked) anchor needs its clock in a state coordinate that
  the protocol can actually update: either the BASELINE `S₀` with the baseline
  `U₀` (protocols never change `U₀`), or the anchor's OWN `S₂` through the
  anchor's own update (when the `S₂` type can hold the clock, at the cost of
  `S₂`'s baseline meaning).

Typed action feasibility of anchors is not encoded; it is a property the menu
must satisfy.
-/

namespace PermanssonResearch.MultiAgent

set_option autoImplicit false
open PermanssonLean

universe u0 u1 u2 uX uA1 uA2
variable {S0 : Type u0} {S1 : Type u1} {S2 : Type u2} {X : Type uX}
variable {A1 : Type uA1} {A2 : Type uA2}
variable [MeasurableSpace S0] [MeasurableSpace S1] [MeasurableSpace S2]
variable [MeasurableSpace X] [MeasurableSpace A1] [MeasurableSpace A2]

namespace TwoPlayerGenerator

/-- Closed loop: replace player 1 only; the opponent's mechanism is untouched
and may respond to the counterfactual history. -/
def closedLoop (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2) : TwoPlayerGenerator S0 S1 S2 X A1 A2 :=
  { G with player1 := r }

/-- Opponent-locked: replace player 1 AND install a declared opponent anchor. -/
def openLoop (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2)
    (anchor : PlayerTwoMechanism S0 S1 S2 X A1 A2) : TwoPlayerGenerator S0 S1 S2 X A1 A2 :=
  { G with player1 := r, player2 := anchor }

@[simp] theorem closedLoop_player2 (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2) : (G.closedLoop r).player2 = G.player2 := rfl

@[simp] theorem closedLoop_common (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2) : (G.closedLoop r).common = G.common := rfl

@[simp] theorem openLoop_player2 (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2) (a : PlayerTwoMechanism S0 S1 S2 X A1 A2) :
    (G.openLoop r a).player2 = a := rfl

/-- With the baseline opponent as anchor, the two protocols coincide: a menu
containing `G.player2` lets the OL label carry the CL generator. -/
theorem openLoop_self (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2) :
    G.openLoop r G.player2 = G.closedLoop r := rfl

end TwoPlayerGenerator

/-- Key read by a strictly non-reactive anchor's action: `(s₀, s₂)`. -/
def anchorKey (y : JointState (GameState S0 S1 S2) X) : S0 × S2 := (y.1.1, y.1.2.2)

/-- Key read by a strictly non-reactive anchor's update: `((s₀, s₂), a₂)`. -/
def anchorUpdateKey (u : UpdateInput (GameState S0 S1 S2) X (A1 × A2)) : (S0 × S2) × A2 :=
  (anchorKey u.1.1, u.1.2.2)

theorem measurable_anchorKey :
    Measurable (anchorKey (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) := by
  unfold anchorKey; fun_prop

theorem measurable_anchorUpdateKey :
    Measurable (anchorUpdateKey (S0 := S0) (S1 := S1) (S2 := S2) (X := X) (A1 := A1)
      (A2 := A2)) := by
  unfold anchorUpdateKey anchorKey; fun_prop

/-- **Strict non-reactivity.** The anchor's action kernel factors through
`(s₀, s₂)` and its update kernel through `((s₀, s₂), a₂)`: it never reads player
1's private state, the world state or player 1's action. -/
structure IsStrictlyNonReactive (a : PlayerTwoMechanism S0 S1 S2 X A1 A2) : Prop where
  action_factors : ∃ ā : Kernel (S0 × S2) A2, a.action = ā.comap anchorKey measurable_anchorKey
  update_factors : ∃ ū : Kernel ((S0 × S2) × A2) S2,
    a.update = ū.comap anchorUpdateKey measurable_anchorUpdateKey

/-- A strictly non-reactive anchor plays the same action law at any two states
with the same `(s₀, s₂)`. -/
theorem IsStrictlyNonReactive.action_eq {a : PlayerTwoMechanism S0 S1 S2 X A1 A2}
    (ha : IsStrictlyNonReactive a) {y y' : JointState (GameState S0 S1 S2) X}
    (h : anchorKey y = anchorKey y') : a.action y = a.action y' := by
  obtain ⟨ā, hā⟩ := ha.action_factors
  rw [hā, Kernel.comap_apply, Kernel.comap_apply, h]

/-- The strict sub-menu. -/
def strictAnchors (anchors : Set (PlayerTwoMechanism S0 S1 S2 X A1 A2)) :
    Set (PlayerTwoMechanism S0 S1 S2 X A1 A2) :=
  {a | a ∈ anchors ∧ IsStrictlyNonReactive a}

/-- The two protocol labels. -/
inductive Protocol
  | closedLoop
  | openLoop

open TwoPlayerGenerator in
/-- Frozen protocol family on the product model: one joint-strategic component
per protocol; the admissible replacements are exactly the CL generator for the
declared player-1 replacement `r`, and OL generators for `r` with an anchor from
the ex-ante declared menu `anchors`. `P` is never replaced. -/
noncomputable def protocolFamily (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2)
    (anchors : Set (PlayerTwoMechanism S0 S1 S2 X A1 A2)) :
    InterventionFamily (G.toModel P) Protocol where
  targetOf _ := .jointStrategic
  admissible
    | .closedLoop, gen => gen = (G.closedLoop r).toGenerator
    | .openLoop, gen => ∃ a ∈ anchors, gen = (G.openLoop r a).toGenerator

open TwoPlayerGenerator in
/-- `J_CL` as a bundled admissible strategic intervention. -/
noncomputable def closedLoopIntervention (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2)
    (anchors : Set (PlayerTwoMechanism S0 S1 S2 X A1 A2)) :
    AdmissibleStrategicIntervention (protocolFamily G P r anchors) where
  intervention := ⟨.closedLoop, (G.closedLoop r).toGenerator⟩
  accepted := rfl
  strategic := InterventionTarget.isStrategic_jointStrategic

open TwoPlayerGenerator in
/-- `J_OL` for a declared anchor `a ∈ anchors`. -/
noncomputable def openLoopIntervention (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2)
    (anchors : Set (PlayerTwoMechanism S0 S1 S2 X A1 A2))
    (a : PlayerTwoMechanism S0 S1 S2 X A1 A2) (ha : a ∈ anchors) :
    AdmissibleStrategicIntervention (protocolFamily G P r anchors) where
  intervention := ⟨.openLoop, (G.openLoop r a).toGenerator⟩
  accepted := ⟨a, ha, rfl⟩
  strategic := InterventionTarget.isStrategic_jointStrategic

open TwoPlayerGenerator in
theorem closedLoop_apply (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2)
    (anchors : Set (PlayerTwoMechanism S0 S1 S2 X A1 A2)) :
    (closedLoopIntervention G P r anchors).intervention.apply =
      (G.closedLoop r).toModel P := rfl

open TwoPlayerGenerator in
theorem openLoop_apply (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2)
    (anchors : Set (PlayerTwoMechanism S0 S1 S2 X A1 A2))
    (a : PlayerTwoMechanism S0 S1 S2 X A1 A2) (ha : a ∈ anchors) :
    (openLoopIntervention G P r anchors a ha).intervention.apply =
      (G.openLoop r a).toModel P := rfl

/-- Every admissible protocol intervention keeps the COMMON world kernel `P`
(the frozen strategic-intervention guarantee). -/
theorem protocol_world_eq (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2)
    (anchors : Set (PlayerTwoMechanism S0 S1 S2 X A1 A2))
    (J : AdmissibleStrategicIntervention (protocolFamily G P r anchors)) :
    J.intervention.apply.world = P :=
  J.world_eq

open TwoPlayerGenerator in
/-- Every admissible protocol intervention replaces player 1 by the declared
`r`: its generator is the product generator of `closedLoop G r` or of
`openLoop G r a` for a menu anchor `a`. -/
theorem protocol_admissible_cases (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2)
    (anchors : Set (PlayerTwoMechanism S0 S1 S2 X A1 A2))
    (J : AdmissibleStrategicIntervention (protocolFamily G P r anchors)) :
    J.intervention.apply = (G.closedLoop r).toModel P ∨
      ∃ a ∈ anchors, J.intervention.apply = (G.openLoop r a).toModel P := by
  obtain ⟨⟨c, gen⟩, hacc, -⟩ := J
  cases c with
  | closedLoop =>
      left
      change ({ (G.toModel P) with generator := gen } : StrategicWorldModel _ _ _) = _
      rw [show gen = (G.closedLoop r).toGenerator from hacc]
      rfl
  | openLoop =>
      right
      obtain ⟨a, ha, hgen⟩ := hacc
      refine ⟨a, ha, ?_⟩
      change ({ (G.toModel P) with generator := gen } : StrategicWorldModel _ _ _) = _
      rw [show gen = (G.openLoop r a).toGenerator from hgen]
      rfl

end PermanssonResearch.MultiAgent
