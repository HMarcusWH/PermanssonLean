import PermanssonLean.StrategicWorld.WellPosedness
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-!
# F1.1 — Two-player conditional-product strategic generators

Integration spec §6, (V20.28), for two players. The strategic state is
`S = S₀ × (S₁ × S₂)` (`S₀` common information, `Sᵢ` player `i`'s private state)
and the action space is `A₁ × A₂`. A `TwoPlayerGenerator` specifies

* player action kernels `αᵢ(daᵢ | s, x)`, combined as `α = α₁ ⊗ α₂`;
* private update kernels `Uᵢ(dsᵢ' | s, x, a, x')` and a common update `U₀`,
  combined as `U = U₀ ⊗ (U₁ ⊗ U₂)`.

`toGenerator` assembles an ordinary frozen `StrategicGenerator`, and `toModel`
pairs it with a COMMON world kernel `P` into a frozen `StrategicWorldModel`.
This is a declared SUBCLASS: given the current joint state the joint action law
is a product, so a state-conditional joint law such as the perfectly correlated
`correlatedLaw` is not produced by any `TwoPlayerGenerator`
(`ProtocolWitnesses.correlated_generator_not_product`). Correlation mediated by a
shared `S₀` coordinate (e.g. a public coin drawn by `U₀` and read by both players)
IS representable. Nothing here claims that games in general have independent
action/update kernels.
-/

namespace PermanssonResearch.MultiAgent

set_option autoImplicit false
open PermanssonLean

universe u0 u1 u2 uX uA1 uA2
variable {S0 : Type u0} {S1 : Type u1} {S2 : Type u2} {X : Type uX}
variable {A1 : Type uA1} {A2 : Type uA2}
variable [MeasurableSpace S0] [MeasurableSpace S1] [MeasurableSpace S2]
variable [MeasurableSpace X] [MeasurableSpace A1] [MeasurableSpace A2]

/-- Common coordinate `S0` and private player states `S1`, `S2`. -/
abbrev GameState (S0 : Type u0) (S1 : Type u1) (S2 : Type u2) := S0 × (S1 × S2)

variable (S0 S1 S2 X A1 A2) in
/-- Player 1's mechanism: action kernel and private-state update kernel. -/
structure PlayerOneMechanism where
  action : Kernel (JointState (GameState S0 S1 S2) X) A1
  update : Kernel (UpdateInput (GameState S0 S1 S2) X (A1 × A2)) S1
  action_isMarkov : IsMarkovKernel action
  update_isMarkov : IsMarkovKernel update

variable (S0 S1 S2 X A1 A2) in
/-- Player 2's mechanism (also the type of a declared opponent anchor). -/
structure PlayerTwoMechanism where
  action : Kernel (JointState (GameState S0 S1 S2) X) A2
  update : Kernel (UpdateInput (GameState S0 S1 S2) X (A1 × A2)) S2
  action_isMarkov : IsMarkovKernel action
  update_isMarkov : IsMarkovKernel update

variable (S0 S1 S2 X A1 A2) in
/-- **Two-player conditional-product subclass**: given the current joint state,
actions are drawn independently (`α = α₁ ⊗ α₂`); given the transition record,
the common and private updates are drawn independently. Correlated action models
outside this product form are NOT represented. -/
structure TwoPlayerGenerator where
  player1 : PlayerOneMechanism S0 S1 S2 X A1 A2
  player2 : PlayerTwoMechanism S0 S1 S2 X A1 A2
  common : Kernel (UpdateInput (GameState S0 S1 S2) X (A1 × A2)) S0
  common_isMarkov : IsMarkovKernel common

namespace TwoPlayerGenerator

/-- The frozen strategic generator `α = α₁ ⊗ α₂`, `U = U₀ ⊗ (U₁ ⊗ U₂)`. -/
noncomputable def toGenerator (G : TwoPlayerGenerator S0 S1 S2 X A1 A2) :
    StrategicGenerator (GameState S0 S1 S2) X (A1 × A2) where
  action := G.player1.action ×ₖ G.player2.action
  update := G.common ×ₖ (G.player1.update ×ₖ G.player2.update)
  action_isMarkov := by
    have := G.player1.action_isMarkov; have := G.player2.action_isMarkov
    infer_instance
  update_isMarkov := by
    have := G.common_isMarkov; have := G.player1.update_isMarkov
    have := G.player2.update_isMarkov
    infer_instance

/-- The canonical frozen model with the COMMON world kernel `P`. -/
noncomputable def toModel (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X)
    [hP : IsMarkovKernel P] : StrategicWorldModel (GameState S0 S1 S2) X (A1 × A2) :=
  ⟨G.toGenerator, P, hP⟩

/-- The joint action law of a product generator at any state is a product. -/
theorem toGenerator_action_apply (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (y : JointState (GameState S0 S1 S2) X) :
    G.toGenerator.action y = (G.player1.action y).prod (G.player2.action y) := by
  have := G.player1.action_isMarkov; have := G.player2.action_isMarkov
  exact Kernel.prod_apply _ _ _

/-- The update law of a product generator is `U₀ ⊗ (U₁ ⊗ U₂)` pointwise. -/
theorem toGenerator_update_apply (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (i : UpdateInput (GameState S0 S1 S2) X (A1 × A2)) :
    G.toGenerator.update i =
      (G.common i).prod ((G.player1.update i).prod (G.player2.update i)) := by
  have := G.common_isMarkov; have := G.player1.update_isMarkov
  have := G.player2.update_isMarkov
  change (G.common ×ₖ (G.player1.update ×ₖ G.player2.update)) i = _
  rw [Kernel.prod_apply, Kernel.prod_apply]

theorem toModel_world (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P] :
    (G.toModel P).world = P := rfl

end TwoPlayerGenerator

end PermanssonResearch.MultiAgent
