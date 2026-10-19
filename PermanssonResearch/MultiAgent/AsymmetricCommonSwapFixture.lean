import PermanssonResearch.MultiAgent.PlayerSwapTransport
import Mathlib.Tactic

/-!
NEXT-03 / F-01: asymmetric world AND common-update input swap.

The first action is false and the second true under the actual baseline
generator. A physical kernel and the common strategic update both read the
first action, not a symmetric joint statistic. Correct player transport
changes that input to true; an unswapped pullback would remain false.
-/

open MeasureTheory ProbabilityTheory Set PermanssonLean
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultiAgent.AsymmetricCommonSwapFixture

noncomputable def firstPlayer :
    PlayerOneMechanism Bool Unit Unit Bool Bool Bool where
  action := Kernel.const _ (Measure.dirac false)
  update := Kernel.const _ (Measure.dirac ())
  action_isMarkov := inferInstance
  update_isMarkov := inferInstance

noncomputable def secondPlayer :
    PlayerTwoMechanism Bool Unit Unit Bool Bool Bool where
  action := Kernel.const _ (Measure.dirac true)
  update := Kernel.const _ (Measure.dirac ())
  action_isMarkov := inferInstance
  update_isMarkov := inferInstance

noncomputable def commonFromFirstAction :
    Kernel (UpdateInput (GameState Bool Unit Unit) Bool (Bool × Bool)) Bool :=
  Kernel.deterministic (fun i => i.1.2.1) (by fun_prop)

instance : IsMarkovKernel commonFromFirstAction := by
  unfold commonFromFirstAction
  infer_instance

noncomputable def generator : TwoPlayerGenerator Bool Unit Unit Bool Bool Bool where
  player1 := firstPlayer
  player2 := secondPlayer
  common := commonFromFirstAction
  common_isMarkov := inferInstance

noncomputable def physicalFromFirstAction :
    Kernel (WorldInput (GameState Bool Unit Unit) Bool (Bool × Bool)) Bool :=
  Kernel.deterministic (fun i => i.2.1) (by fun_prop)

instance : IsMarkovKernel physicalFromFirstAction := by
  unfold physicalFromFirstAction
  infer_instance

def initial : JointState (GameState Bool Unit Unit) Bool :=
  ((false, ((), ())), false)

def liveWorldInput :
    WorldInput (GameState Bool Unit Unit) Bool (Bool × Bool) :=
  (initial, (false, true))

def liveUpdateInput :
    UpdateInput (GameState Bool Unit Unit) Bool (Bool × Bool) :=
  (liveWorldInput, false)

/-- Both action values occur in the actual constructed joint action row. -/
theorem actual_player_action_rows :
    generator.player1.action initial {false} = 1 ∧
      generator.player2.action initial {true} = 1 := by
  simp [generator, firstPlayer, secondPlayer,
    Kernel.const_apply, Measure.dirac_apply]

/-- At this realized action, the correct world-input swap is observable. -/
theorem real_physical_pullback_changes_asymmetric_input :
    (PlayerSwap.physical physicalFromFirstAction) liveWorldInput {true} = 1 ∧
      physicalFromFirstAction liveWorldInput {true} = 0 := by
  simp [PlayerSwap.physical, PlayerSwap.worldInput, PlayerSwap.state,
    PlayerSwap.strategic, physicalFromFirstAction, liveWorldInput, initial,
    Kernel.comap_apply, Kernel.deterministic_apply, Measure.dirac_apply]

/-- Common update is reindexed too, rather than accidentally left untouched. -/
theorem real_common_update_pullback_changes_input :
    (PlayerSwap.generator generator).common liveUpdateInput {true} = 1 ∧
      generator.common liveUpdateInput {true} = 0 := by
  simp [PlayerSwap.generator, PlayerSwap.updateInput,
    PlayerSwap.worldInput, PlayerSwap.state, PlayerSwap.strategic,
    generator, commonFromFirstAction, liveUpdateInput, liveWorldInput, initial,
    Kernel.comap_apply, Kernel.deterministic_apply, Measure.dirac_apply]

/-- The old-to-new canonical path-law identity is instantiated on THIS
asymmetric original typed model and its actual point-started law. -/
theorem asymmetric_original_path_law_transport :
    ((generator.toModel physicalFromFirstAction).pathLaw (Measure.dirac initial)).map
      (PlayerSwap.compression (S0 := Bool) (S1 := Unit)
        (S2 := Unit) (X := Bool)).pathMap =
      ((PlayerSwap.generator generator).toModel
        (PlayerSwap.physical physicalFromFirstAction)).pathLaw
          ((Measure.dirac initial).map PlayerSwap.state) := by
  exact PlayerSwap.actual_pathLaw generator physicalFromFirstAction
    (Measure.dirac initial)

end PermanssonResearch.MultiAgent.AsymmetricCommonSwapFixture
