import PermanssonResearch.MultiAgent.PlayerSwapTransport
import PermanssonResearch.X1.TypedModels
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


/-- The initial source is deliberately NON-DIRAC. Both physical world
values and both common-state values occur before the first action; no
single favorable start is substituted for the original all-initial theorem. -/
def mixedInitialState (b : Bool) :
    JointState (GameState Bool Unit Unit) Bool :=
  ((b, ((), ())), b)

noncomputable def mixedInitialLaw :
    Measure (JointState (GameState Bool Unit Unit) Bool) :=
  (PermanssonResearch.X1.coin (1/2)).map mixedInitialState

instance mixedInitialLaw_isProbability : IsProbabilityMeasure mixedInitialLaw := by
  unfold mixedInitialLaw
  haveI : IsProbabilityMeasure (PermanssonResearch.X1.coin (1/2)) :=
    PermanssonResearch.X1.coin_probability (1/2) (by norm_num)
  infer_instance

theorem mixed_starts_distinct :
    mixedInitialState false ≠ mixedInitialState true := by decide

theorem mixedPreimage_false :
    mixedInitialState ⁻¹' ({mixedInitialState false} :
        Set (JointState (GameState Bool Unit Unit) Bool)) =
      ({false} : Set Bool) := by
  ext b
  cases b <;> simp [mixedInitialState]

theorem mixedPreimage_true :
    mixedInitialState ⁻¹' ({mixedInitialState true} :
        Set (JointState (GameState Bool Unit Unit) Bool)) =
      ({true} : Set Bool) := by
  ext b
  cases b <;> simp [mixedInitialState]

theorem mixed_initial_positive_each_state :
    mixedInitialLaw {mixedInitialState false} =
      ENNReal.ofReal (1/2 : ℝ) ∧
    mixedInitialLaw {mixedInitialState true} =
      ENNReal.ofReal (1/2 : ℝ) := by
  constructor
  · rw [mixedInitialLaw,
        Measure.map_apply (by fun_prop)
          (measurableSet_singleton (mixedInitialState false))]
    rw [mixedPreimage_false, PermanssonResearch.X1.coin_false]
    norm_num
  · rw [mixedInitialLaw,
        Measure.map_apply (by fun_prop)
          (measurableSet_singleton (mixedInitialState true))]
    rw [mixedPreimage_true]
    exact PermanssonResearch.X1.coin_true (1/2)

/-- A path distribution with two positive distinct time-zero atoms
cannot equal the earlier point-started Dirac initial distribution. -/
theorem mixed_initial_not_point_mass :
    mixedInitialLaw ≠ Measure.dirac (mixedInitialState false) := by
  intro h
  have hm := congrArg
    (fun μ : Measure (JointState (GameState Bool Unit Unit) Bool) =>
      μ {mixedInitialState true}) h
  rw [mixed_initial_positive_each_state.2] at hm
  simp [Measure.dirac_apply', mixed_starts_distinct] at hm

/-- Genuine asymmetric source transport for a mixed ORIGINAL initial law.
It is an instance of the existing all-measurable-event whole-path theorem;
the physical/world input is reindexed, not assumed symmetric. -/
theorem asymmetric_mixed_original_path_law_transport :
    ((generator.toModel physicalFromFirstAction).pathLaw mixedInitialLaw).map
      (PlayerSwap.compression (S0 := Bool) (S1 := Unit)
        (S2 := Unit) (X := Bool)).pathMap =
      ((PlayerSwap.generator generator).toModel
        (PlayerSwap.physical physicalFromFirstAction)).pathLaw
          (mixedInitialLaw.map PlayerSwap.state) := by
  exact PlayerSwap.actual_pathLaw generator physicalFromFirstAction
    mixedInitialLaw

end PermanssonResearch.MultiAgent.AsymmetricCommonSwapFixture
