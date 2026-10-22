import PermanssonResearch.MultiAgent.AutonomousMarkedKernel
import PermanssonResearch.MultiAgent.MarkedCouplingCountermodel
import PermanssonResearch.X1.TypedModels
import Mathlib.Tactic

/-!
# M-02: typed opponent-mark countermodel, bounded source bridge

The opponent's sampled action is fair under the actual conditional-product
generator. Its private update records the sampled action when player one acts
false, and its negation when player one acts true. This module connects the
finite aligned/crossed arithmetic to actual source action/update rows and
proves the strict opponent-locked premise fails.

The entire one-step history kernel pushed through opponentMark still needs a
separate compiled atom identity before full historical M-02 acceptance.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace PermanssonResearch.MultiAgent.MarkedStrategicPathCountermodel

open PermanssonLean
open PermanssonResearch.MultiAgent
open PermanssonResearch.MultiAgent.Autonomous
open PermanssonResearch.X1 (coin coin_probability coin_true coin_false)

set_option autoImplicit false

abbrev Y := State Unit Unit Bool Unit
abbrev UI := UpdateInput (GameState Unit Unit Bool) Unit (Bool × Bool)
abbrev WI := WorldInput (GameState Unit Unit Bool) Unit (Bool × Bool)

noncomputable def player (t : Bool) :
    PlayerOneMechanism Unit Unit Bool Unit Bool Bool where
  action := Kernel.deterministic (fun _ : Y => t) Measurable.of_discrete
  update := Kernel.deterministic (fun _ : UI => ()) Measurable.of_discrete
  action_isMarkov := by infer_instance
  update_isMarkov := by infer_instance

noncomputable def opponent : PlayerTwoMechanism Unit Unit Bool Unit Bool Bool where
  action := Kernel.const Y (coin (1/2))
  update := Kernel.deterministic
    (fun i : UI => if i.1.2.1 then !i.1.2.2 else i.1.2.2)
    Measurable.of_discrete
  action_isMarkov := by
    letI : IsProbabilityMeasure (coin (1/2)) :=
      coin_probability _ (by norm_num)
    infer_instance
  update_isMarkov := by infer_instance

noncomputable def world : Kernel WI Unit :=
  Kernel.const WI (Measure.dirac ())

instance world_isMarkov : IsMarkovKernel world := by
  unfold world
  infer_instance

noncomputable def game : TwoPlayerGenerator Unit Unit Bool Unit Bool Bool where
  player1 := player false
  player2 := opponent
  common := Kernel.const UI (Measure.dirac ())
  common_isMarkov := by infer_instance

theorem same_physical_P_for_both_actual_protocols :
    ((game.openLoop (player false) opponent).toModel world).world =
      ((game.openLoop (player true) opponent).toModel world).world := rfl

def markedNextKey (t b : Bool) : Bool :=
  if t then !b else b

def sourceInput (t b old : Bool) : UI :=
  ((((((), ((), old)), ()), (t,b)), ())

/-- The opponent's actual private update uses both sampled actions, in the
actual update-input type of the original TwoPlayerGenerator. -/
theorem actual_opponent_private_update (t b old : Bool) :
    opponent.update (sourceInput t b old) =
      Measure.dirac (markedNextKey t b) := by
  change Kernel.deterministic
      (fun i : UI => if i.1.2.1 then !i.1.2.2 else i.1.2.2)
      Measurable.of_discrete (sourceInput t b old) = _
  rw [Kernel.deterministic_apply]
  rfl

def markerInput (t : Bool) : UI := sourceInput t false false

theorem same_allowed_anchor_update_key :
    anchorUpdateKey (markerInput false) =
      anchorUpdateKey (markerInput true) := rfl

theorem unequal_actual_update_rows :
    opponent.update (markerInput false) ≠
      opponent.update (markerInput true) := by
  intro heq
  have h := congrArg (fun μ : Measure Bool => μ {true}) heq
  simp [opponent, markerInput, sourceInput,
    Kernel.deterministic_apply, Measure.dirac_apply'] at h

/-- The genuine original strict factorization premise is false because the
update law depends on player one's current action at identical opponent keys. -/
theorem original_strict_anchor_premise_rejected :
    ¬ IsStrictlyNonReactive opponent := by
  intro h
  exact unequal_actual_update_rows
    (h.update_eq same_allowed_anchor_update_key)

theorem actual_opponent_action_fair (y : Y) :
    opponent.action y {true} = ENNReal.ofReal (1/2 : ℝ) ∧
    opponent.action y {false} = ENNReal.ofReal (1/2 : ℝ) := by
  constructor
  · change (coin (1/2)) {true} = _
    simpa using coin_true (1/2)
  · change (coin (1/2)) {false} = _
    rw [coin_false]
    norm_num

/-- Finite exact marked rows obtained from the source's measured action law
and the deterministic opponent update, not an independent key lottery. -/
def actualMarkedAtom (t opponentAction nextKey : Bool) : ℚ :=
  if nextKey = markedNextKey t opponentAction then 1/2 else 0

theorem source_aligned_atom (a k : Bool) :
    actualMarkedAtom false a k =
      (if k = a then (1/2 : ℚ) else 0) := by
  cases a <;> cases k <;> norm_num [actualMarkedAtom, markedNextKey]

theorem source_crossed_atom (a k : Bool) :
    actualMarkedAtom true a k =
      (if k ≠ a then (1/2 : ℚ) else 0) := by
  cases a <;> cases k <;> norm_num [actualMarkedAtom, markedNextKey]

def nextKeyMass (t k : Bool) : ℚ :=
  ∑ a : Bool, actualMarkedAtom t a k

theorem unmarked_key_laws_identical (k : Bool) :
    nextKeyMass false k = nextKeyMass true k ∧
    nextKeyMass false k = (1/2 : ℚ) := by
  cases k <;> norm_num [nextKeyMass, actualMarkedAtom,
    markedNextKey, Fintype.sum_bool]

def diagonalMass (t : Bool) : ℚ :=
  ∑ a : Bool, actualMarkedAtom t a a

theorem marked_diagonal_separates :
    diagonalMass false = 1 ∧ diagonalMass true = 0 := by
  norm_num [diagonalMass, actualMarkedAtom,
    markedNextKey, Fintype.sum_bool]

theorem unmarked_not_strict_certificate :
    (∀ k : Bool, nextKeyMass false k = nextKeyMass true k) ∧
      ¬ IsStrictlyNonReactive opponent := by
  exact ⟨fun k => (unmarked_key_laws_identical k).1,
    original_strict_anchor_premise_rejected⟩

end PermanssonResearch.MultiAgent.MarkedStrategicPathCountermodel
