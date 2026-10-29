import PermanssonResearch.MultiAgent.MarkedStrategicPathCountermodel
import PermanssonResearch.MultiAgent.AutonomousMarkedKernel
import Mathlib.Tactic

/-!
# M-02 actual conditional-product marked history source

Two genuinely admitted strict opponent update mechanisms have fair sampled
opponent actions and the same unmarked next-key distribution. One records
a₂; the other records ¬a₂. We instantiate the ORIGINAL alpha -> P -> U
oneStepHistoryKernel and its opponentMark pushforward, rather than assuming
that an arbitrary independent key lottery describes the source.

This does NOT refute the strict MA2 path-law obstruction: the two anchors
do not satisfy baseline mechanism agreement, which remains mandatory.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultiAgent.M02ActualMarkedHistoryFixture

open PermanssonLean
open PermanssonResearch.MultiAgent
open PermanssonResearch.MultiAgent.Autonomous
open PermanssonResearch.MultiAgent.MarkedStrategicPathCountermodel
open PermanssonResearch.X1 (coin coin_probability coin_true coin_false)

set_option autoImplicit false

noncomputable def fairActionFactor : Kernel (Unit × Bool) Bool :=
  Kernel.const _ (coin (1/2))

noncomputable def markedUpdateFactor (twist : Bool) :
    Kernel ((Unit × Bool) × Bool) Bool :=
  Kernel.deterministic
    (fun i => if twist then !i.2 else i.2) Measurable.of_discrete

/-- Actual source opponent action/update rows factor through strictly the
original anchorKey/anchorUpdateKey. They never read player one's action. -/
noncomputable def strictAnchor (twist : Bool) :
    PlayerTwoMechanism Unit Unit Bool Unit Bool Bool where
  action := (fairActionFactor).comap anchorKey measurable_anchorKey
  update := (markedUpdateFactor twist).comap
    anchorUpdateKey measurable_anchorUpdateKey
  action_isMarkov := by
    letI : IsProbabilityMeasure (coin (1/2)) :=
      coin_probability _ (by norm_num)
    unfold fairActionFactor
    infer_instance
  update_isMarkov := by
    unfold markedUpdateFactor
    infer_instance

theorem strictAnchor_isStrict (twist : Bool) :
    IsStrictlyNonReactive (strictAnchor twist) := by
  exact ⟨⟨fairActionFactor, rfl⟩,
         ⟨markedUpdateFactor twist, rfl⟩⟩

/-- Unlike an assumed arbitrary probability coupling, this profile records
the exact factor kernels that reconstruct the actual typed source. -/
noncomputable def sourceProfile (twist : Bool) :
    Profile game (strictAnchor twist) where
  common := Kernel.const Unit (Measure.dirac ())
  action := fairActionFactor
  update := markedUpdateFactor twist
  common_eq := rfl
  action_eq := rfl
  update_eq := rfl

/-- This marked probability is ACTUALLY the sampled opponent action and the
next common/private opponent state of the original one-step history law. -/
noncomputable def markedLaw (twist : Bool) (y : Y) :
    Measure (Bool × (Unit × Bool)) :=
  ((((game.openLoop (player false) (strictAnchor twist)).toModel world).oneStepHistoryKernel y).map
    (opponentMark (S0 := Unit) (S1 := Unit) (S2 := Bool)
      (X := Unit) (A1 := Bool) (A2 := Bool)))

theorem markedLaw_actual_source_atom (twist : Bool) (y : Y) (b k : Bool) :
    markedLaw twist y {(b, ((), k))} =
      (coin (1/2)) {b} *
        (if k = (if twist then !b else b) then 1 else 0) := by
  classical
  have h := autonomous_marked_atom game world
    (strictAnchor twist) (sourceProfile twist) (player false)
    y b ((), k)
  -- In the finite Boolean source the only residual after the actual marked
  -- atom theorem is Pi.single's indicator. Resolve the eight exact source
  -- atoms rather than replacing the original history kernel with a table.
  cases twist <;> cases b <;> cases k <;>
    simpa [markedLaw, sourceProfile, fairActionFactor, markedUpdateFactor,
      Kernel.const_apply, Kernel.deterministic_apply,
      Measure.dirac_apply', Kernel.comap_apply,
      markedNextKey, Pi.single_apply] using h

/-- Both marked laws have exactly the SAME (fair) unmarked next-key
marginal, shown by summing their actual marked source atoms. -/
theorem actual_unmarked_next_key_fair (twist : Bool) (y : Y) (k : Bool) :
    (∑ b : Bool, markedLaw twist y {(b, ((), k))}) =
      ENNReal.ofReal (1/2 : ℝ) := by
  simp_rw [markedLaw_actual_source_atom]
  cases twist <;> cases k <;>
    norm_num [Fintype.sum_bool, coin_true, coin_false]

theorem actual_unmarked_next_key_laws_equal (y : Y) (k : Bool) :
    (∑ b : Bool, markedLaw false y {(b, ((), k))}) =
      (∑ b : Bool, markedLaw true y {(b, ((), k))}) := by
  rw [actual_unmarked_next_key_fair, actual_unmarked_next_key_fair]

/-- Complete original action-marked diagonal event, in the ACTUAL original
one-step history law, separates the two legal strict anchors. -/
private theorem fair_halves_add_one :
    ENNReal.ofReal (1/2 : ℝ) + ENNReal.ofReal (1/2 : ℝ) = 1 := by
  rw [← ENNReal.ofReal_add
    (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (0 : ℝ) ≤ 1/2)]
  norm_num

theorem actual_marked_diagonal_separation (y : Y) :
    (∑ b : Bool, markedLaw false y {(b, ((), b))}) = 1 ∧
    (∑ b : Bool, markedLaw true y {(b, ((), b))}) = 0 := by
  constructor <;> simp_rw [markedLaw_actual_source_atom] <;>
    norm_num [Fintype.sum_bool, coin_true, coin_false, fair_halves_add_one]

/-- The assumptions of the strict MA2 no-separation theorem are not silently
inherited from equality of unmarked key marginals: these anchors have
different private-update kernels at the same original opponent key/action. -/
theorem update_mechanisms_differ :
    (strictAnchor false).update (sourceInput false false false) ≠
      (strictAnchor true).update (sourceInput false false false) := by
  intro h
  have he := congrArg (fun μ : Measure Bool => μ {true}) h
  simp [strictAnchor, markedUpdateFactor, fairActionFactor,
    sourceInput, anchorUpdateKey, Kernel.comap_apply,
    Kernel.deterministic_apply, Measure.dirac_apply'] at he

end PermanssonResearch.MultiAgent.M02ActualMarkedHistoryFixture
