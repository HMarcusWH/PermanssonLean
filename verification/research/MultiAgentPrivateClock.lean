import PermanssonResearch.MultiAgent.PrivateClockTransport

open MeasureTheory ProbabilityTheory Set PermanssonLean
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultiAgent.PrivateClockTests

noncomputable def one : PlayerOneMechanism Unit Unit Unit Unit Unit Bool where
  action := Kernel.const _ (Measure.dirac ())
  update := Kernel.const _ (Measure.dirac ())
  action_isMarkov := inferInstance
  update_isMarkov := inferInstance

noncomputable def periodicAnchor (t : Bool) : PlayerTwoMechanism Unit Unit Unit Unit Unit Bool where
  action := Kernel.const _ (Measure.dirac t)
  update := Kernel.const _ (Measure.dirac ())
  action_isMarkov := inferInstance
  update_isMarkov := inferInstance

noncomputable def baseline : TwoPlayerGenerator Unit Unit Unit Unit Unit Bool where
  player1 := one
  player2 := periodicAnchor false
  common := Kernel.const _ (Measure.dirac ())
  common_isMarkov := inferInstance

noncomputable def physical :
    Kernel (WorldInput (GameState Unit Unit Unit) Unit (Unit × Bool)) Unit :=
  Kernel.const _ (Measure.dirac ())

instance : IsMarkovKernel physical := by unfold physical; infer_instance

def start : JointState (GameState Unit Unit Unit) Unit := (((),((),())),())

/-- Actual typed alpha/P/U flips the private phase. A supposedly frozen clock
would fail the first atom and satisfy the second, opposite to these checks. -/
example :
    ((PrivateClock.generator baseline periodicAnchor Bool.not).toModel
      (PrivateClock.physical physical)).inducedKernel (PrivateClock.lift false start)
        {PrivateClock.lift true start} = 1 ∧
    ((PrivateClock.generator baseline periodicAnchor Bool.not).toModel
      (PrivateClock.physical physical)).inducedKernel (PrivateClock.lift false start)
        {PrivateClock.lift false start} = 0 := by
  constructor
  · rw [PrivateClock.actual_atom]
    simp only [Bool.not_false,ite_true]
    rw [Autonomous.product_transition_atom]
    simp [baseline,one,periodicAnchor,physical,TwoPlayerGenerator.openLoop,
      Kernel.const_apply,Measure.dirac_apply,start]
  · rw [PrivateClock.actual_atom]
    simp

example : Bool.not (Bool.not false) = false := rfl

end PermanssonResearch.MultiAgent.PrivateClockTests
