import PermanssonResearch.MultiAgent.MeasurableNatClockTransport

/-! Every original coordinate is the real line. The anchor uses a genuine
nonperiodic natural schedule; full path projection holds for arbitrary real
initial probability laws. There are no finite-action/world instances. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace PermanssonResearch.MultiAgent.MeasurableNatPrivateClock.RealFixture
open PermanssonLean
noncomputable section

def player1 : PlayerOneMechanism ℝ ℝ ℝ ℝ ℝ ℝ where
  action := Kernel.const _ (Measure.dirac 0)
  update := Kernel.const _ (Measure.dirac 0)
  action_isMarkov := inferInstance
  update_isMarkov := inferInstance

def schedule (t : ℕ) : PlayerTwoMechanism ℝ ℝ ℝ ℝ ℝ ℝ where
  action := Kernel.const _ (Measure.dirac (t : ℝ))
  update := Kernel.const _ (Measure.dirac 0)
  action_isMarkov := inferInstance
  update_isMarkov := inferInstance

def baseline : TwoPlayerGenerator ℝ ℝ ℝ ℝ ℝ ℝ where
  player1 := player1
  player2 := schedule 0
  common := Kernel.const _ (Measure.dirac 0)
  common_isMarkov := inferInstance

def world : Kernel (WorldInput (GameState ℝ ℝ ℝ) ℝ (ℝ × ℝ)) ℝ :=
  Kernel.deterministic (fun i => i.2.2) (by fun_prop)
instance world_isMarkov : IsMarkovKernel world := by unfold world; infer_instance

theorem scheduled_actions_differ (t u : ℕ) (htu : t ≠ u)
    (y : OldState (S0 := ℝ) (S1 := ℝ) (S2 := ℝ) (X := ℝ)) :
    (schedule t).action y ≠ (schedule u).action y := by
  intro he
  have hh := congrArg (fun μ : Measure ℝ => μ {(t : ℝ)}) he
  have htu' : (t : ℝ) ≠ (u : ℝ) := by exact_mod_cast htu
  simp [schedule,htu',Ne.symm htu'] at hh

theorem strict_schedule (t : ℕ) : IsStrictlyNonReactive (schedule t) := by
  refine ⟨⟨Kernel.const _ (Measure.dirac (t : ℝ)),?_⟩,
    ⟨Kernel.const _ (Measure.dirac (0:ℝ)),?_⟩⟩ <;>
      apply Kernel.ext <;> intro y <;> rfl

theorem clocked_strict : IsStrictlyNonReactive (anchor schedule Nat.succ) :=
  inherited_strictness schedule Nat.succ strict_schedule

theorem clock_advances (i : UpdateInput (GameState ℝ ℝ (ℝ × ℕ)) ℝ (ℝ × ℝ)) :
    (anchor schedule Nat.succ).update i (Set.univ ×ˢ {phase i.1.1+1}) = 1 :=
  advancing_update schedule i

theorem stalled_clock_rejected (t : ℕ)
    (y : OldState (S0 := ℝ) (S1 := ℝ) (S2 := ℝ) (X := ℝ)) :
    (anchor schedule Nat.succ).update ((lift t y,(0,0)),0) (Set.univ ×ˢ {t}) = 0 := by
  rw [anchor_update,Measure.map_apply (by fun_prop)
    (MeasurableSet.univ.prod (measurableSet_singleton _))]
  simp [phase,lift,liftStrategic]

theorem full_actual_real_projection (t : ℕ)
    (μ : Measure (OldState (S0 := ℝ) (S1 := ℝ) (S2 := ℝ) (X := ℝ))) [IsProbabilityMeasure μ] :
    (((generator baseline schedule Nat.succ).toModel (physical world)).pathLaw
      (μ.map (lift t))).map (fun w n => drop (w n)) =
        Chronological.law (scheduledKernel baseline world schedule Nat.succ t) μ :=
  natural_projection baseline world schedule t μ

end
end PermanssonResearch.MultiAgent.MeasurableNatPrivateClock.RealFixture
