import PermanssonResearch.MultiAgent.NatPrivateClockTransport
import Mathlib.Probability.Distributions.Bernoulli

open MeasureTheory ProbabilityTheory Set PermanssonLean
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultiAgent.NatClockTests
set_option autoImplicit false
attribute [local instance] StrategicWorldModel.inducedKernel_isMarkov

noncomputable def one : PlayerOneMechanism Unit Unit Unit Unit Unit Bool where
  action := Kernel.const _ (Measure.dirac ())
  update := Kernel.const _ (Measure.dirac ())
  action_isMarkov := inferInstance
  update_isMarkov := inferInstance

noncomputable def rate (t : ℕ) : unitInterval :=
  ⟨1/((t : ℝ)+2), by
    constructor
    · positivity
    · apply (div_le_one (by positivity : 0 < (t : ℝ)+2)).mpr
      have ht : (0 : ℝ) ≤ t := by positivity
      linarith⟩

noncomputable def schedule (t : ℕ) : PlayerTwoMechanism Unit Unit Unit Unit Unit Bool where
  action := Kernel.const _ (bernoulliMeasure true false (rate t))
  update := Kernel.const _ (Measure.dirac ())
  action_isMarkov := inferInstance
  update_isMarkov := inferInstance

noncomputable def baseline : TwoPlayerGenerator Unit Unit Unit Unit Unit Bool where
  player1 := one
  player2 := schedule 0
  common := Kernel.const _ (Measure.dirac ())
  common_isMarkov := inferInstance

noncomputable def physical :
    Kernel (WorldInput (GameState Unit Unit Unit) Unit (Unit × Bool)) Unit :=
  Kernel.const _ (Measure.dirac ())

instance : IsMarkovKernel physical := by unfold physical; infer_instance

def start : JointState (GameState Unit Unit Unit) Unit := (((),((),())),())

theorem rate_injective : Function.Injective (fun n : ℕ => (rate n : ℝ)) := by
  intro m n h
  have hi := congrArg (fun x : ℝ => x⁻¹) h
  simp only [rate, one_div, inv_inv] at hi
  exact_mod_cast (show (m : ℝ) = n by linarith)

theorem action_rate (t : ℕ) : ((schedule t).action start).real {true} = rate t := by
  simp [schedule, Kernel.const_apply, bernoulliMeasure_real_apply]

/-- Every time has a different law, so this schedule cannot be periodic. -/
theorem schedule_nonperiodic :
    ¬ ∃ p : ℕ, 0 < p ∧ ∀ n, (schedule (n+p)).action start = (schedule n).action start := by
  rintro ⟨p,hp,h⟩
  have hr := congrArg (fun μ : Measure Bool => μ.real {true}) (h 0)
  rw [action_rate, action_rate] at hr
  have : p = 0 := rate_injective (by simpa using hr)
  omega

theorem schedule_strict (t : ℕ) : IsStrictlyNonReactive (schedule t) := by
  refine ⟨⟨Kernel.const _ (bernoulliMeasure true false (rate t)), ?_⟩,
    ⟨Kernel.const _ (Measure.dirac ()), ?_⟩⟩ <;> apply Kernel.ext <;> intro i <;> rfl

theorem baseline_exogenous : IsExogenousCommon baseline := by
  refine ⟨Kernel.const _ (Measure.dirac ()), ?_⟩
  apply Kernel.ext
  intro i
  rfl

example : IsStrictlyNonReactive (NatPrivateClock.anchor schedule Nat.succ) :=
  NatPrivateClock.inherited_strictness schedule Nat.succ schedule_strict

example : IsExogenousCommon (NatPrivateClock.generator baseline schedule Nat.succ) :=
  NatPrivateClock.inherited_exogeneity baseline schedule Nat.succ baseline_exogenous

example :
    ((NatPrivateClock.generator baseline schedule Nat.succ).toModel
      (NatPrivateClock.physical physical)).inducedKernel (NatPrivateClock.lift 0 start)
        {NatPrivateClock.lift 1 start} = 1 ∧
    ((NatPrivateClock.generator baseline schedule Nat.succ).toModel
      (NatPrivateClock.physical physical)).inducedKernel (NatPrivateClock.lift 0 start)
        {NatPrivateClock.lift 0 start} = 0 := by
  constructor
  · rw [NatPrivateClock.actual_atom]
    simp only [Nat.succ_eq_add_one, zero_add, ite_true]
    have hi : IsProbabilityMeasure
        (((baseline.openLoop baseline.player1 (schedule 0)).toModel physical).inducedKernel start) := by
      letI := StrategicWorldModel.inducedKernel_isMarkov
        ((baseline.openLoop baseline.player1 (schedule 0)).toModel physical)
      infer_instance
    have hu : ({start} : Set (JointState (GameState Unit Unit Unit) Unit)) = Set.univ := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    rw [hu, measure_univ]
  · rw [NatPrivateClock.actual_atom]
    simp

example :
    (((NatPrivateClock.generator baseline schedule Nat.succ).toModel
      (NatPrivateClock.physical physical)).pathLaw
        ((Measure.dirac start).map (NatPrivateClock.lift 0))).map
      (fun w n => NatPrivateClock.drop (w n)) =
        Chronological.law (NatPrivateClock.scheduledKernel baseline physical schedule Nat.succ 0)
          (Measure.dirac start) :=
  NatPrivateClock.natural_projection baseline physical schedule 0 (Measure.dirac start)

def zeroClock : JointState (GameState Unit Unit (Unit × ℕ)) Unit :=
  (((),((),((),0))),())

noncomputable def treatedClock : PlayerTwoMechanism Unit Unit (Unit × ℕ) Unit Bool Bool where
  action := Kernel.const _ (Measure.dirac false)
  update := Kernel.deterministic
    (fun i => ((), if i.1.2.1 then NatPrivateClock.phase i.1.1 + 1
      else NatPrivateClock.phase i.1.1)) (measurable_of_countable _)
  action_isMarkov := inferInstance
  update_isMarkov := inferInstance

/-- Reading the treated action in the clock update violates the actual
original strict anchor predicate, even though the clock is private. -/
theorem treated_clock_not_strict : ¬ IsStrictlyNonReactive treatedClock := by
  intro h
  have he := h.update_eq (u := ((zeroClock,(false,false)),()))
    (u' := ((zeroClock,(true,false)),())) rfl
  have hm := congrArg (fun μ : Measure (Unit × ℕ) => μ {((),0)}) he
  simp [treatedClock, Kernel.deterministic_apply, Measure.dirac_apply,
    zeroClock, NatPrivateClock.phase] at hm

end PermanssonResearch.MultiAgent.NatClockTests
