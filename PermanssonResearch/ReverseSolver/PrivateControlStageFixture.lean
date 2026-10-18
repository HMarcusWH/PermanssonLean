import PermanssonResearch.ReverseSolver.PrivateControlStageOptimizer

/-! Matching/opposite regression with nature's information stated literally:
the private draw has value one half, every pure control has worst value zero,
and observing the realized control changes the game to value zero. -/

namespace PermanssonResearch.ReverseSolver.PrivateControlStage.MatchingFixture
open ActionTrace
noncomputable section

def payoff (θ c : Bool) : ℚ := if θ=c then 1 else 0

def halfRow : Row Bool where
  mass _ := 1/2
  nonneg _ := by norm_num
  total := by norm_num [Fintype.sum_bool]

theorem stagePayoff_eq_mass (p : Row Bool) (θ : Bool) : stagePayoff payoff p θ=p.mass θ := by
  cases θ <;> simp [stagePayoff,payoff,Row.expect,Fintype.sum_bool]

theorem all_real_mixtures_upper (p : Row Bool) : privateValue payoff p≤1/2 := by
  have hf := privateValue_le payoff p false
  have ht := privateValue_le payoff p true
  rw [stagePayoff_eq_mass] at hf ht
  have hs := p.total
  simp only [Fintype.sum_bool] at hs
  linarith

theorem half_value : privateValue payoff halfRow=1/2 := by
  change stagePayoff payoff halfRow (minimizingNature payoff halfRow)=1/2
  rw [stagePayoff_eq_mass]
  rfl

theorem half_actual_expectation (η : Row Bool) :
    (stageLaw halfRow η).expect (fun a => (payoff a.1 a.2 : ℝ))=1/2 := by
  rw [actual_stage_expectation]
  have he : stagePayoff payoff halfRow=(fun _ => (1/2:ℝ)) := by
    funext θ
    rw [stagePayoff_eq_mass]
    rfl
  rw [he,Row.expect_const]

theorem pure_private_value (c : Bool) : privateValue payoff (Row.pure c)=0 := by
  have hu := privateValue_le payoff (Row.pure c) (!c)
  rw [stagePayoff_eq_mass] at hu
  have hn : 0≤privateValue payoff (Row.pure c) := by
    change 0≤(Row.pure c).expect (fun a => (payoff (minimizingNature payoff (Row.pure c)) a : ℝ))
    have hh := (Row.pure c).expect_mono (fun a =>
      show (0:ℝ)≤(payoff (minimizingNature payoff (Row.pure c)) a : ℝ) by
        unfold payoff
        split_ifs <;> norm_num)
    simpa only [Row.expect_const] using hh
  have hz : (Row.pure c).mass (!c)=0 := by cases c <;> simp [Row.pure]
  exact le_antisymm (by simpa only [hz] using hu) hn

/-- In this different experiment nature sees the realized control, and
chooses its opposite. This is deliberately not the private-draw law. -/
def revealedControlLaw (p : Row Bool) : Row (Bool × Bool) := p.map (fun c => (!c,c))

theorem revealed_control_zero (p : Row Bool) :
    (revealedControlLaw p).expect (fun a => (payoff a.1 a.2 : ℝ))=0 := by
  rw [revealedControlLaw,Row.expect_map]
  have he : (fun c : Bool => (payoff (!c) c : ℝ))=(fun _ => 0) := by
    funext c
    cases c <;> simp [payoff]
  rw [he,Row.expect_const]

theorem returned_value_half (q : Option Bool → ℚ) (hq : solvePrivateStage payoff=some q) :
    q none=1/2 := by
  have hl := returned_dominates_all_real_mixtures payoff q hq halfRow
  rw [half_value] at hl
  have hu := all_real_mixtures_upper (solutionRow payoff q hq)
  rw [returned_value_attained] at hu
  have he : (q none : ℝ)=1/2 := le_antisymm hu hl
  apply Rat.cast_injective (α:=ℝ)
  norm_num
  exact he

theorem solver_value_half :
    (solvePrivateStage payoff).map (fun q => q none)=some (1/2) := by
  obtain ⟨q,hq⟩ := solvePrivateStage_returns payoff
  rw [hq,Option.map_some,returned_value_half q hq]

theorem timing_and_randomization_boundary :
    privateValue payoff halfRow=1/2 ∧
    (∀ c : Bool,privateValue payoff (Row.pure c)=0) ∧
    (revealedControlLaw halfRow).expect (fun a => (payoff a.1 a.2 : ℝ))=0 :=
  ⟨half_value,pure_private_value,revealed_control_zero halfRow⟩

def negativePayoff (_ _ : Bool) : ℚ := -7

theorem negative_private_value (p : Row Bool) : privateValue negativePayoff p=-7 := by
  simp [privateValue,stagePayoff,negativePayoff]

/-- The value coordinate can be negative. Its lower bound comes from the
payoff table rather than an unjustified nonnegativity constraint. -/
theorem negative_solver_value :
    (solvePrivateStage negativePayoff).map (fun q => q none)=some (-7) := by
  obtain ⟨q,hq⟩ := solvePrivateStage_returns negativePayoff
  have he := returned_value_attained negativePayoff q hq
  rw [negative_private_value] at he
  have hr : q none=-7 := by exact_mod_cast he.symm
  rw [hq,Option.map_some,hr]

end
end PermanssonResearch.ReverseSolver.PrivateControlStage.MatchingFixture
