import PermanssonResearch.StrategicWorld.ActionTrace

/-! Executed information-class countermodels for the original behavioral
policy. A rule at a fixed observed history cannot copy an unobserved draw. -/

namespace PermanssonResearch.ActionTrace.InformationBoundary

noncomputable def fair : Row Bool where
  mass := fun _ => 1/2
  nonneg := by intro b; norm_num
  total := by norm_num [Fintype.sum_bool]

theorem independent_fair_matching (p : Row Bool) :
    p.expect (fun a => fair.expect (fun b => if a = b then 1 else 0)) = (1/2 : ℝ) := by
  have hf (a : Bool) : fair.expect (fun b => if a = b then 1 else 0) = (1/2 : ℝ) := by
    cases a <;> norm_num [Row.expect, fair, Fintype.sum_bool]
  simp_rw [hf]
  exact p.expect_const _

theorem peeked_fair_matching :
    fair.expect (fun b => if b = b then (1 : ℝ) else 0) = 1 := by simp

/-- The actual original alternating step draws the opponent independently.
Its matching probability is exactly one half for every admitted policy. -/
theorem actual_step_fair_matching {Y : Type} [Fintype Y]
    (G : Game Y Bool) (σ : BehavioralPolicy Y Bool) (n : ℕ)
    (h : History Y (Bool × Bool) n) (hf : G.opponent (last n h) = fair) :
    (step G σ n h).expect (fun z => if z.1.1 = z.1.2 then 1 else 0) = (1/2 : ℝ) := by
  simp only [step, Row.expect_bind, Row.expect_map, Row.expect_const, hf]
  change (σ n h).expect (fun a => fair.expect (fun b =>
    (G.physical (last n h) a b).expect (fun _ => if a = b then (1 : ℝ) else 0))) = _
  simp_rw [Row.expect_const]
  exact independent_fair_matching _

/-- A current opponent draw or a future Boolean draw is not recoverable from
the same fixed history, even by a randomized rule in the original class. -/
theorem no_unobserved_draw_copy {Y : Type} [Fintype Y] (n : ℕ)
    (h : History Y (Bool × Bool) n) :
    ¬ ∃ σ : BehavioralPolicy Y Bool, ∀ b : Bool, σ n h = Row.pure b := by
  rintro ⟨σ, hσ⟩
  have he := (hσ false).symm.trans (hσ true)
  have hm := congrArg (fun p : Row Bool => p.mass false) he
  norm_num [Row.pure] at hm

theorem observed_history_cannot_copy_next_state {Y : Type} [Fintype Y] (n : ℕ)
    (h : History Y (Bool × Bool) n) :
    ¬ ∃ σ : BehavioralPolicy Y Bool, ∀ nextState : Bool,
      σ n h = Row.pure nextState := no_unobserved_draw_copy n h

end PermanssonResearch.ActionTrace.InformationBoundary
