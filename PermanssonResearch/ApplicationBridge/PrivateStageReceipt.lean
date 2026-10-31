import PermanssonResearch.ReverseSolver.PrivateControlStageOptimizer
import Mathlib.Tactic

/-!
# ApplicationBridge — private-stage robust certificate receipts

In Research's private control stage nature chooses a finite parameter after
seeing the controller's mixed strategy but before the private control draw
(`stageLaw p η`). A receipt supplies a rational controller mixture `p`, a
rational nature mixture `q`, the claimed value `v` and the best pure-control
value `r`.

`SaddleChecks` decides that `p` and `q` are rational simplex vectors, that `p`
earns at least `v` against every nature parameter, and that `q` holds every
pure control to at most `v`; `PureChecks` decides that every pure control is
held to `r` by some parameter and some pure control guarantees `r`. From the
kernel-evaluated check:

* `checked_isGreatest`: `v` is the greatest `privateValue` over all real mixed
  controllers, attained by `p`;
* `checked_private_saddle`: on the actual stage law, `p` guarantees `v`
  against every real nature row and `q` holds every real controller to `v`;
* `checked_solver_value`: Research's executable rational vertex solver
  `solvePrivateStage` returns exactly the value `v` (the solver is not run);
* `checked_pure_controls` and `checked_revealed_control`: pure controls and
  the different revealed-control experiment, where nature observes the
  realized control, are worth exactly `r`.

No minimax theorem or LP duality hypothesis is used: both bounds come from the
literal certificate. Multi-stage private games are not claimed.
-/

namespace PermanssonResearch.ApplicationBridge.PrivateStageReceipt

open PermanssonResearch.ActionTrace
open PermanssonResearch.ReverseSolver.PrivateControlStage

set_option autoImplicit false

variable {C Θ : Type*} [Fintype C] [LinearOrder C] [Nonempty C]
  [Fintype Θ] [LinearOrder Θ] [Nonempty Θ]

/-- Rational saddle certificate for the private stage. -/
def SaddleChecks (Q : Θ → C → ℚ) (p : C → ℚ) (q : Θ → ℚ) (v : ℚ) : Prop :=
  (∀ c, 0 ≤ p c) ∧ (∑ c, p c = 1) ∧ (∀ θ, 0 ≤ q θ) ∧ (∑ θ, q θ = 1) ∧
  (∀ θ, v ≤ ∑ c, p c * Q θ c) ∧ ∀ c, ∑ θ, q θ * Q θ c ≤ v

/-- Pure-control certificate: every pure control is held to `r` by some
    parameter, and some pure control guarantees `r` against all of them. -/
def PureChecks (Q : Θ → C → ℚ) (r : ℚ) : Prop :=
  (∀ c, ∃ θ, Q θ c ≤ r) ∧ ∃ c, ∀ θ, r ≤ Q θ c

instance (Q : Θ → C → ℚ) (p : C → ℚ) (q : Θ → ℚ) (v : ℚ) :
    Decidable (SaddleChecks Q p q v) := by
  unfold SaddleChecks
  infer_instance

instance (Q : Θ → C → ℚ) (r : ℚ) : Decidable (PureChecks Q r) := by
  unfold PureChecks
  infer_instance

def checkPrivateStage (Q : Θ → C → ℚ) (p : C → ℚ) (q : Θ → ℚ) (v r : ℚ) : Bool :=
  decide (SaddleChecks Q p q v ∧ PureChecks Q r)

omit [LinearOrder C] [Nonempty C] [LinearOrder Θ] [Nonempty Θ] in
theorem checkPrivateStage_sound (Q : Θ → C → ℚ) (p : C → ℚ) (q : Θ → ℚ) (v r : ℚ)
    (h : checkPrivateStage Q p q v r = true) : SaddleChecks Q p q v ∧ PureChecks Q r := by
  unfold checkPrivateStage at h
  exact of_decide_eq_true h

/-- The real probability row of a checked rational simplex vector. -/
noncomputable def ratRow {α : Type*} [Fintype α] (p : α → ℚ) (h0 : ∀ a, 0 ≤ p a)
    (h1 : ∑ a, p a = 1) : Row α where
  mass a := (p a : ℝ)
  nonneg a := by exact_mod_cast h0 a
  total := by exact_mod_cast h1

omit [LinearOrder C] [Nonempty C] [Fintype Θ] [LinearOrder Θ] [Nonempty Θ] in
theorem stagePayoff_ratRow (Q : Θ → C → ℚ) (p : C → ℚ) (h0 : ∀ c, 0 ≤ p c)
    (h1 : ∑ c, p c = 1) (θ : Θ) :
    stagePayoff Q (ratRow p h0 h1) θ = ((∑ c, p c * Q θ c : ℚ) : ℝ) := by
  simp [stagePayoff, Row.expect, ratRow]

omit [Nonempty C] [Fintype Θ] [LinearOrder Θ] [Nonempty Θ] in
theorem stagePayoff_pure (Q : Θ → C → ℚ) (c : C) (θ : Θ) :
    stagePayoff Q (Row.pure c) θ = (Q θ c : ℝ) := by
  simp [stagePayoff]

section Saddle

variable (Q : Θ → C → ℚ) (p : C → ℚ) (q : Θ → ℚ) (v : ℚ) (h : SaddleChecks Q p q v)
include h

/-- The certified controller row. -/
noncomputable def controllerRow : Row C := ratRow p h.1 h.2.1

/-- The certified nature row. -/
noncomputable def natureRow : Row Θ := ratRow q h.2.2.1 h.2.2.2.1

omit [LinearOrder C] [Nonempty C] [LinearOrder Θ] in
theorem controller_value_ge : (v : ℝ) ≤ privateValue Q (controllerRow Q p q v h) := by
  unfold privateValue controllerRow
  rw [stagePayoff_ratRow]
  exact_mod_cast h.2.2.2.2.1 _

theorem nature_holds (p' : Row C) :
    (stageLaw p' (natureRow Q p q v h)).expect (fun a => (Q a.1 a.2 : ℝ)) ≤ v := by
  rw [actual_stage_expectation]
  have hc : ∀ c, (∑ θ, (q θ : ℝ) * (Q θ c : ℝ)) ≤ (v : ℝ) := fun c => by
    exact_mod_cast h.2.2.2.2.2 c
  calc (natureRow Q p q v h).expect (stagePayoff Q p')
      = ∑ c, p'.mass c * ∑ θ, (q θ : ℝ) * (Q θ c : ℝ) := by
        simp only [Row.expect, stagePayoff, natureRow, ratRow, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun θ _ => by ring
    _ ≤ ∑ c, p'.mass c * (v : ℝ) :=
        Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hc c) (p'.nonneg c)
    _ = v := by rw [← Finset.sum_mul, p'.total, one_mul]

theorem privateValue_le_checked (p' : Row C) : privateValue Q p' ≤ (v : ℝ) :=
  (actual_nature_lower_bound Q p' _).trans (nature_holds Q p q v h p')

/-- `v` is the greatest private-stage value over every real mixed
    controller, attained by the certified rational controller. -/
theorem checked_isGreatest :
    privateValue Q (controllerRow Q p q v h) = (v : ℝ) ∧
    IsGreatest (Set.range (privateValue Q)) (v : ℝ) := by
  have he := le_antisymm (privateValue_le_checked Q p q v h _) (controller_value_ge Q p q v h)
  exact ⟨he, ⟨⟨_, he⟩, by rintro _ ⟨p', rfl⟩; exact privateValue_le_checked Q p q v h p'⟩⟩

/-- Actual stage-law saddle: the certified controller guarantees `v`
    against every real nature row, and the certified nature row holds every
    real controller to `v`. -/
theorem checked_private_saddle :
    (∀ η : Row Θ, (v : ℝ) ≤
      (stageLaw (controllerRow Q p q v h) η).expect (fun a => (Q a.1 a.2 : ℝ))) ∧
    (∀ p' : Row C,
      (stageLaw p' (natureRow Q p q v h)).expect (fun a => (Q a.1 a.2 : ℝ)) ≤ v) :=
  ⟨fun η => (controller_value_ge Q p q v h).trans (actual_nature_lower_bound Q _ η),
   nature_holds Q p q v h⟩

/-- Research's executable private-stage solver returns exactly the certified
    value; the solver itself is not evaluated. -/
theorem checked_solver_value : (solvePrivateStage Q).map (fun x => x none) = some v := by
  obtain ⟨x, hx⟩ := solvePrivateStage_returns Q
  have he : (x none : ℝ) = v :=
    (returned_isGreatest Q x hx).unique (checked_isGreatest Q p q v h).2
  rw [hx, Option.map_some]
  exact congrArg some (by exact_mod_cast he)

end Saddle

section Pure

variable (Q : Θ → C → ℚ) (r : ℚ) (h : PureChecks Q r)
include h

/-- Pure controls under private timing are worth exactly `r`. -/
theorem checked_pure_controls :
    (∀ c, privateValue Q (Row.pure c) ≤ (r : ℝ)) ∧ ∃ c, privateValue Q (Row.pure c) = (r : ℝ) := by
  have hle : ∀ c, privateValue Q (Row.pure c) ≤ (r : ℝ) := fun c => by
    obtain ⟨θ, hθ⟩ := h.1 c
    have hv := privateValue_le Q (Row.pure c) θ
    rw [stagePayoff_pure] at hv
    exact hv.trans (by exact_mod_cast hθ)
  obtain ⟨c, hc⟩ := h.2
  refine ⟨hle, c, le_antisymm (hle c) ?_⟩
  unfold privateValue
  rw [stagePayoff_pure]
  exact_mod_cast hc _

omit [Nonempty C] [LinearOrder Θ] [Nonempty Θ] in
/-- The revealed-control experiment, where nature observes the realized
    control: some response holds every real controller to `r`, and some pure
    control earns `r` against every response. -/
theorem checked_revealed_control :
    (∃ f : C → Θ, ∀ p' : Row C,
      (p'.map (fun c => (f c, c))).expect (fun a => (Q a.1 a.2 : ℝ)) ≤ r) ∧
    ∃ c, ∀ f : C → Θ,
      (r : ℝ) ≤ ((Row.pure c).map (fun c => (f c, c))).expect (fun a => (Q a.1 a.2 : ℝ)) := by
  refine ⟨⟨fun c => Classical.choose (h.1 c), fun p' => ?_⟩, ?_⟩
  · rw [Row.expect_map]
    calc p'.expect (fun c => (Q (Classical.choose (h.1 c)) c : ℝ))
        ≤ p'.expect (fun _ => (r : ℝ)) :=
          p'.expect_mono fun c => by exact_mod_cast Classical.choose_spec (h.1 c)
      _ = r := Row.expect_const _ _
  · obtain ⟨c, hc⟩ := h.2
    refine ⟨c, fun f => ?_⟩
    rw [Row.expect_map, Row.expect_pure]
    exact_mod_cast hc (f c)

end Pure

end PermanssonResearch.ApplicationBridge.PrivateStageReceipt
