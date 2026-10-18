import PermanssonResearch.MultiAgent.ProductGame
import Mathlib.Data.Fintype.Pi

/-! F-CORR: sample a joint mediator at the action-generation stage and read its
coordinates. The mediator distribution may depend on the current state. This
construction neither asserts exogeneity nor grants players new observations. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultiAgent

variable {I : Type*} [Fintype I] [DecidableEq I]
  {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- Conditional on the mediator draw, every coordinate is deterministic. -/
noncomputable def mediatorProduct (a z : ∀ i, A i) : ℝ := by
  classical
  exact ∏ i, if a i = z i then 1 else 0

theorem mediatorProduct_eq_indicator (a z : ∀ i, A i) :
    mediatorProduct a z = if a = z then 1 else 0 := by
  classical
  by_cases h : a = z
  · subst z; simp [mediatorProduct]
  · have hex : ∃ i, a i ≠ z i := by
      by_contra hn
      apply h
      funext i
      exact not_not.mp (not_exists.mp hn i)
    obtain ⟨i, hi⟩ := hex
    simp only [mediatorProduct, if_neg h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

/-- Exact mixture of conditional product laws for any finite joint weights.
Probability normalization is inherited from the supplied joint law. -/
theorem mediator_mixture_eq (γ : (∀ i, A i) → ℝ) (a : ∀ i, A i) :
    (∑ z, γ z * mediatorProduct a z) = γ a := by
  classical
  simp_rw [mediatorProduct_eq_indicator]
  simp [eq_comm]

/-- The complete mediator coordinate readout is the identity on the joint
action space, so its pushforward is exactly the declared joint law. -/
noncomputable def mediatedAction {Y J : Type*} [MeasurableSpace Y] [MeasurableSpace J]
    (γ : Kernel Y J) : Kernel Y J := γ.map id

@[simp] theorem mediatedAction_eq {Y J : Type*} [MeasurableSpace Y] [MeasurableSpace J]
    (γ : Kernel Y J) : mediatedAction γ = γ := by
  simp [mediatedAction]

/-- An arbitrary joint mediator is consumed by the original general strategic
generator. Its update and literal physical world are retained. -/
noncomputable def withMediatedActions
    {S X J : Type*} [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace J]
    (M : PermanssonLean.StrategicWorldModel S X J)
    (γ : Kernel (PermanssonLean.JointState S X) J) [IsMarkovKernel γ] :
    PermanssonLean.StrategicWorldModel S X J where
  generator :=
    { action := mediatedAction γ
      update := M.generator.update
      action_isMarkov := by rw [mediatedAction_eq]; infer_instance
      update_isMarkov := M.generator.update_isMarkov }
  world := M.world
  world_isMarkov := M.world_isMarkov

@[simp] theorem withMediatedActions_action
    {S X J : Type*} [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace J]
    (M : PermanssonLean.StrategicWorldModel S X J)
    (γ : Kernel (PermanssonLean.JointState S X) J) [IsMarkovKernel γ] :
    (withMediatedActions M γ).generator.action = γ := mediatedAction_eq γ

@[simp] theorem withMediatedActions_world
    {S X J : Type*} [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace J]
    (M : PermanssonLean.StrategicWorldModel S X J)
    (γ : Kernel (PermanssonLean.JointState S X) J) [IsMarkovKernel γ] :
    (withMediatedActions M γ).world = M.world := rfl

end PermanssonResearch.MultiAgent
