import PermanssonResearch.MultiAgent.AutonomousInputMarginal

namespace PermanssonResearch.MultiAgent.Autonomous

open MeasureTheory ProbabilityTheory Set PermanssonLean
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {S0 S1 S2 X A1 A2 : Type*}
variable [MeasurableSpace S0] [MeasurableSpace S1] [MeasurableSpace S2]
variable [MeasurableSpace X] [MeasurableSpace A1] [MeasurableSpace A2]

theorem actual_row_from_actionWorld
    (M : StrategicWorldModel (GameState S0 S1 S2) X (A1 × A2))
    (y : State S0 S1 S2 X) {E : Set (State S0 S1 S2 X)} (hE : MeasurableSet E) :
    M.inducedKernel y E = ∫⁻ h : (A1 × A2) × X,
      M.generator.update ((y,h.1),h.2) {s | (s,h.2) ∈ E} ∂M.actionWorldKernel y := by
  letI := M.generator.update_isMarkov
  letI := M.actionWorldKernel_isMarkov
  letI := M.reassociatedUpdate_isMarkov
  have hm : Measurable (fun z : (((A1 × A2) × X) × GameState S0 S1 S2) =>
      (z.2,z.1.2)) := by fun_prop
  rw [StrategicWorldModel.inducedKernel, Kernel.map_apply' _ hm _ hE,
    StrategicWorldModel.oneStepHistoryKernel, Kernel.compProd_apply (hE.preimage hm)]
  rfl

/-- Actual action and actual action/world-input update agreement imply equality
of whole induced rows almost everywhere. The exceptional event is chosen
before evaluating any measurable output set. -/
theorem actual_rows_ae_of_primitive_agreement
    (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2)
    (a b : PlayerTwoMechanism S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (μ : Measure (State S0 S1 S2 X)) [SFinite μ]
    (hA : a.action =ᵐ[μ] b.action)
    (hU : ∀ᵐ z ∂(μ ⊗ₘ ((G.openLoop r a).toModel P).actionWorldKernel),
      a.update ((z.1,z.2.1),z.2.2) = b.update ((z.1,z.2.1),z.2.2)) :
    ((G.openLoop r a).toModel P).inducedKernel =ᵐ[μ]
      ((G.openLoop r b).toModel P).inducedKernel := by
  let M0 := (G.openLoop r a).toModel P
  let M1 := (G.openLoop r b).toModel P
  letI := M0.actionWorldKernel_isMarkov
  letI := M1.actionWorldKernel_isMarkov
  letI := M0.generator.action_isMarkov
  letI := M1.generator.action_isMarkov
  letI := M0.world_isMarkov
  letI := M1.world_isMarkov
  have hUi : ∀ᵐ y ∂μ, ∀ᵐ h ∂M0.actionWorldKernel y,
      a.update ((y,h.1),h.2) = b.update ((y,h.1),h.2) :=
    Measure.ae_ae_of_ae_compProd hU
  filter_upwards [hA,hUi] with y hay huy
  have hAlpha : M0.generator.action y = M1.generator.action y := by
    dsimp only [M0,M1,TwoPlayerGenerator.toModel]
    rw [TwoPlayerGenerator.toGenerator_action_apply,TwoPlayerGenerator.toGenerator_action_apply]
    simp only [TwoPlayerGenerator.openLoop,hay]
  have hAW : M0.actionWorldKernel y = M1.actionWorldKernel y := by
    rw [StrategicWorldModel.actionWorldKernel, Kernel.compProd_apply_eq_compProd_sectR,
      StrategicWorldModel.actionWorldKernel, Kernel.compProd_apply_eq_compProd_sectR]
    change M0.generator.action y ⊗ₘ Kernel.sectR P y =
      M1.generator.action y ⊗ₘ Kernel.sectR P y
    rw [hAlpha]
  ext E hE
  rw [actual_row_from_actionWorld M0 y hE, actual_row_from_actionWorld M1 y hE,← hAW]
  apply lintegral_congr_ae
  filter_upwards [huy] with h huh
  have hUpdate : M0.generator.update ((y,h.1),h.2) =
      M1.generator.update ((y,h.1),h.2) := by
    dsimp only [M0,M1,TwoPlayerGenerator.toModel]
    rw [TwoPlayerGenerator.toGenerator_update_apply,TwoPlayerGenerator.toGenerator_update_apply]
    simp only [TwoPlayerGenerator.openLoop,huh]
  rw [hUpdate]

end
end PermanssonResearch.MultiAgent.Autonomous
