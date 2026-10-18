import PermanssonResearch.MultiAgent.AutonomousMeasurableKey
import Mathlib.Probability.Kernel.Composition.Lemmas

namespace PermanssonResearch.MultiAgent.Autonomous

open MeasureTheory ProbabilityTheory Set PermanssonLean
open scoped ENNReal ProbabilityTheory

noncomputable section

theorem map_compProd_key {Y Q A : Type*}
    [MeasurableSpace Y] [MeasurableSpace Q] [MeasurableSpace A]
    (μ : Measure Y) [SFinite μ] (q : Y → Q) (hq : Measurable q)
    (L : Kernel Q A) [IsMarkovKernel L] :
    (μ ⊗ₘ L.comap q hq).map (Prod.map q id) = μ.map q ⊗ₘ L := by
  ext E hE
  rw [Measure.map_apply (hq.prodMap measurable_id) hE,
    Measure.compProd_apply (hE.preimage (hq.prodMap measurable_id)),
    Measure.compProd_apply hE,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hE) hq]
  simp only [Kernel.comap_apply]
  rfl

variable {S0 S1 S2 X A1 A2 : Type*}
variable [MeasurableSpace S0] [MeasurableSpace S1] [MeasurableSpace S2]
variable [MeasurableSpace X] [MeasurableSpace A1] [MeasurableSpace A2]

def inputMark (z : State S0 S1 S2 X × ((A1 × A2) × X)) : (S0 × S2) × A2 :=
  (anchorKey z.1,z.2.1.2)

theorem measurable_inputMark :
    Measurable (inputMark (S0 := S0) (S1 := S1) (S2 := S2)
      (X := X) (A1 := A1) (A2 := A2)) := by
  unfold inputMark anchorKey
  fun_prop

theorem Profile.actual_actionWorld_mark {G : TwoPlayerGenerator S0 S1 S2 X A1 A2}
    {a : PlayerTwoMechanism S0 S1 S2 X A1 A2} (d : Profile G a)
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (y : State S0 S1 S2 X) :
    ((((G.openLoop r a).toModel P).actionWorldKernel y).map
      (fun h : (A1 × A2) × X => h.1.2)) = d.action (anchorKey y) := by
  let M := (G.openLoop r a).toModel P
  letI := M.generator.action_isMarkov
  letI := M.world_isMarkov
  letI := r.action_isMarkov
  letI := a.action_isMarkov
  have hf : (M.actionWorldKernel y).map Prod.fst = M.generator.action y := by
    rw [← Kernel.fst_apply]
    simp only [StrategicWorldModel.actionWorldKernel, Kernel.fst_compProd]
  change (M.actionWorldKernel y).map (Prod.snd ∘ Prod.fst) = _
  rw [← Measure.map_map measurable_snd measurable_fst, hf]
  dsimp only [M, TwoPlayerGenerator.toModel]
  rw [TwoPlayerGenerator.toGenerator_action_apply]
  simp only [TwoPlayerGenerator.openLoop, Measure.map_snd_prod, measure_univ, one_smul]
  exact d.action_apply y

/-- The actual old-key/opponent-action input marginal. This retains the
realized opponent action and does not infer it from an unmarked next-key law. -/
theorem Profile.actual_input_marginal {G : TwoPlayerGenerator S0 S1 S2 X A1 A2}
    {a : PlayerTwoMechanism S0 S1 S2 X A1 A2} (d : Profile G a)
    [IsMarkovKernel d.action]
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (μ : Measure (State S0 S1 S2 X)) [SFinite μ] :
    (μ ⊗ₘ ((G.openLoop r a).toModel P).actionWorldKernel).map inputMark =
      μ.map anchorKey ⊗ₘ d.action := by
  let M := (G.openLoop r a).toModel P
  let f : ((A1 × A2) × X) → A2 := fun h => h.1.2
  have hf : Measurable f := by fun_prop
  letI := M.actionWorldKernel_isMarkov
  have hK : M.actionWorldKernel.map f = d.action.comap anchorKey measurable_anchorKey := by
    ext y E hE
    rw [Kernel.map_apply _ hf, Kernel.comap_apply]
    exact congrArg (fun ν : Measure A2 => ν E) (d.actual_actionWorld_mark r P y)
  calc
    (μ ⊗ₘ M.actionWorldKernel).map inputMark =
        ((μ ⊗ₘ M.actionWorldKernel).map (Prod.map id f)).map
          (Prod.map anchorKey id) := by
      rw [Measure.map_map (measurable_anchorKey.prodMap measurable_id)
        (measurable_id.prodMap hf)]
      rfl
    _ = (μ ⊗ₘ M.actionWorldKernel.map f).map (Prod.map anchorKey id) := by
      rw [Measure.compProd_map hf]
    _ = (μ ⊗ₘ d.action.comap anchorKey measurable_anchorKey).map (Prod.map anchorKey id) := by
      rw [hK]
    _ = μ.map anchorKey ⊗ₘ d.action :=
      map_compProd_key μ anchorKey measurable_anchorKey d.action

end
end PermanssonResearch.MultiAgent.Autonomous
