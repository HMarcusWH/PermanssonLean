import PermanssonResearch.MultiAgent.AutonomousKey
import PermanssonResearch.Probability.StandardBorelKernelEquality

/-! Autonomous key rows derived from the actual conditional product mechanism
on general measurable spaces. No positive-atom argument is used. -/

namespace PermanssonResearch.MultiAgent.Autonomous

open MeasureTheory ProbabilityTheory Set PermanssonLean
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {S0 S1 S2 X A1 A2 : Type*}
variable [MeasurableSpace S0] [MeasurableSpace S1] [MeasurableSpace S2]
variable [MeasurableSpace X] [MeasurableSpace A1] [MeasurableSpace A2]

def strategicKey (s : GameState S0 S1 S2) : S0 × S2 := (s.1,s.2.2)

theorem measurable_strategicKey : Measurable (strategicKey (S0 := S0) (S1 := S1) (S2 := S2)) := by
  unfold strategicKey
  fun_prop

theorem map_product_update (μ0 : Measure S0) (μ1 : Measure S1) (μ2 : Measure S2)
    [IsProbabilityMeasure μ0] [IsProbabilityMeasure μ1] [IsProbabilityMeasure μ2] :
    (μ0.prod (μ1.prod μ2)).map strategicKey = μ0.prod μ2 := by
  change (μ0.prod (μ1.prod μ2)).map (Prod.map id Prod.snd) = _
  rw [← Measure.map_prod_map μ0 (μ1.prod μ2) measurable_id measurable_snd]
  simp

theorem Profile.update_key {G : TwoPlayerGenerator S0 S1 S2 X A1 A2}
    {a : PlayerTwoMechanism S0 S1 S2 X A1 A2} (d : Profile G a)
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2) (i : Input S0 S1 S2 X A1 A2) :
    (((G.openLoop r a).toGenerator.update i).map strategicKey) =
      (d.common (commonUpdateKey i)).prod (d.update (anchorUpdateKey i)) := by
  letI := G.common_isMarkov
  letI := r.update_isMarkov
  letI := a.update_isMarkov
  rw [TwoPlayerGenerator.toGenerator_update_apply]
  simp only [TwoPlayerGenerator.openLoop]
  rw [map_product_update, d.common_apply, d.update_apply]

def Profile.keyUpdate {G : TwoPlayerGenerator S0 S1 S2 X A1 A2}
    {a : PlayerTwoMechanism S0 S1 S2 X A1 A2} (d : Profile G a) :
    Kernel ((S0 × S2) × A2) (S0 × S2) :=
  (d.common.comap (fun i => i.1.1) (measurable_fst.comp measurable_fst)) ×ₖ d.update

def Profile.keyKernel {G : TwoPlayerGenerator S0 S1 S2 X A1 A2}
    {a : PlayerTwoMechanism S0 S1 S2 X A1 A2} (d : Profile G a) : Kernel (S0 × S2) (S0 × S2) :=
  (d.action ⊗ₖ d.keyUpdate).map Prod.snd

instance Profile.keyUpdate_isMarkov {G : TwoPlayerGenerator S0 S1 S2 X A1 A2}
    {a : PlayerTwoMechanism S0 S1 S2 X A1 A2} (d : Profile G a)
    [IsMarkovKernel d.common] [IsMarkovKernel d.update] : IsMarkovKernel d.keyUpdate := by
  unfold Profile.keyUpdate
  infer_instance

instance Profile.keyKernel_isMarkov {G : TwoPlayerGenerator S0 S1 S2 X A1 A2}
    {a : PlayerTwoMechanism S0 S1 S2 X A1 A2} (d : Profile G a)
    [IsMarkovKernel d.common] [IsMarkovKernel d.action] [IsMarkovKernel d.update] :
    IsMarkovKernel d.keyKernel := by
  unfold Profile.keyKernel
  exact Kernel.IsMarkovKernel.map _ measurable_snd

theorem Profile.keyKernel_apply {G : TwoPlayerGenerator S0 S1 S2 X A1 A2}
    {a : PlayerTwoMechanism S0 S1 S2 X A1 A2} (d : Profile G a)
    [IsMarkovKernel d.common] [IsMarkovKernel d.action] [IsMarkovKernel d.update]
    (q : S0 × S2) {E : Set (S0 × S2)} (hE : MeasurableSet E) :
    d.keyKernel q E = ∫⁻ b, (d.common q.1).prod (d.update (q,b)) E ∂d.action q := by
  unfold Profile.keyKernel
  rw [Kernel.map_apply' _ measurable_snd _ hE,
    Kernel.compProd_apply (hE.preimage measurable_snd)]
  apply lintegral_congr
  intro b
  simp only [Profile.keyUpdate, Kernel.prod_apply, Kernel.comap_apply]
  rfl

/-- The actual typed next-key law is independent of the treated mechanism and
physical world, even on nonatomic measurable spaces. -/
theorem Profile.actual_key_row {G : TwoPlayerGenerator S0 S1 S2 X A1 A2}
    {a : PlayerTwoMechanism S0 S1 S2 X A1 A2} (d : Profile G a)
    [IsMarkovKernel d.common] [IsMarkovKernel d.action] [IsMarkovKernel d.update]
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (y : State S0 S1 S2 X) :
    ((((G.openLoop r a).toModel P).inducedKernel y).map anchorKey) = d.keyKernel (anchorKey y) := by
  let M := (G.openLoop r a).toModel P
  letI := r.action_isMarkov
  letI := a.action_isMarkov
  letI := M.generator.action_isMarkov
  letI := M.generator.update_isMarkov
  letI := M.world_isMarkov
  ext E hE
  rw [Measure.map_apply measurable_anchorKey hE,
    StrategicWorldModel.inducedKernel_apply _ _ (hE.preimage measurable_anchorKey)]
  change (∫⁻ b : A1 × A2, ∫⁻ x : X,
    M.generator.update ((y,b),x) (strategicKey ⁻¹' E) ∂P (y,b)
      ∂M.generator.action y) = d.keyKernel (anchorKey y) E
  have hu (b : A1 × A2) (x : X) :
      M.generator.update ((y,b),x) (strategicKey ⁻¹' E) =
        (d.common y.1.1).prod (d.update (anchorKey y,b.2)) E := by
    have hh := congrArg (fun μ : Measure (S0 × S2) => μ E) (d.update_key r ((y,b),x))
    simpa only [M, TwoPlayerGenerator.toModel, Measure.map_apply measurable_strategicKey hE,
      commonUpdateKey, anchorUpdateKey] using hh
  simp_rw [hu]
  simp only [lintegral_const, measure_univ, mul_one]
  dsimp only [M, TwoPlayerGenerator.toModel]
  rw [TwoPlayerGenerator.toGenerator_action_apply]
  change (∫⁻ b : A1 × A2,
    (d.common y.1.1).prod (d.update (anchorKey y,b.2)) E
      ∂(r.action y).prod (a.action y)) = _
  rw [MeasureTheory.lintegral_prod]
  · simp_rw [lintegral_const, measure_univ, mul_one]
    rw [d.action_apply, d.keyKernel_apply (anchorKey y) hE]
    rfl
  · have hm : Measurable (fun b : A1 × A2 => d.keyUpdate (anchorKey y,b.2) E) :=
      (d.keyUpdate.measurable_coe hE).comp
      (measurable_const.prodMk measurable_snd)
    simpa only [Profile.keyUpdate, Kernel.prod_apply, Kernel.comap_apply, anchorKey] using hm.aemeasurable

end
end PermanssonResearch.MultiAgent.Autonomous
