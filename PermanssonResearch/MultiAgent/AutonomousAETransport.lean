import PermanssonResearch.MultiAgent.AutonomousMarginalLaw

namespace PermanssonResearch.MultiAgent.Autonomous

open MeasureTheory ProbabilityTheory Set PermanssonLean
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {S0 S1 S2 X A1 A2 : Type*}
variable [MeasurableSpace S0] [MeasurableSpace S1] [MeasurableSpace S2]
variable [MeasurableSpace X] [MeasurableSpace A1] [MeasurableSpace A2]

attribute [local instance] StrategicWorldModel.inducedKernel_isMarkov

theorem actual_actionWorld_rows_ae
    (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2)
    (a b : PlayerTwoMechanism S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (μ : Measure (State S0 S1 S2 X))
    (hA : a.action =ᵐ[μ] b.action) :
    ((G.openLoop r a).toModel P).actionWorldKernel =ᵐ[μ]
      ((G.openLoop r b).toModel P).actionWorldKernel := by
  let M0 := (G.openLoop r a).toModel P
  let M1 := (G.openLoop r b).toModel P
  letI := M0.generator.action_isMarkov
  letI := M1.generator.action_isMarkov
  letI := M0.world_isMarkov
  letI := M1.world_isMarkov
  filter_upwards [hA] with y hay
  have hAlpha : M0.generator.action y = M1.generator.action y := by
    dsimp only [M0,M1,TwoPlayerGenerator.toModel]
    rw [TwoPlayerGenerator.toGenerator_action_apply,TwoPlayerGenerator.toGenerator_action_apply]
    simp only [TwoPlayerGenerator.openLoop,hay]
  rw [StrategicWorldModel.actionWorldKernel, Kernel.compProd_apply_eq_compProd_sectR,
    StrategicWorldModel.actionWorldKernel, Kernel.compProd_apply_eq_compProd_sectR]
  change M0.generator.action y ⊗ₘ Kernel.sectR P y =
    M1.generator.action y ⊗ₘ Kernel.sectR P y
  rw [hAlpha]

variable {G : TwoPlayerGenerator S0 S1 S2 X A1 A2}
variable {a b : PlayerTwoMechanism S0 S1 S2 X A1 A2}

theorem Profile.actual_key_marginal (d : Profile G a)
    [IsMarkovKernel d.common] [IsMarkovKernel d.action] [IsMarkovKernel d.update]
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (μ : Measure (State S0 S1 S2 X)) (n : ℕ) :
    (stateLaw ((G.openLoop r a).toModel P).inducedKernel μ n).map anchorKey =
      stateLaw d.keyKernel (μ.map anchorKey) n := by
  apply projected_stateLaw_eq _ _ _ anchorKey measurable_anchorKey
  intro t
  exact Filter.Eventually.of_forall (d.actual_key_row r P)

theorem Profile.baseline_key_marginal (d : Profile G a)
    [IsMarkovKernel d.common] [IsMarkovKernel d.action] [IsMarkovKernel d.update]
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (μ : Measure (State S0 S1 S2 X)) [IsProbabilityMeasure μ]
    (hA : ∀ t, G.player2.action =ᵐ[stateLaw (G.toModel P).inducedKernel μ t] a.action)
    (hU : ∀ t, ∀ᵐ z ∂(stateLaw (G.toModel P).inducedKernel μ t ⊗ₘ
        (G.toModel P).actionWorldKernel),
      G.player2.update ((z.1,z.2.1),z.2.2) = a.update ((z.1,z.2.1),z.2.2)) (n : ℕ) :
    (stateLaw (G.toModel P).inducedKernel μ n).map anchorKey =
      stateLaw d.keyKernel (μ.map anchorKey) n := by
  apply projected_stateLaw_eq _ _ _ anchorKey measurable_anchorKey
  intro t
  have hh := actual_rows_ae_of_primitive_agreement G G.player1 G.player2 a P
    (stateLaw (G.toModel P).inducedKernel μ t) (hA t) (hU t)
  change (G.toModel P).inducedKernel =ᵐ[stateLaw (G.toModel P).inducedKernel μ t]
    ((G.openLoop G.player1 a).toModel P).inducedKernel at hh
  filter_upwards [hh] with y hy
  rw [hy]
  exact d.actual_key_row G.player1 P y

theorem Profile.baseline_input_marginal (d : Profile G a) [IsMarkovKernel d.action]
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (μ : Measure (State S0 S1 S2 X)) [SFinite μ]
    (hA : G.player2.action =ᵐ[μ] a.action) :
    (μ ⊗ₘ (G.toModel P).actionWorldKernel).map inputMark =
      μ.map anchorKey ⊗ₘ d.action := by
  letI := (G.toModel P).actionWorldKernel_isMarkov
  letI := ((G.openLoop G.player1 a).toModel P).actionWorldKernel_isMarkov
  have hh := actual_actionWorld_rows_ae G G.player1 G.player2 a P μ hA
  change (G.toModel P).actionWorldKernel =ᵐ[μ]
    ((G.openLoop G.player1 a).toModel P).actionWorldKernel at hh
  rw [Measure.compProd_congr hh]
  exact d.actual_input_marginal G.player1 P μ

/-- Countably determined whole-kernel equality events let actual baseline
primitive agreement descend to the autonomous marked input law. -/
theorem primitive_factor_agreement [StandardBorelSpace A2] [StandardBorelSpace S2]
    (da : Profile G a) (db : Profile G b)
    [IsMarkovKernel da.action] [IsMarkovKernel db.action]
    [IsMarkovKernel da.update] [IsMarkovKernel db.update]
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (μ : Measure (State S0 S1 S2 X)) [SFinite μ]
    (hAa : G.player2.action =ᵐ[μ] a.action)
    (hAb : G.player2.action =ᵐ[μ] b.action)
    (hUa : ∀ᵐ z ∂(μ ⊗ₘ (G.toModel P).actionWorldKernel),
      G.player2.update ((z.1,z.2.1),z.2.2) = a.update ((z.1,z.2.1),z.2.2))
    (hUb : ∀ᵐ z ∂(μ ⊗ₘ (G.toModel P).actionWorldKernel),
      G.player2.update ((z.1,z.2.1),z.2.2) = b.update ((z.1,z.2.1),z.2.2)) :
    (da.action =ᵐ[μ.map anchorKey] db.action) ∧
      (da.update =ᵐ[μ.map anchorKey ⊗ₘ da.action] db.update) := by
  constructor
  · apply (ae_map_iff measurable_anchorKey.aemeasurable
      (PermanssonResearch.Probability.measurableSet_kernel_equality da.action db.action)).mpr
    filter_upwards [hAa,hAb] with y hya hyb
    simpa only [da.action_apply,db.action_apply] using hya.symm.trans hyb
  · rw [← da.baseline_input_marginal P μ hAa]
    apply (ae_map_iff measurable_inputMark.aemeasurable
      (PermanssonResearch.Probability.measurableSet_kernel_equality da.update db.update)).mpr
    filter_upwards [hUa,hUb] with z hza hzb
    simpa only [da.update_apply,db.update_apply,anchorUpdateKey,inputMark]
      using hza.symm.trans hzb

/-- Transfer the primitive equality events to any actual treated state law
with the baseline key marginal. The update event is pulled through the actual
marked action/world input law, retaining the realized opponent action. -/
theorem actual_primitive_agreement_of_key_agreement
    (da : Profile G a) (db : Profile G b) [IsMarkovKernel da.action]
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (ρ : Measure (State S0 S1 S2 X)) [SFinite ρ] (ν : Measure (S0 × S2))
    (hkey : ρ.map anchorKey = ν)
    (hA : da.action =ᵐ[ν] db.action)
    (hU : da.update =ᵐ[ν ⊗ₘ da.action] db.update) :
    (a.action =ᵐ[ρ] b.action) ∧
      (∀ᵐ z ∂(ρ ⊗ₘ ((G.openLoop r a).toModel P).actionWorldKernel),
        a.update ((z.1,z.2.1),z.2.2) = b.update ((z.1,z.2.1),z.2.2)) := by
  constructor
  · have hh : da.action =ᵐ[ρ.map anchorKey] db.action := by rwa [hkey]
    have ht := ae_of_ae_map measurable_anchorKey.aemeasurable hh
    filter_upwards [ht] with y hy
    simpa only [da.action_apply,db.action_apply] using hy
  · have hm : (ρ ⊗ₘ ((G.openLoop r a).toModel P).actionWorldKernel).map inputMark =
        ν ⊗ₘ da.action := by rw [da.actual_input_marginal r P ρ,hkey]
    have hh : da.update =ᵐ[(ρ ⊗ₘ ((G.openLoop r a).toModel P).actionWorldKernel).map inputMark]
        db.update := by rwa [hm]
    have ht := ae_of_ae_map measurable_inputMark.aemeasurable hh
    filter_upwards [ht] with z hz
    simpa only [da.update_apply,db.update_apply,anchorUpdateKey,inputMark] using hz

end
end PermanssonResearch.MultiAgent.Autonomous
