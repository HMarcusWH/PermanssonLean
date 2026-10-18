import PermanssonResearch.MultiAgent.StrictMA2Obstruction

/-! The opponent action is retained from the ORIGINAL sampled one-step history.
This is a marked statement; equality of an unmarked key transition alone would
not imply it. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultiAgent.Autonomous

set_option autoImplicit false
open PermanssonLean

variable {S0 S1 S2 X A1 A2 : Type*}
variable [MeasurableSpace S0] [MeasurableSpace S1] [MeasurableSpace S2]
variable [MeasurableSpace X] [MeasurableSpace A1] [MeasurableSpace A2]
variable [Fintype S0] [Fintype S1] [Fintype S2] [Fintype X] [Fintype A1] [Fintype A2]
variable [MeasurableSingletonClass S0] [MeasurableSingletonClass S1]
variable [MeasurableSingletonClass S2] [MeasurableSingletonClass X]
variable [MeasurableSingletonClass A1] [MeasurableSingletonClass A2]

/-- Keep the sampled opponent action and the next common/private opponent key. -/
def opponentMark (z : (((A1 × A2) × X) × GameState S0 S1 S2)) :
    A2 × (S0 × S2) := (z.1.1.2,(z.2.1,z.2.2.2))

theorem measurable_opponentMark :
    Measurable (opponentMark (S0 := S0) (S1 := S1) (S2 := S2)
      (X := X) (A1 := A1) (A2 := A2)) := by
  unfold opponentMark
  fun_prop

/-- The autonomous marked row of the actual conditional-product protocol. -/
theorem autonomous_marked_atom
    (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (a : PlayerTwoMechanism S0 S1 S2 X A1 A2) (d : Profile G a)
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2)
    (y : State S0 S1 S2 X) (b : A2) (q : S0 × S2) :
    ((((G.openLoop r a).toModel P).oneStepHistoryKernel y).map opponentMark) {(b,q)} =
      d.common y.1.1 {q.1} * d.action (anchorKey y) {b} *
        d.update (anchorKey y,b) {q.2} := by
  classical
  let M := (G.openLoop r a).toModel P
  letI := G.common_isMarkov
  letI := r.action_isMarkov
  letI := r.update_isMarkov
  letI := a.action_isMarkov
  letI := a.update_isMarkov
  letI := M.world_isMarkov
  letI := M.generator.action_isMarkov
  letI := M.generator.update_isMarkov
  letI := StrategicWorldModel.reassociatedUpdate_isMarkov M
  letI := StrategicWorldModel.actionWorldKernel_isMarkov M
  rw [Measure.map_apply measurable_opponentMark (measurableSet_singleton (b,q))]
  change M.oneStepHistoryKernel y (opponentMark ⁻¹' ({(b,q)} : Set (A2 × (S0 × S2)))) = _
  rw [StrategicWorldModel.oneStepHistoryKernel,
    Kernel.compProd_apply ((measurableSet_singleton (b,q)).preimage measurable_opponentMark),
    StrategicWorldModel.actionWorldKernel, Kernel.lintegral_compProd]
  · change (∫⁻ v : A1 × A2, ∫⁻ x : X,
      (G.openLoop r a).toGenerator.update ((y,v),x)
        {s : GameState S0 S1 S2 | opponentMark ((v,x),s) = (b,q)}
      ∂P (y,v) ∂(G.openLoop r a).toGenerator.action y) = _
    have hset (v : A1 × A2) (x : X) :
        {s : GameState S0 S1 S2 | opponentMark ((v,x),s) = (b,q)} =
        if v.2 = b then ({q.1} : Set S0) ×ˢ (Set.univ ×ˢ ({q.2} : Set S2))
        else ∅ := by
      rcases q with ⟨q0,q2⟩
      ext s
      rcases s with ⟨s0,s1,s2⟩
      by_cases hv : v.2 = b <;> simp [opponentMark, hv, Prod.mk.injEq]
    simp_rw [hset]
    simp only [apply_ite, measure_empty, TwoPlayerGenerator.toGenerator_update_apply,
      Measure.prod_prod, measure_univ, one_mul, TwoPlayerGenerator.openLoop]
    simp_rw [d.common_apply,d.update_apply]
    simp only [commonUpdateKey,anchorUpdateKey,lintegral_const,measure_univ,mul_one]
    rw [TwoPlayerGenerator.toGenerator_action_apply]
    simp only [TwoPlayerGenerator.openLoop]
    rw [MeasureTheory.lintegral_prod _ (measurable_of_finite _).aemeasurable]
    simp_rw [d.action_apply]
    simp only [lintegral_const,measure_univ,mul_one]
    rw [lintegral_fintype]
    simp only [ite_mul,zero_mul]
    simp
    ring
  · exact Kernel.measurable_kernel_prodMk_left'
      ((measurableSet_singleton (b,q)).preimage measurable_opponentMark) y

end PermanssonResearch.MultiAgent.Autonomous
