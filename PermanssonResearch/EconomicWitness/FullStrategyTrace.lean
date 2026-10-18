import PermanssonResearch.EconomicWitness.Incentives
import PermanssonResearch.EconomicWitness.Geometry
import PermanssonResearch.StrategicWorld.ActionTraceInitialLaw
import PermanssonResearch.StrategicWorld.ActionTraceOriginalBridge

/-! The economic incentive and original-regime gates refer to the same actual
baseline process; every finite initial probability measure is admitted. -/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch.EconomicWitness
open ActionTrace DiscountedVerification
set_option autoImplicit false

theorem expected_behavioral_optimality_initial_measure
    (i : Player) (σ : BehavioralPolicy Y Bool)
    (μ : Measure Y) [IsProbabilityMeasure μ] :
    (∫ w, (∑' n, (3/4 : ℝ)^n * pathReward (strategyGame i) n w)
      ∂canonicalLaw (strategyGame i) σ (Row.ofMeasure μ)) ≤ ∫ y, value i y ∂μ :=
  expected_verification_initial_measure (strategyGame i) σ μ (value i)
    (reward_bound i) (value_bound i) (pure_bellman i)

noncomputable def baselineRow (_y : Y) : Row Bool := Row.pure false

theorem baseline_stateStep_actual (i : Player) (y : Y) :
    (stateStep (strategyGame i) baselineRow y).measure = model.inducedKernel y := by
  apply Measure.ext_of_singleton
  intro z
  rw [Row.measure_singleton,induced_atom]
  rcases y with ⟨u,x⟩
  rcases z with ⟨v,z⟩
  cases u
  cases v
  fin_cases i <;> fin_cases x <;> fin_cases z <;>
    norm_num [stateStep,strategyGame,baselineRow,Row.bind,Row.map,Row.pure,
      worldRow,fairRow,assemble,Fin.sum_univ_three,Fintype.sum_prod_type]
  all_goals
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num

theorem baseline_trace_stateLaw_eq_original (i : Player) (μ : Row Y) :
    (canonicalLaw (strategyGame i) baselineBehavior μ).map statePath =
      model.pathLaw μ.measure :=
  canonical_state_erasure_eq_original model (strategyGame i) baselineRow μ
    (baseline_stateStep_actual i)

end PermanssonResearch.EconomicWitness
