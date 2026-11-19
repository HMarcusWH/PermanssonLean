import PermanssonResearch.Probability.FullPathProductTV
import PermanssonResearch.Perturbation.PrimitiveProductTV
import PermanssonResearch.Probability.DependentHistoryCommonMass
import PermanssonResearch.Probability.DependentThreeStageSaturation
import PermanssonResearch.StrategicWorld.ActionTrace
import PermanssonResearch.Probability.EventTVCalculus

/-!
Original Q-03: embed the existing dependent finite history law into the
repository's actual measure/event-TV interface. The old normalized atoms and
generic conditional-product theorem are unchanged. This finite example makes
no assumption of unconditional independence and no infinite-path assertion.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace PermanssonResearch.Certification.Tranche10Q03

open PermanssonResearch.Probability.DependentThreeStage
open PermanssonResearch.ActionTrace
open PermanssonLean.ProbabilitySupport

noncomputable def dependentRow : Row History where
  mass := dependentLaw.atom
  nonneg := dependentLaw.nonnegative
  total := by simpa [dependentLaw] using dependentLaw.normalized

noncomputable def perfectRow : Row History where
  mass := perfectLaw.atom
  nonneg := perfectLaw.nonnegative
  total := by simpa [perfectLaw] using perfectLaw.normalized

noncomputable def dependentMeasure : Measure History := dependentRow.measure
noncomputable def perfectMeasure : Measure History := perfectRow.measure

instance dependentMeasure_probability : IsProbabilityMeasure dependentMeasure :=
  inferInstanceAs (IsProbabilityMeasure dependentRow.measure)

instance perfectMeasure_probability : IsProbabilityMeasure perfectMeasure :=
  inferInstanceAs (IsProbabilityMeasure perfectRow.measure)

/-- Every original normalized atom is retained in the actual measure. -/
theorem dependent_measure_atom (w : History) :
    dependentMeasure {w} = ENNReal.ofReal (dependentLaw.atom w) := by
  exact Row.measure_singleton dependentRow w

theorem perfect_measure_atom (w : History) :
    perfectMeasure {w} = ENNReal.ofReal (perfectLaw.atom w) := by
  exact Row.measure_singleton perfectRow w

noncomputable def commonMeasure : Measure History :=
  ENNReal.ofReal (27 / 50 : ℝ) • Measure.dirac (true, (true, true))

instance commonMeasure_finite : IsFiniteMeasure commonMeasure := by
  refine ⟨?_⟩
  simp [commonMeasure, Measure.smul_apply, smul_eq_mul]

theorem common_le_dependent : commonMeasure ≤ dependentMeasure := by
  have h := Finset.single_le_sum
    (f := fun w : History => ENNReal.ofReal (dependentLaw.atom w) • Measure.dirac w)
    (fun _ _ => bot_le) (Finset.mem_univ (true, (true, true)))
  simpa [commonMeasure, dependentMeasure, Row.measure, dependentRow,
    true_history_mass] using h

theorem common_le_perfect : commonMeasure ≤ perfectMeasure := by
  have h := Finset.single_le_sum
    (f := fun w : History => ENNReal.ofReal (perfectLaw.atom w) • Measure.dirac w)
    (fun _ _ => bot_le) (Finset.mem_univ (true, (true, true)))
  have hsmall : commonMeasure ≤
      ENNReal.ofReal (perfectLaw.atom (true, (true, true))) •
        Measure.dirac (true, (true, true)) := by
    unfold commonMeasure
    gcongr
    norm_num [perfectLaw, perfectAtom]
  exact hsmall.trans (by simpa [perfectMeasure, Row.measure, perfectRow] using h)

theorem common_mass_exact : commonMeasure.real Set.univ = 27 / 50 := by
  norm_num [commonMeasure, Measure.real, Measure.smul_apply, smul_eq_mul]

/-- The original event-supremum TV, not merely half-L1 of an atom table. -/
theorem actual_event_tv_exact :
    eventTotalVariation dependentMeasure perfectMeasure = 23 / 50 := by
  apply le_antisymm
  · have h := eventTotalVariation_le_one_sub_commonMass
      common_le_dependent common_le_perfect
    rw [common_mass_exact] at h
    norm_num at h ⊢
    exact h
  · have h := abs_measureReal_sub_le_eventTotalVariation
      dependentMeasure perfectMeasure
      (s := {(true, (true, true))}) (by measurability)
    norm_num [Measure.real, dependent_measure_atom, perfect_measure_atom,
      true_history_mass, perfectLaw, perfectAtom] at h ⊢
    exact h

/-- Reconciles the previously proved half-L1 computation with event TV. -/
theorem halfL1_eq_actual_event_tv :
    finiteHalfL1 = eventTotalVariation dependentMeasure perfectMeasure := by
  rw [dependent_three_stage_halfL1_exact, actual_event_tv_exact]

/-- A failed first stage cannot be followed by a successful second stage. -/
theorem failed_then_success_atom_zero (c : Bool) :
    dependentLaw.atom (false, (true, c)) = 0 := by
  cases c <;> norm_num [dependentLaw, dependentAtom, initialStep, nextRow]

theorem first_failure_probability :
    dependentMeasure.real {w | w.1 = false} = 1 / 10 := by
  norm_num [Measure.real, dependentMeasure, Row.measure, dependentRow,
    dependentLaw, dependentAtom, initialStep, nextRow,
    Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply',
    Fintype.sum_prod_type, Fintype.sum_bool, smul_eq_mul]

theorem second_success_probability :
    dependentMeasure.real {w | w.2.1 = true} = 18 / 25 := by
  norm_num [Measure.real, dependentMeasure, Row.measure, dependentRow,
    dependentLaw, dependentAtom, initialStep, nextRow,
    Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply',
    Fintype.sum_prod_type, Fintype.sum_bool, smul_eq_mul, ENNReal.toReal_add]

theorem failure_then_success_probability :
    dependentMeasure.real {w | w.1 = false ∧ w.2.1 = true} = 0 := by
  norm_num [Measure.real, dependentMeasure, Row.measure, dependentRow,
    dependentLaw, dependentAtom, initialStep, nextRow,
    Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply',
    Fintype.sum_prod_type, Fintype.sum_bool, smul_eq_mul]

/-- The actual two-coordinate events violate unconditional product independence. -/
theorem unconditional_event_product_fails :
    dependentMeasure.real {w | w.1 = false ∧ w.2.1 = true} ≠
      dependentMeasure.real {w | w.1 = false} *
        dependentMeasure.real {w | w.2.1 = true} := by
  rw [first_failure_probability, second_success_probability,
    failure_then_success_probability]
  norm_num

end PermanssonResearch.Certification.Tranche10Q03

-- Tranche10 complete named receipt coverage.
#check PermanssonResearch.Probability.DependentThreeStage.initialStep
#print axioms PermanssonResearch.Probability.DependentThreeStage.initialStep
#check PermanssonResearch.Probability.DependentThreeStage.nextRow
#print axioms PermanssonResearch.Probability.DependentThreeStage.nextRow
#check PermanssonResearch.Probability.DependentThreeStage.dependentAtom
#print axioms PermanssonResearch.Probability.DependentThreeStage.dependentAtom
#check PermanssonResearch.Probability.DependentThreeStage.perfectAtom
#print axioms PermanssonResearch.Probability.DependentThreeStage.perfectAtom
#check PermanssonResearch.Probability.DependentThreeStage.dependentLaw
#print axioms PermanssonResearch.Probability.DependentThreeStage.dependentLaw
#check PermanssonResearch.Probability.DependentThreeStage.perfectLaw
#print axioms PermanssonResearch.Probability.DependentThreeStage.perfectLaw
#check PermanssonResearch.Probability.DependentThreeStage.true_history_mass
#print axioms PermanssonResearch.Probability.DependentThreeStage.true_history_mass
#check PermanssonResearch.Probability.DependentThreeStage.finiteHalfL1
#print axioms PermanssonResearch.Probability.DependentThreeStage.finiteHalfL1
#check PermanssonResearch.Probability.DependentThreeStage.dependent_three_stage_halfL1_exact
#print axioms PermanssonResearch.Probability.DependentThreeStage.dependent_three_stage_halfL1_exact
#check PermanssonResearch.Probability.DependentThreeStage.actual_retained_product
#print axioms PermanssonResearch.Probability.DependentThreeStage.actual_retained_product
#check PermanssonResearch.Probability.DependentHistory.evolution
#print axioms PermanssonResearch.Probability.DependentHistory.evolution
#check PermanssonResearch.Probability.DependentHistory.evolution_probability
#print axioms PermanssonResearch.Probability.DependentHistory.evolution_probability
#check PermanssonResearch.Probability.DependentHistory.evolution_mono
#print axioms PermanssonResearch.Probability.DependentHistory.evolution_mono
#check PermanssonResearch.Probability.DependentHistory.retained
#print axioms PermanssonResearch.Probability.DependentHistory.retained
#check PermanssonResearch.Probability.DependentHistory.common_mass_ge
#print axioms PermanssonResearch.Probability.DependentHistory.common_mass_ge
#check PermanssonResearch.Probability.DependentHistory.prefix_tv_le_product
#print axioms PermanssonResearch.Probability.DependentHistory.prefix_tv_le_product
#check PermanssonResearch.Perturbation.primitiveCommon_mass_ge_product
#print axioms PermanssonResearch.Perturbation.primitiveCommon_mass_ge_product
#check PermanssonResearch.Perturbation.inducedKernel_tv_le_primitive_product
#print axioms PermanssonResearch.Perturbation.inducedKernel_tv_le_primitive_product
#check PermanssonResearch.Probability.FullPathProduct.path_tv_le_product
#print axioms PermanssonResearch.Probability.FullPathProduct.path_tv_le_product
#check PermanssonResearch.Probability.FullPathProduct.zero_defect_product
#print axioms PermanssonResearch.Probability.FullPathProduct.zero_defect_product
#check PermanssonResearch.Probability.FullPathProduct.unit_defect_product
#print axioms PermanssonResearch.Probability.FullPathProduct.unit_defect_product
#check PermanssonResearch.Probability.FullPathProduct.recurring_leak_retained_tendsto_zero
#print axioms PermanssonResearch.Probability.FullPathProduct.recurring_leak_retained_tendsto_zero
#check PermanssonResearch.Probability.FullPathProduct.recurring_leak_budget_tendsto_one
#print axioms PermanssonResearch.Probability.FullPathProduct.recurring_leak_budget_tendsto_one
#check PermanssonResearch.ActionTrace.Row
#print axioms PermanssonResearch.ActionTrace.Row
#check PermanssonResearch.ActionTrace.Row.measure
#print axioms PermanssonResearch.ActionTrace.Row.measure
#check PermanssonResearch.ActionTrace.Row.measure_probability
#print axioms PermanssonResearch.ActionTrace.Row.measure_probability
#check PermanssonResearch.ActionTrace.Row.measure_singleton
#print axioms PermanssonResearch.ActionTrace.Row.measure_singleton
#check PermanssonResearch.ActionTrace.Row.expect_eq_integral
#print axioms PermanssonResearch.ActionTrace.Row.expect_eq_integral
#check PermanssonLean.ProbabilitySupport.eventTotalVariation
#print axioms PermanssonLean.ProbabilitySupport.eventTotalVariation
#check PermanssonLean.ProbabilitySupport.eventTotalVariation_le_one_sub_commonMass
#print axioms PermanssonLean.ProbabilitySupport.eventTotalVariation_le_one_sub_commonMass
#check PermanssonLean.ProbabilitySupport.abs_measureReal_sub_le_eventTotalVariation
#print axioms PermanssonLean.ProbabilitySupport.abs_measureReal_sub_le_eventTotalVariation
#check PermanssonResearch.Certification.Tranche10Q03.dependentRow
#print axioms PermanssonResearch.Certification.Tranche10Q03.dependentRow
#check PermanssonResearch.Certification.Tranche10Q03.perfectRow
#print axioms PermanssonResearch.Certification.Tranche10Q03.perfectRow
#check PermanssonResearch.Certification.Tranche10Q03.dependentMeasure
#print axioms PermanssonResearch.Certification.Tranche10Q03.dependentMeasure
#check PermanssonResearch.Certification.Tranche10Q03.perfectMeasure
#print axioms PermanssonResearch.Certification.Tranche10Q03.perfectMeasure
#check PermanssonResearch.Certification.Tranche10Q03.dependentMeasure_probability
#print axioms PermanssonResearch.Certification.Tranche10Q03.dependentMeasure_probability
#check PermanssonResearch.Certification.Tranche10Q03.perfectMeasure_probability
#print axioms PermanssonResearch.Certification.Tranche10Q03.perfectMeasure_probability
#check PermanssonResearch.Certification.Tranche10Q03.dependent_measure_atom
#print axioms PermanssonResearch.Certification.Tranche10Q03.dependent_measure_atom
#check PermanssonResearch.Certification.Tranche10Q03.perfect_measure_atom
#print axioms PermanssonResearch.Certification.Tranche10Q03.perfect_measure_atom
#check PermanssonResearch.Certification.Tranche10Q03.commonMeasure
#print axioms PermanssonResearch.Certification.Tranche10Q03.commonMeasure
#check PermanssonResearch.Certification.Tranche10Q03.commonMeasure_finite
#print axioms PermanssonResearch.Certification.Tranche10Q03.commonMeasure_finite
#check PermanssonResearch.Certification.Tranche10Q03.common_le_dependent
#print axioms PermanssonResearch.Certification.Tranche10Q03.common_le_dependent
#check PermanssonResearch.Certification.Tranche10Q03.common_le_perfect
#print axioms PermanssonResearch.Certification.Tranche10Q03.common_le_perfect
#check PermanssonResearch.Certification.Tranche10Q03.common_mass_exact
#print axioms PermanssonResearch.Certification.Tranche10Q03.common_mass_exact
#check PermanssonResearch.Certification.Tranche10Q03.actual_event_tv_exact
#print axioms PermanssonResearch.Certification.Tranche10Q03.actual_event_tv_exact
#check PermanssonResearch.Certification.Tranche10Q03.halfL1_eq_actual_event_tv
#print axioms PermanssonResearch.Certification.Tranche10Q03.halfL1_eq_actual_event_tv
#check PermanssonResearch.Certification.Tranche10Q03.failed_then_success_atom_zero
#print axioms PermanssonResearch.Certification.Tranche10Q03.failed_then_success_atom_zero
#check PermanssonResearch.Certification.Tranche10Q03.first_failure_probability
#print axioms PermanssonResearch.Certification.Tranche10Q03.first_failure_probability
#check PermanssonResearch.Certification.Tranche10Q03.second_success_probability
#print axioms PermanssonResearch.Certification.Tranche10Q03.second_success_probability
#check PermanssonResearch.Certification.Tranche10Q03.failure_then_success_probability
#print axioms PermanssonResearch.Certification.Tranche10Q03.failure_then_success_probability
#check PermanssonResearch.Certification.Tranche10Q03.unconditional_event_product_fails
#print axioms PermanssonResearch.Certification.Tranche10Q03.unconditional_event_product_fails
