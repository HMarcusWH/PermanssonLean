import PermanssonResearch.MultipleLimit.ExactSixStateClassLaws
import Mathlib.Tactic

/-!
# C53-17 — exact WHOLE law of the actual six-state random occupation limit

Under the authentic infinite typed alpha/P/U model, from t or u the
physical empirical occupation converges almost surely to one of TWO
distinct invariant probability measures πA/πB, not their barycenter.

The distribution of this physical probability-measure-valued limit is
exactly (1/3)·δ_{πA}+(2/3)·δ_{πB}. The weights are not assigned: they
were derived from the finite-prefix hitting recurrences, monotone
infinite-horizon measure continuity, and canonical class-selection
identification. Periodicity in class A is allowed.

This proof concerns the genuine law on probability measures, not an
expectation or approximation to the recurrent class mixture.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactSixStateFullRandomLaw

open PermanssonLean
open ReverseSolver.FiniteStrategicRealization
open ExactSixStateTyped
open ExactSixStateClassSelectionWeights
open ExactSixStateClassLaws
open FiniteCanonicalPath
open FiniteOccupationRandomLaw
open CanonicalClassSelector

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

abbrev SixY := JointState Unit (Fin 6)
private abbrev K := typedModel.inducedKernel

private def EA : Set (ℕ → SixY) :=
  {w | selectedRepresentative K w ∈ classASet}

private def EB : Set (ℕ → SixY) :=
  {w | selectedRepresentative K w ∈ classBSet}

private theorem EA_measurable : MeasurableSet EA :=
  ((Set.toFinite classASet).measurableSet).preimage
    (selectedRepresentative_measurable K)

private theorem EB_measurable : MeasurableSet EB :=
  ((Set.toFinite classBSet).measurableSet).preimage
    (selectedRepresentative_measurable K)

private theorem events_partition : EA ∪ EB = Set.univ := by
  ext w
  simp only [EA, EB, Set.mem_union, Set.mem_setOf_eq,
    Set.mem_univ, iff_true]
  exact selected_in_A_or_B w

private theorem events_disjoint : Disjoint EA EB := by
  apply Set.disjoint_left.mpr
  intro w hwA hwB
  exact Set.disjoint_left.mp classASet_disjoint_classBSet hwA hwB

private theorem EA_EB_weights_normalized
    (P : Measure (ℕ → SixY)) [IsProbabilityMeasure P] :
    P EA + P EB = 1 := by
  have h := measure_union events_disjoint EB_measurable (μ := P)
  rw [events_partition, measure_univ] at h
  exact h.symm

private theorem physical_eq_A_of_event
    (w : ℕ → SixY) (hw : w ∈ EA) :
    physicalOccupationLimit K w = πA :=
  actualPhysicalLimit_eq_piA_of_selected_A w hw

private theorem physical_eq_B_of_event
    (w : ℕ → SixY) (hw : w ∈ EB) :
    physicalOccupationLimit K w = πB :=
  actualPhysicalLimit_eq_piB_of_selected_B w hw

/-- Two-valued measurable random variables have exactly the displayed
two-Dirac pushforward law, once the genuine two event weights are known.
The proof is an equality of ALL measurable target sets, not a moment. -/
theorem full_random_law_from_class_weights
    (P : Measure (ℕ → SixY)) [IsProbabilityMeasure P] :
    P.map (physicalOccupationLimit K) =
      (P EA) • Measure.dirac πA +
      (P EB) • Measure.dirac πB := by
  apply Measure.ext
  intro E hE
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hE, Measure.dirac_apply' _ hE]
  rw [Measure.map_apply (physicalOccupationLimit_measurable K) hE]
  change P {w : ℕ → SixY | physicalOccupationLimit K w ∈ E} =
    (P EA) * (if πA ∈ E then 1 else 0) +
    (P EB) * (if πB ∈ E then 1 else 0)
  by_cases ha : πA ∈ E
  · by_cases hb : πB ∈ E
    · have hp :
        {w : ℕ → SixY | physicalOccupationLimit K w ∈ E} =
          Set.univ := by
        ext w
        rcases selected_in_A_or_B w with hA | hB
        · simp [actualPhysicalLimit_eq_piA_of_selected_A w hA, ha]
        · simp [actualPhysicalLimit_eq_piB_of_selected_B w hB, hb]
      rw [hp, measure_univ]
      simpa [ha, hb] using (EA_EB_weights_normalized P).symm
    · have hp :
        {w : ℕ → SixY | physicalOccupationLimit K w ∈ E} = EA := by
        ext w
        rcases selected_in_A_or_B w with hA | hB
        · simp [EA, actualPhysicalLimit_eq_piA_of_selected_A w hA,
            hA, ha]
        · have hnotA : ¬ selectedRepresentative K w ∈ classASet := by
            intro he
            exact Set.disjoint_left.mp classASet_disjoint_classBSet he hB
          simp [EA, actualPhysicalLimit_eq_piB_of_selected_B w hB,
            hnotA, hb]
      rw [hp]
      simp [ha, hb]
  · by_cases hb : πB ∈ E
    · have hp :
        {w : ℕ → SixY | physicalOccupationLimit K w ∈ E} = EB := by
        ext w
        rcases selected_in_A_or_B w with hA | hB
        · have hnotB : ¬ selectedRepresentative K w ∈ classBSet := by
            intro he
            exact Set.disjoint_left.mp classASet_disjoint_classBSet hA he
          simp [EB, actualPhysicalLimit_eq_piA_of_selected_A w hA,
            hnotB, ha]
        · simp [EB, actualPhysicalLimit_eq_piB_of_selected_B w hB,
            hB, hb]
      rw [hp]
      simp [ha, hb]
    · have hp :
        {w : ℕ → SixY | physicalOccupationLimit K w ∈ E} =
          (∅ : Set (ℕ → SixY)) := by
        ext w
        rcases selected_in_A_or_B w with hA | hB
        · simp [actualPhysicalLimit_eq_piA_of_selected_A w hA, ha]
        · simp [actualPhysicalLimit_eq_piB_of_selected_B w hB, hb]
      rw [hp, measure_empty]
      simp [ha, hb]

/-- Exact two-atom RANDOM PHYSICAL OCCUPATION LIMIT from the true
six-state u point start. In conjunction with
physicalOccupationLimit_ae_correct this is the entire limiting law. -/
theorem full_random_occupation_law_u :
    (typedModel.pathLaw (Measure.dirac (decode (1 : Fin 6)))).map
      (physicalOccupationLimit K) =
      ENNReal.ofReal (1/3 : ℝ) • Measure.dirac πA +
      ENNReal.ofReal (2/3 : ℝ) • Measure.dirac πB := by
  rw [full_random_law_from_class_weights]
  rw [selected_A_weight_u, selected_B_weight_u]

theorem full_random_occupation_law_t :
    (typedModel.pathLaw (Measure.dirac (decode (0 : Fin 6)))).map
      (physicalOccupationLimit K) =
      ENNReal.ofReal (1/3 : ℝ) • Measure.dirac πA +
      ENNReal.ofReal (2/3 : ℝ) • Measure.dirac πB := by
  rw [full_random_law_from_class_weights]
  rw [selected_A_weight_t, selected_B_weight_t]

/-- The end-to-end physical limit is genuine almost-sure convergence
under BOTH transient point starts, with certified distinct outcomes. -/
theorem actual_six_state_physical_occupation_u :
    ∀ᵐ w ∂typedModel.pathLaw (Measure.dirac (decode (1 : Fin 6))),
      Tendsto (fun n : ℕ =>
        FiniteStateOccupation.empiricalOccupation w (n+1)
          (Nat.succ_pos n))
        atTop (𝓝 (physicalOccupationLimit K w)) := by
  exact physicalOccupationLimit_ae_correct K
    (diracProba (decode (1 : Fin 6)))

/-- The same a.s. physical occupation convergence also holds under the
transient t start, independently of which recurrent class is selected. -/
theorem actual_six_state_physical_occupation_t :
    ∀ᵐ w ∂typedModel.pathLaw (Measure.dirac (decode (0 : Fin 6))),
      Tendsto (fun n : ℕ =>
        FiniteStateOccupation.empiricalOccupation w (n+1)
          (Nat.succ_pos n))
        atTop (𝓝 (physicalOccupationLimit K w)) := by
  exact physicalOccupationLimit_ae_correct K
    (diracProba (decode (0 : Fin 6)))

end ExactSixStateFullRandomLaw
end MultipleLimit
end PermanssonResearch
