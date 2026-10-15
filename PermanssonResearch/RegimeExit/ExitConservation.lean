import PermanssonResearch.RegimeExit.ExitRouting
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Tactic

/-!
# C-Exit — exact finite/infinite routing under genuine path probabilities

This theorem layer never accesses a trajectory at an infinite stopping
index and never upgrades an output-restricted kernel to a Markov kernel.
All first-exit distribution statements enforce initial support on B.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory Topology

namespace PermanssonResearch.RegimeExit
open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA uH
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]

/-- Genuine finite routing = probability of one of the disjoint first exits. -/
theorem exitRouting_eq_prob_exit_in
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (L : ℕ) {y : JointState S X} (hy : y ∈ spec.region)
    (D : Set (JointState S X)) (hD : MeasurableSet D) :
    exitRoutingFinite M spec L y D =
      M.pathLaw (Measure.dirac y) (firstExitWithinDestination spec L D) := by
  induction L with
  | zero =>
      simp [exitRoutingFinite_zero, firstExitWithinDestination_zero]
  | succ L ih =>
      have hDisj := firstExitWithinDestination_disjoint_last spec L D
      have hMeas := firstExitAtDestination_measurable spec L D hD
      calc
        exitRoutingFinite M spec (L+1) y D =
            exitRoutingFinite M spec L y D +
              firstExitStepMass M spec L y D :=
          exitRoutingFinite_succ M spec L y D hD
        _ = M.pathLaw (Measure.dirac y)
              (firstExitWithinDestination spec L D) +
            M.pathLaw (Measure.dirac y)
              (firstExitAtDestination spec L D) := by
              rw [ih, ← firstExitStep_eq_pathEvent M spec L hy D hD]
        _ = M.pathLaw (Measure.dirac y)
              (firstExitWithinDestination spec (L+1) D) := by
          rw [firstExitWithinDestination_succ]
          exact (measure_union hDisj hMeas).symm

theorem exitRoutingFromLaw_eq_prob_exit_in
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (L : ℕ) (μ : ProbabilityMeasure (JointState S X))
    (hSupport : μ.toMeasure spec.region = 1)
    (D : Set (JointState S X)) (hD : MeasurableSet D) :
    exitRoutingFiniteFromLaw M spec L μ D =
      M.pathLaw μ.toMeasure (firstExitWithinDestination spec L D) := by
  induction L with
  | zero => simp [exitRoutingFiniteFromLaw, exitRoutingFiniteMeasureFromLaw,
      firstExitWithinDestination_zero]
  | succ L ih =>
      have hDisj := firstExitWithinDestination_disjoint_last spec L D
      have hMeas := firstExitAtDestination_measurable spec L D hD
      calc
        exitRoutingFiniteFromLaw M spec (L+1) μ D =
          exitRoutingFiniteFromLaw M spec L μ D +
            firstExitStepMeasureFromLaw M spec μ L D := by
            simp [exitRoutingFiniteFromLaw,
              exitRoutingFiniteMeasureFromLaw, Measure.add_apply]
        _ = M.pathLaw μ.toMeasure
              (firstExitWithinDestination spec L D) +
            M.pathLaw μ.toMeasure
              (firstExitAtDestination spec L D) := by
            rw [ih, ← firstExitStepFromLaw_eq_pathEvent
              M spec μ hSupport L D hD]
        _ = M.pathLaw μ.toMeasure
              (firstExitWithinDestination spec (L+1) D) := by
            rw [firstExitWithinDestination_succ]
            exact (measure_union hDisj hMeas).symm

theorem exitRoutingInfinite_eq_prob_exit_in
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {y : JointState S X} (hy : y ∈ spec.region)
    (D : Set (JointState S X)) (hD : MeasurableSet D) :
    exitRoutingInfinite M spec y D =
      M.pathLaw (Measure.dirac y) (firstExitEverDestination spec D) := by
  let P := M.pathLaw (Measure.dirac y)
  have hPair :
      Pairwise (fun n m : ℕ =>
        Disjoint (firstExitAtDestination spec n D)
          (firstExitAtDestination spec m D)) := by
    intro n m hne
    exact firstExitAtDestination_disjoint spec D hne
  have hMeas : ∀ n, MeasurableSet (firstExitAtDestination spec n D) :=
    fun n => firstExitAtDestination_measurable spec n D hD
  calc
    exitRoutingInfinite M spec y D =
        ∑' n : ℕ, firstExitStepMass M spec n y D := by
      exact exitRoutingInfiniteMeasure_apply M spec y D hD
    _ = ∑' n : ℕ, P (firstExitAtDestination spec n D) := by
      congr 1
      funext n
      exact (firstExitStep_eq_pathEvent M spec n hy D hD).symm
    _ = P (firstExitEverDestination spec D) := by
      rw [firstExitEverDestination, measure_iUnion hPair hMeas]

theorem exitRoutingInfiniteFromLaw_eq_prob_exit_in
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (hSupport : μ.toMeasure spec.region = 1)
    (D : Set (JointState S X)) (hD : MeasurableSet D) :
    exitRoutingInfiniteFromLaw M spec μ D =
      M.pathLaw μ.toMeasure (firstExitEverDestination spec D) := by
  let P := M.pathLaw μ.toMeasure
  have hPair :
      Pairwise (fun n m : ℕ =>
        Disjoint (firstExitAtDestination spec n D)
          (firstExitAtDestination spec m D)) := by
    intro n m hne
    exact firstExitAtDestination_disjoint spec D hne
  have hMeas : ∀ n, MeasurableSet (firstExitAtDestination spec n D) :=
    fun n => firstExitAtDestination_measurable spec n D hD
  calc
    exitRoutingInfiniteFromLaw M spec μ D =
        ∑' n : ℕ, firstExitStepMeasureFromLaw M spec μ n D :=
      exitRoutingInfiniteMeasureFromLaw_apply M spec μ D hD
    _ = ∑' n : ℕ, P (firstExitAtDestination spec n D) := by
      congr 1
      funext n
      exact (firstExitStepFromLaw_eq_pathEvent M spec μ hSupport n D hD).symm
    _ = P (firstExitEverDestination spec D) := by
      rw [firstExitEverDestination, measure_iUnion hPair hMeas]

/-- The union of first exits and finite survival is exactly the set of
paths whose initial coordinate lies inside B. -/
theorem firstExitFinite_partition
    (spec : RegimeSpecification (JointState S X) H)
    (L : ℕ) :
    firstExitWithinDestination spec L Set.univ ∪
      survivesThroughSet spec L =
    (fun w : ℕ → JointState S X => w 0) ⁻¹' spec.region := by
  ext w
  constructor
  · rintro (hExit | hSurv)
    · change w ∈ (⋃ n : Fin L, firstExitAtDestination spec (n : ℕ) Set.univ)
        at hExit
      obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hExit
      exact hn.1 0 (by omega)
    · exact hSurv 0 (by omega)
  · intro h0
    by_cases hstay : w ∈ survivesThroughSet spec L
    · exact Or.inr hstay
    · exact Or.inl
        ((firstExitWithinDestination_iff_not_survives spec L w h0).2 hstay)

theorem firstExitFinite_partition_disjoint
    (spec : RegimeSpecification (JointState S X) H)
    (L : ℕ) :
    Disjoint (firstExitWithinDestination spec L Set.univ)
      (survivesThroughSet spec L) := by
  apply Set.disjoint_left.mpr
  intro w hExit hStay
  have h0 : w 0 ∈ spec.region := hStay 0 (by omega)
  exact ((firstExitWithinDestination_iff_not_survives
    spec L w h0).1 hExit) hStay

theorem firstExitInfinite_partition
    (spec : RegimeSpecification (JointState S X) H) :
    firstExitEverDestination spec Set.univ ∪ survivesForeverSet spec =
      (fun w : ℕ → JointState S X => w 0) ⁻¹' spec.region := by
  ext w
  constructor
  · rintro (hExit | hForever)
    · obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hExit
      exact hn.1 0 (by omega)
    · exact hForever 0
  · intro h0
    by_cases hs : w ∈ survivesForeverSet spec
    · exact Or.inr hs
    · exact Or.inl
        ((firstExitEverDestination_iff_not_survivesForever spec w h0).2 hs)

theorem firstExitInfinite_partition_disjoint
    (spec : RegimeSpecification (JointState S X) H) :
    Disjoint (firstExitEverDestination spec Set.univ)
      (survivesForeverSet spec) := by
  apply Set.disjoint_left.mpr
  intro w hExit hForever
  have h0 : w 0 ∈ spec.region := hForever 0
  exact ((firstExitEverDestination_iff_not_survivesForever
    spec w h0).1 hExit) hForever

/-- Exact nonnegative mass conservation, for L transitions, from B. -/
theorem exitRouting_add_killedSurvivalMass_eq_one
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (L : ℕ) {y : JointState S X} (hy : y ∈ spec.region) :
    exitRoutingFinite M spec L y (Set.univ \ spec.region) +
      killedSurvivalMass M spec L y = 1 := by
  let P := M.pathLaw (Measure.dirac y)
  have hstart : P ((fun w : ℕ → JointState S X => w 0) ⁻¹' spec.region) = 1 := by
    rw [← Measure.map_apply (measurable_pi_apply 0) spec.region_measurable]
    rw [StrategicWorldModel.pathLaw_eval_zero M (Measure.dirac y)]
    simp [hy]
  have hsplit :
      P (firstExitWithinDestination spec L Set.univ) +
        P (survivesThroughSet spec L) = 1 := by
    rw [← measure_union (firstExitFinite_partition_disjoint spec L)
      (measurableSet_survivesThroughSet spec L)]
    rw [firstExitFinite_partition]
    exact hstart
  have hroute :
      firstExitWithinDestination spec L (Set.univ \ spec.region) =
        firstExitWithinDestination spec L Set.univ := by
    ext w
    simp [firstExitWithinDestination, firstExitAtDestination]
  rw [exitRouting_eq_prob_exit_in M spec L hy
      (Set.univ \ spec.region) (MeasurableSet.univ.diff spec.region_measurable),
    hroute, ← survivalProbability_eq_killedSurvivalMass M spec L hy]
  exact hsplit

/-- The exact mass outside B plus all-state survival through L from μ is one. -/
theorem exitRoutingFromLaw_add_survival_eq_one
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (L : ℕ) (μ : ProbabilityMeasure (JointState S X))
    (hSupport : μ.toMeasure spec.region = 1) :
    exitRoutingFiniteFromLaw M spec L μ (Set.univ \ spec.region) +
      survivalProbabilityFromLaw M spec μ L = 1 := by
  let P := M.pathLaw μ.toMeasure
  have hstart :
      P ((fun w : ℕ → JointState S X => w 0) ⁻¹' spec.region) = 1 := by
    rw [← Measure.map_apply (measurable_pi_apply 0) spec.region_measurable]
    rw [StrategicWorldModel.pathLaw_eval_zero M μ.toMeasure]
    exact hSupport
  have hsplit :
      P (firstExitWithinDestination spec L Set.univ) +
        P (survivesThroughSet spec L) = 1 := by
    rw [← measure_union (firstExitFinite_partition_disjoint spec L)
      (measurableSet_survivesThroughSet spec L)]
    rw [firstExitFinite_partition]
    exact hstart
  have hroute :
      firstExitWithinDestination spec L (Set.univ \ spec.region) =
        firstExitWithinDestination spec L Set.univ := by
    ext w
    simp [firstExitWithinDestination, firstExitAtDestination]
  rw [exitRoutingFromLaw_eq_prob_exit_in
    M spec L μ hSupport
      (Set.univ \ spec.region)
      (MeasurableSet.univ.diff spec.region_measurable),
    hroute]
  exact hsplit

/-- Infinite routing plus the forever-survival remainder exhausts 1. -/
theorem exitRoutingInfinite_add_survivalForever_eq_one
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {y : JointState S X} (hy : y ∈ spec.region) :
    exitRoutingInfinite M spec y (Set.univ \ spec.region) +
      survivalForeverProbability M spec y = 1 := by
  let P := M.pathLaw (Measure.dirac y)
  have hstart : P ((fun w : ℕ → JointState S X => w 0) ⁻¹' spec.region) = 1 := by
    rw [← Measure.map_apply (measurable_pi_apply 0) spec.region_measurable]
    rw [StrategicWorldModel.pathLaw_eval_zero M (Measure.dirac y)]
    simp [hy]
  have hsplit :
      P (firstExitEverDestination spec Set.univ) +
        P (survivesForeverSet spec) = 1 := by
    rw [← measure_union (firstExitInfinite_partition_disjoint spec)
      (measurableSet_survivesForeverSet spec)]
    rw [firstExitInfinite_partition]
    exact hstart
  have hroute :
      firstExitEverDestination spec (Set.univ \ spec.region) =
        firstExitEverDestination spec Set.univ := by
    ext w
    simp [firstExitEverDestination, firstExitAtDestination]
  rw [exitRoutingInfinite_eq_prob_exit_in M spec hy
    (Set.univ \ spec.region)
      (MeasurableSet.univ.diff spec.region_measurable),
    hroute]
  exact hsplit

theorem exitRoutingInfiniteFromLaw_add_survivalForever_eq_one
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (hSupport : μ.toMeasure spec.region = 1) :
    exitRoutingInfiniteFromLaw M spec μ (Set.univ \ spec.region) +
      survivalForeverProbabilityFromLaw M spec μ = 1 := by
  let P := M.pathLaw μ.toMeasure
  have hstart :
      P ((fun w : ℕ → JointState S X => w 0) ⁻¹' spec.region) = 1 := by
    rw [← Measure.map_apply (measurable_pi_apply 0) spec.region_measurable]
    rw [StrategicWorldModel.pathLaw_eval_zero M μ.toMeasure]
    exact hSupport
  have hsplit :
      P (firstExitEverDestination spec Set.univ) +
        P (survivesForeverSet spec) = 1 := by
    rw [← measure_union (firstExitInfinite_partition_disjoint spec)
      (measurableSet_survivesForeverSet spec)]
    rw [firstExitInfinite_partition]
    exact hstart
  have hroute :
      firstExitEverDestination spec (Set.univ \ spec.region) =
        firstExitEverDestination spec Set.univ := by
    ext w
    simp [firstExitEverDestination, firstExitAtDestination]
  rw [exitRoutingInfiniteFromLaw_eq_prob_exit_in M spec μ hSupport
      (Set.univ \ spec.region)
      (MeasurableSet.univ.diff spec.region_measurable),
    hroute]
  exact hsplit

end PermanssonResearch.RegimeExit
