import PermanssonResearch.MultipleLimit.FiniteExactGRObstruction
import PermanssonResearch.MultipleLimit.ExactSixStateClassLaws
import PermanssonResearch.MultipleLimit.ExactSixStateObservedGR
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Instances.Discrete
import Mathlib.Tactic

/-!
# C54-05 — genuine typed six-state Exact GR classification witnesses

The same six-state alpha/P/U model and frozen proper region yield:
* positive original Boolean-observed Exact GR, despite two distinct
  physical recurrent-class stationary probability laws;
* an identity-observed obstruction under EVERY fixed target.

The canonical representatives are Classical.choose values, NOT
definitionally a0/b0. We prove singleton-representative event
identities before transporting the genuine 1/3 and 2/3 class weights.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactSixStateC3Witness

open PermanssonLean
open PermanssonLean.RegimeSpecification
open ReverseSolver.FiniteStrategicRealization
open ExactSixState
open ExactSixStateTyped
open ExactSixStateKernelRegion
open ExactSixStateRecurrentGeometry
open ExactSixStateObservedGR
open ExactSixStateClassSelectionWeights
open ExactSixStateClassLaws
open CanonicalClassSelector
open KernelCommunication
open RecurrentClassDecomposition
open BasinFamily
open FiniteCanonicalPath
open FiniteExactGRRecovery
open FiniteExactGRCharacterization
open FiniteExactGRObstruction
open ClassDescriptorSelectionLaw

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

abbrev SixY := JointState Unit (Fin 6)
private noncomputable abbrev K := typedModel.inducedKernel

/-- True canonical class representatives; neither is assumed to
equal any particular physical state in its communicating class. -/
def rA : SixY := classRepresentative K (decode (2 : Fin 6))
def rB : SixY := classRepresentative K (decode (4 : Fin 6))

theorem rA_mem_A : rA ∈ classASet := by
  change classRepresentative K (decode (2 : Fin 6)) ∈ classASet
  rw [classASet_eq_commClass]
  exact classRepresentative_mem K _

theorem rB_mem_B : rB ∈ classBSet := by
  change classRepresentative K (decode (4 : Fin 6)) ∈ classBSet
  rw [classBSet_eq_commClass]
  exact classRepresentative_mem K _

theorem rA_ne_rB : rA ≠ rB := by
  intro h
  have hmemA : rB ∈ classASet := h ▸ rA_mem_A
  exact Set.disjoint_left.mp classASet_disjoint_classBSet hmemA rB_mem_B

theorem selected_eq_rA_iff_A (w : ℕ → SixY) :
    selectedRepresentative K w = rA ↔
      selectedRepresentative K w ∈ classASet := by
  constructor
  · intro h
    rw [h]
    exact rA_mem_A
  · intro hw
    rw [classASet_eq_commClass] at hw
    have hrep := classRepresentative_eq_of_communicates K hw
    have hfix := selectedRepresentative_fixed K w
    change selectedRepresentative K w = classRepresentative K (decode (2 : Fin 6))
    exact (hrep.trans hfix).symm

theorem selected_eq_rB_iff_B (w : ℕ → SixY) :
    selectedRepresentative K w = rB ↔
      selectedRepresentative K w ∈ classBSet := by
  constructor
  · intro h
    rw [h]
    exact rB_mem_B
  · intro hw
    rw [classBSet_eq_commClass] at hw
    have hrep := classRepresentative_eq_of_communicates K hw
    have hfix := selectedRepresentative_fixed K w
    change selectedRepresentative K w = classRepresentative K (decode (4 : Fin 6))
    exact (hrep.trans hfix).symm

/-- Actual canonical singleton representative A event has exactly the
previously established whole-A class selection probability. -/
theorem canonical_rA_weight_u :
    canonicalPathLaw K (Measure.dirac (decode (1 : Fin 6)))
      ((selectedRepresentative K) ⁻¹' ({rA} : Set SixY)) =
        ENNReal.ofReal (1/3 : ℝ) := by
  have hEvent :
      (selectedRepresentative K) ⁻¹' ({rA} : Set SixY) =
        (selectedRepresentative K) ⁻¹' classASet := by
    ext w
    exact selected_eq_rA_iff_A w
  rw [hEvent]
  change typedModel.pathLaw (Measure.dirac (decode (1 : Fin 6)))
    ((selectedRepresentative K) ⁻¹' classASet) = _
  exact selected_A_weight_u

theorem canonical_rB_weight_u :
    canonicalPathLaw K (Measure.dirac (decode (1 : Fin 6)))
      ((selectedRepresentative K) ⁻¹' ({rB} : Set SixY)) =
        ENNReal.ofReal (2/3 : ℝ) := by
  have hEvent :
      (selectedRepresentative K) ⁻¹' ({rB} : Set SixY) =
        (selectedRepresentative K) ⁻¹' classBSet := by
    ext w
    exact selected_eq_rB_iff_B w
  rw [hEvent]
  change typedModel.pathLaw (Measure.dirac (decode (1 : Fin 6)))
    ((selectedRepresentative K) ⁻¹' classBSet) = _
  exact selected_B_weight_u

private theorem rA_recurrent : (decode (2 : Fin 6)) ∈ RecurrentStates K := by
  change ClosedSubset K (CommunicatingClass K (decode (2 : Fin 6)))
  rw [← classASet_eq_commClass]
  exact classASet_closed

private theorem rB_recurrent : (decode (4 : Fin 6)) ∈ RecurrentStates K := by
  change ClosedSubset K (CommunicatingClass K (decode (4 : Fin 6)))
  rw [← classBSet_eq_commClass]
  exact classBSet_closed

theorem rA_representative : rA ∈ recurrentRepresentatives K := by
  classical
  change classRepresentative K (decode (2 : Fin 6)) ∈
    (Finset.univ.filter (fun i =>
      i ∈ RecurrentStates K ∧ classRepresentative K i = i))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨classRepresentative_recurrent K rA_recurrent,
    classRepresentative_idempotent K (decode (2 : Fin 6))⟩

theorem rB_representative : rB ∈ recurrentRepresentatives K := by
  classical
  change classRepresentative K (decode (4 : Fin 6)) ∈
    (Finset.univ.filter (fun i =>
      i ∈ RecurrentStates K ∧ classRepresentative K i = i))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨classRepresentative_recurrent K rB_recurrent,
    classRepresentative_idempotent K (decode (4 : Fin 6))⟩

/-- Any frozen basin admitting u reaches both genuine classes with
strictly positive probability. H and the descriptor may differ. -/
theorem representatives_reachable_from_u
    {H : Type*} [MeasurableSpace H]
    (F : FrozenBasinFamily K H)
    (hu : decode (1 : Fin 6) ∈ F.basin) :
    rA ∈ reachableRepresentatives K H F ∧
      rB ∈ reachableRepresentatives K H F := by
  classical
  constructor
  · change rA ∈ (recurrentRepresentatives K).filter
      (fun i => ∃ y ∈ F.basin,
        canonicalPathLaw K (Measure.dirac y)
          ((selectedRepresentative K) ⁻¹' {i}) ≠ 0)
    apply Finset.mem_filter.mpr
    refine ⟨rA_representative, decode (1 : Fin 6), hu, ?_⟩
    rw [canonical_rA_weight_u]
    norm_num
  · change rB ∈ (recurrentRepresentatives K).filter
      (fun i => ∃ y ∈ F.basin,
        canonicalPathLaw K (Measure.dirac y)
          ((selectedRepresentative K) ⁻¹' {i}) ≠ 0)
    apply Finset.mem_filter.mpr
    refine ⟨rB_representative, decode (1 : Fin 6), hu, ?_⟩
    rw [canonical_rB_weight_u]
    norm_num

/-- C3's *necessity* direction recovers the original common Boolean
target from the previously proved positive Exact GR witness. -/
theorem boolean_common_target_via_C3 :
    ∀ i ∈ reachableRepresentatives K Bool
      (frozenFamilyOfExactSpec typedModel observedSpec observedReference
        observedAssumption41 observedExactlyInvariant),
      observedStationaryForClass K observedDescriptor i =
        diracProba true := by
  exact (exactGR_iff_common_reachable_target
    typedModel observedSpec observedReference
    observedAssumption41 observedExactlyInvariant rfl).mp
      observedExactGeneratedRegime

/-- Same actual typed model, original proper region and two-point basin.
Only the frozen descriptor and target are changed. -/
def identitySpec (ν : ProbabilityMeasure SixY) :
    RegimeSpecification SixY SixY where
  region := typedRegion
  region_measurable := typed_region_measurable
  basin := observedBasin
  basin_measurable := (Set.toFinite observedBasin).measurableSet
  basin_subset_region := observedBasin_subset_region
  descriptor := id
  descriptor_measurable := measurable_id
  target := ν
  convergenceMode := ConvergenceMode.almostSureWeak SixY SixY

theorem identityAssumption41 (ν : ProbabilityMeasure SixY) :
    Assumption41 typedModel (identitySpec ν) observedReference := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact observedAssumption41.1
  · exact observedAssumption41.2.1
  · refine ⟨decode (1 : Fin 6), ?_, decode (2 : Fin 6), ?_, ?_⟩
    · simp [identitySpec, typedRegion, ExactSixStateRegion.region,
        decode, encode]
    · simp [identitySpec, typedRegion, ExactSixStateRegion.region,
        decode, encode]
    · decide
  · exact observedAssumption41.2.2.2

theorem identityExactlyInvariant (ν : ProbabilityMeasure SixY) :
    IsExactlyInvariant typedModel (identitySpec ν) :=
  observedExactlyInvariant

private theorem representative_A_class :
    CommunicatingClass K rA = classASet := by
  have hmem := rA_mem_A
  rw [classASet_eq_commClass] at hmem
  exact (communicatingClass_eq_of_communicates K hmem).symm.trans
    classASet_eq_commClass.symm

private theorem representative_B_class :
    CommunicatingClass K rB = classBSet := by
  have hmem := rB_mem_B
  rw [classBSet_eq_commClass] at hmem
  exact (communicatingClass_eq_of_communicates K hmem).symm.trans
    classBSet_eq_commClass.symm

theorem identity_observed_A (ν : ProbabilityMeasure SixY) :
    observedStationaryForClass K (identitySpec ν).descriptor rA = πA := by
  change (ClassStationarySelectionLaw.stationaryForSet K
    (CommunicatingClass K rA)).map id = πA
  rw [representative_A_class]
  change πA.map (id : SixY → SixY) = πA
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (id : SixY → SixY) πA.toMeasure = πA.toMeasure
  exact Measure.map_id _

theorem identity_observed_B (ν : ProbabilityMeasure SixY) :
    observedStationaryForClass K (identitySpec ν).descriptor rB = πB := by
  change (ClassStationarySelectionLaw.stationaryForSet K
    (CommunicatingClass K rB)).map id = πB
  rw [representative_B_class]
  change πB.map (id : SixY → SixY) = πB
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (id : SixY → SixY) πB.toMeasure = πB
  exact Measure.map_id _

theorem identity_observed_classes_distinct (ν : ProbabilityMeasure SixY) :
    observedStationaryForClass K (identitySpec ν).descriptor rA ≠
      observedStationaryForClass K (identitySpec ν).descriptor rB := by
  rw [identity_observed_A, identity_observed_B]
  exact πA_ne_πB

theorem identity_classes_reachable (ν : ProbabilityMeasure SixY) :
    let F := frozenFamilyOfExactSpec typedModel (identitySpec ν)
      observedReference (identityAssumption41 ν) (identityExactlyInvariant ν)
    rA ∈ reachableRepresentatives K SixY F ∧
      rB ∈ reachableRepresentatives K SixY F := by
  dsimp
  apply representatives_reachable_from_u
  simp [frozenFamilyOfExactSpec, identitySpec, observedBasin]

/-- In the actual typed alpha/P/U six-state model the noncollapsed
identity descriptor rules out Exact GR for *every* frozen target. -/
theorem identity_no_exactGR_for_any_target (ν : ProbabilityMeasure SixY) :
    ¬ IsExactGeneratedRegime typedModel (identitySpec ν)
      observedReference := by
  obtain ⟨hA, hB⟩ := identity_classes_reachable ν
  have hnot := no_exactGR_for_any_target_of_incompatible_classes
    typedModel (identitySpec ν) observedReference
    (identityAssumption41 ν) (identityExactlyInvariant ν) rfl
    rA rB hA hB (identity_observed_classes_distinct ν)
  have hν := hnot ν
  change ¬ IsExactGeneratedRegime typedModel (identitySpec ν)
    observedReference at hν
  exact hν

end
end ExactSixStateC3Witness
end MultipleLimit
end PermanssonResearch
