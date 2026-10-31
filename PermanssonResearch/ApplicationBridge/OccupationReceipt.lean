import PermanssonResearch.ApplicationBridge.ControlTableReceipt
import PermanssonResearch.ReverseSolver.CheckedRationalEventValue
import PermanssonResearch.ReverseSolver.RationalBSCCPartition
import PermanssonResearch.ReverseSolver.TypedStoppedClassSelection
import PermanssonResearch.ReverseSolver.C11TypedStationaryBridge
import PermanssonResearch.MultipleLimit.FiniteOccupationRandomLaw
import Mathlib.Tactic

/-!
# ApplicationBridge — finite joint-class occupation receipts

A joint-class receipt for one fixed rational Markov matrix lists its bottom
recurrent classes, an exact absorption weight per class and state, a
stationary law per class, and a per-state mean law (the absorption-weighted
mixture of the class laws).

The check is decidable and reuses the existing providers: C10's
`checkDirichlet` (exact class list and complete Dirichlet system) and C11's
`checkClassStationary` for each class law. Soundness:

* `checked_class_absorption_actual` / `checked_class_selection_weight` — every
  weight is the actual probability, under the infinite path law from that
  state, of eventually entering the class, equivalently of the canonical
  selected recurrent class being that class;
* `checked_random_limit_on_class` — on that event the actual almost-sure
  physical occupation limit (C2) is exactly the receipt's class law;
* `random_limit_law_eq_receipt` — the whole law of the random occupation limit
  is the Dirac mixture of the receipt's class laws with the receipt's weights.

The mean law is only the barycenter of that random law (`checked_mean_mixture`);
it is not the realized limit. GR/PR recovery and C10 original-margin
corollaries need the original specification, mode and invariance premises and
are not claimed here.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace PermanssonResearch.ApplicationBridge.OccupationReceipt

open PermanssonLean
open PermanssonResearch.ReverseSolver
open PermanssonResearch.ReverseSolver.C10
open PermanssonResearch.ReverseSolver.C11
open PermanssonResearch.ReverseSolver.FiniteStrategicRealization
open PermanssonResearch.MultipleLimit.FrozenObservedEvent
open PermanssonResearch.MultipleLimit.KernelCommunication
open PermanssonResearch.MultipleLimit.RecurrentClassDecomposition
open PermanssonResearch.MultipleLimit.CanonicalClassSelector
open PermanssonResearch.MultipleLimit.ClassStationarySelectionLaw
open PermanssonResearch.MultipleLimit.FiniteStateOccupation
open PermanssonResearch.MultipleLimit.FiniteOccupationRandomLaw

set_option autoImplicit false

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

variable {n : ℕ}

/-- The C11 stationary candidate carrying the receipt's law for class `C`. -/
def classCandidate (laws : Finset (Fin n) → Fin n → ℚ) (C : Finset (Fin n)) :
    ClassStationaryCandidate n :=
  ⟨C, laws C⟩

/-- Complete Dirichlet receipt (C10), one checked stationary law per listed
    class (C11), and the mean law as the absorption-weighted mixture. -/
def JointClassChecks (K : RationalMarkovMatrix n) (cert : DirichletCertificate n)
    (laws : Finset (Fin n) → Fin n → ℚ) (mean : Fin n → Fin n → ℚ) : Prop :=
  checkDirichlet K cert = true ∧
  (∀ C ∈ cert.classes, checkClassStationary K (classCandidate laws C) = true) ∧
  ∀ x y : Fin n, mean x y = ∑ C ∈ cert.classes, cert.weight C x * laws C y

instance (K : RationalMarkovMatrix n) (cert : DirichletCertificate n)
    (laws : Finset (Fin n) → Fin n → ℚ) (mean : Fin n → Fin n → ℚ) :
    Decidable (JointClassChecks K cert laws mean) := by
  unfold JointClassChecks
  infer_instance

/-- A false result means some class, weight, law or mean entry is wrong. -/
def checkJointClassReceipt (K : RationalMarkovMatrix n) (cert : DirichletCertificate n)
    (laws : Finset (Fin n) → Fin n → ℚ) (mean : Fin n → Fin n → ℚ) : Bool :=
  decide (JointClassChecks K cert laws mean)

theorem checkJointClassReceipt_sound (K : RationalMarkovMatrix n)
    (cert : DirichletCertificate n)
    (laws : Finset (Fin n) → Fin n → ℚ) (mean : Fin n → Fin n → ℚ)
    (h : checkJointClassReceipt K cert laws mean = true) :
    JointClassChecks K cert laws mean := by
  unfold checkJointClassReceipt at h
  exact of_decide_eq_true h

/-- The listed classes are exactly the computed bottom classes. -/
theorem checked_classes_exact (K : RationalMarkovMatrix n) (cert : DirichletCertificate n)
    (hc : checkDirichlet K cert = true) :
    cert.classes = bottomClasses K :=
  (checkDirichlet_sound K cert hc).1

theorem checked_class_stationary (K : RationalMarkovMatrix n)
    (cert : DirichletCertificate n)
    (laws : Finset (Fin n) → Fin n → ℚ) (mean : Fin n → Fin n → ℚ)
    (h : checkJointClassReceipt K cert laws mean = true)
    (C : Finset (Fin n)) (hC : C ∈ cert.classes) :
    checkClassStationary K (classCandidate laws C) = true :=
  (checkJointClassReceipt_sound K cert laws mean h).2.1 C hC

/-- Every listed law is strictly positive on its whole class. -/
theorem checked_law_positive_on_class (K : RationalMarkovMatrix n)
    (cert : DirichletCertificate n)
    (laws : Finset (Fin n) → Fin n → ℚ) (mean : Fin n → Fin n → ℚ)
    (h : checkJointClassReceipt K cert laws mean = true)
    (C : Finset (Fin n)) (hC : C ∈ cert.classes) (y : Fin n) (hy : y ∈ C) :
    0 < laws C y :=
  checked_stationary_positive_on_class K K (classCandidate laws C)
    (checked_class_stationary K cert laws mean h C hC) y hy

/-- For a listed class, the eventual-entry value is that class's own weight:
    distinct bottom classes are disjoint and nonempty. -/
theorem eventValue_class (K : RationalMarkovMatrix n) (cert : DirichletCertificate n)
    (hc : checkDirichlet K cert = true) (C : Finset (Fin n)) (hC : C ∈ cert.classes)
    (x : Fin n) :
    eventValue cert (fun z => decide (z ∈ C)) x = cert.weight C x := by
  have hclasses := checked_classes_exact K cert hc
  have hfilter : cert.classes.filter (GoodClass (fun z => decide (z ∈ C))) = {C} := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_singleton, goodClass_iff, decide_eq_true_eq]
    constructor
    · rintro ⟨hD, hsub⟩
      have hDb : D ∈ bottomClasses K := hclasses ▸ hD
      have hCb : C ∈ bottomClasses K := hclasses ▸ hC
      obtain ⟨z, hz⟩ := (Finset.mem_filter.mp hDb).2.1
      exact bottomClasses_common_member_eq K D C hDb hCb z hz (hsub z hz)
    · rintro rfl
      exact ⟨hC, fun z hz => hz⟩
  unfold eventValue
  rw [hfilter, Finset.sum_singleton]

/-- Every checked weight is the actual probability of eventually entering
    that bottom class under the infinite path law from `x`. -/
theorem checked_class_absorption_actual [NeZero n] (K : RationalMarkovMatrix n)
    (cert : DirichletCertificate n) (hc : checkDirichlet K cert = true)
    (C : Finset (Fin n)) (hC : C ∈ cert.classes) (x : Fin n) :
    ((realizedModel K).pathLaw (Measure.dirac (decode x))).real
      (eventuallyObserved (fun y => decide (encode y ∈ C)) true) =
      (cert.weight C x : ℝ) := by
  have key := checked_eventValue_eq_actual_path K cert hc (fun z => decide (z ∈ C)) x
  rw [eventValue_class K cert hc C hC x] at key
  exact key

/-- Every checked weight is the actual probability that the canonical
    selected recurrent class is that class. -/
theorem checked_class_selection_weight [NeZero n] (K : RationalMarkovMatrix n)
    (cert : DirichletCertificate n) (hc : checkDirichlet K cert = true)
    (C : Finset (Fin n)) (hC : C ∈ cert.classes) (x : Fin n) :
    ((realizedModel K).pathLaw (Measure.dirac (decode x))).real
      ((selectedRepresentative (realizedModel K).inducedKernel) ⁻¹' decodedClass C) =
      (cert.weight C x : ℝ) := by
  have hb : C ∈ bottomClasses K := checked_classes_exact K cert hc ▸ hC
  rw [checked_class_column_unique K cert (referenceDirichletCertificate K) hc
    (referenceDirichlet_check_true K) C hb x]
  exact (cramerWeight_eq_canonical_selected_class K C hb x).symm

/-- On the event that the canonical selected class is a bottom class `C`,
    the actual physical occupation limit is C2's stationary law of `C`. -/
theorem physicalLimit_eq_of_selected [NeZero n] (K : RationalMarkovMatrix n)
    (C : Finset (Fin n)) (hb : C ∈ bottomClasses K) (w : ℕ → JointState Unit (Fin n))
    (hw : selectedRepresentative (realizedModel K).inducedKernel w ∈ decodedClass C) :
    physicalOccupationLimit (realizedModel K).inducedKernel w =
      stationaryForSet (realizedModel K).inducedKernel (decodedClass C) := by
  let T := (realizedModel K).inducedKernel
  have hNative : decodedClass C ∈ RecurrentClasses T :=
    (bottomClasses_native_iff K K C).mp hb
  obtain ⟨i, _, hi⟩ := (recurrentClasses_mem_iff T _).mp hNative
  have hmem : selectedRepresentative T w ∈ CommunicatingClass T i := hi ▸ hw
  have hclass : CommunicatingClass T (selectedRepresentative T w) = decodedClass C :=
    (communicatingClass_eq_of_common T (mem_communicatingClass T _) hmem).trans hi
  unfold physicalOccupationLimit
  rw [hclass]

/-- On the event that the selected class is a listed class, the actual
    almost-sure occupation limit is the receipt's own class law. -/
theorem checked_random_limit_on_class [NeZero n] (K : RationalMarkovMatrix n)
    (cert : DirichletCertificate n)
    (laws : Finset (Fin n) → Fin n → ℚ) (mean : Fin n → Fin n → ℚ)
    (h : checkJointClassReceipt K cert laws mean = true)
    (C : Finset (Fin n)) (hC : C ∈ cert.classes) (w : ℕ → JointState Unit (Fin n))
    (hw : selectedRepresentative (realizedModel K).inducedKernel w ∈ decodedClass C) :
    physicalOccupationLimit (realizedModel K).inducedKernel w =
      certifiedProbability K (classCandidate laws C)
        (checked_class_stationary K cert laws mean h C hC) := by
  have hc := (checkJointClassReceipt_sound K cert laws mean h).1
  have hb : C ∈ bottomClasses K := checked_classes_exact K cert hc ▸ hC
  rw [physicalLimit_eq_of_selected K C hb w hw]
  exact (checked_stationary_eq_native K K (classCandidate laws C)
    (checked_class_stationary K cert laws mean h C hC)).symm

/-- The empirical occupation converges almost surely to the physical
    limit from every start (C2; no irreducibility or aperiodicity). -/
theorem occupation_ae_limit [NeZero n] (K : RationalMarkovMatrix n) (x : Fin n) :
    ∀ᵐ w ∂(realizedModel K).pathLaw (Measure.dirac (decode x)),
      Tendsto (fun t : ℕ => empiricalOccupation w (t + 1) (Nat.succ_pos t)) atTop
        (𝓝 (physicalOccupationLimit (realizedModel K).inducedKernel w)) :=
  physicalOccupationLimit_ae_correct _ (diracProba (decode x))

/-- The whole law of the actual random occupation limit from `x` is the
    Dirac mixture of the receipt's class laws with the receipt's weights. -/
theorem random_limit_law_eq_receipt [NeZero n] (K : RationalMarkovMatrix n)
    (cert : DirichletCertificate n)
    (laws : Finset (Fin n) → Fin n → ℚ) (mean : Fin n → Fin n → ℚ)
    (h : checkJointClassReceipt K cert laws mean = true) (x : Fin n) :
    ((realizedModel K).pathLaw (Measure.dirac (decode x))).map
        (physicalOccupationLimit (realizedModel K).inducedKernel) =
      ∑ C ∈ cert.classes.attach,
        ENNReal.ofReal (cert.weight C.1 x : ℝ) •
          Measure.dirac (certifiedProbability K (classCandidate laws C.1)
            (checked_class_stationary K cert laws mean h C.1 C.2)) := by
  classical
  have hc := (checkJointClassReceipt_sound K cert laws mean h).1
  have hclasses := checked_classes_exact K cert hc
  let T := (realizedModel K).inducedKernel
  let P := (realizedModel K).pathLaw (Measure.dirac (decode x))
  let E : Finset (Fin n) → Set (ℕ → JointState Unit (Fin n)) :=
    fun C => (selectedRepresentative T) ⁻¹' decodedClass C
  have hEm : ∀ C, MeasurableSet (E C) := fun C =>
    (Set.toFinite _).measurableSet.preimage (selectedRepresentative_measurable T)
  have hcover : ∀ w, ∃ C ∈ cert.classes, w ∈ E C := by
    intro w
    let y := selectedRepresentative T w
    refine ⟨component K (encode y), ?_, ?_⟩
    · have hrec : IsRecurrentState T (decode (encode y)) := by
        rw [decode_encode]
        exact selectedRepresentative_recurrent T w
      rw [hclasses]
      exact (bottom_component_iff_native_recurrent K K (encode y)).mpr hrec
    · show encode y ∈ component K (encode y)
      exact (component_native_iff K K (encode y) (encode y)).mpr
        (mem_communicatingClass _ _)
  have hdisj : ∀ C ∈ cert.classes, ∀ D ∈ cert.classes, C ≠ D → Disjoint (E C) (E D) := by
    intro C hC D hD hne
    rw [Set.disjoint_left]
    intro w hwC hwD
    have hCb : C ∈ bottomClasses K := hclasses ▸ hC
    have hDb : D ∈ bottomClasses K := hclasses ▸ hD
    exact hne (bottomClasses_common_member_eq K C D hCb hDb _ hwC hwD)
  have hweight : ∀ C ∈ cert.classes, P (E C) = ENNReal.ofReal (cert.weight C x : ℝ) := by
    intro C hC
    rw [← checked_class_selection_weight K cert hc C hC x]
    exact (ENNReal.ofReal_toReal (measure_ne_top P (E C))).symm
  ext S hS
  rw [Measure.map_apply (physicalOccupationLimit_measurable T) hS,
    Measure.coe_finsetSum, Finset.sum_apply]
  have hsplit : P (physicalOccupationLimit T ⁻¹' S) =
      ∑ C ∈ cert.classes, P (physicalOccupationLimit T ⁻¹' S ∩ E C) := by
    have hU : physicalOccupationLimit T ⁻¹' S =
        ⋃ C ∈ cert.classes, (physicalOccupationLimit T ⁻¹' S ∩ E C) := by
      ext w
      simp only [Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
      constructor
      · intro hw
        obtain ⟨C, hC, hwC⟩ := hcover w
        exact ⟨C, hC, hw, hwC⟩
      · rintro ⟨C, -, hw, -⟩
        exact hw
    conv_lhs => rw [hU]
    apply measure_biUnion_finset
    · intro C hC D hD hne
      exact (hdisj C hC D hD hne).mono Set.inter_subset_right Set.inter_subset_right
    · intro C _
      exact ((physicalOccupationLimit_measurable T) hS).inter (hEm C)
  rw [hsplit, ← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro C _
  rw [Measure.smul_apply, Measure.dirac_apply' _ hS, smul_eq_mul, ← hweight C.1 C.2]
  by_cases hπ : certifiedProbability K (classCandidate laws C.1)
      (checked_class_stationary K cert laws mean h C.1 C.2) ∈ S
  · have hset : physicalOccupationLimit T ⁻¹' S ∩ E C.1 = E C.1 := by
      apply Set.inter_eq_right.mpr
      intro w hw
      show physicalOccupationLimit T w ∈ S
      rw [checked_random_limit_on_class K cert laws mean h C.1 C.2 w hw]
      exact hπ
    rw [hset]
    simp [hπ]
  · have hset : physicalOccupationLimit T ⁻¹' S ∩ E C.1 = ∅ := by
      ext w
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_empty_iff_false, iff_false,
        not_and]
      intro hwS hw
      rw [checked_random_limit_on_class K cert laws mean h C.1 C.2 w hw] at hwS
      exact hπ hwS
    rw [hset]
    simp [hπ]

/-- The checked mean law is only the barycenter of that random law: the
    mixture of class laws weighted by actual eventual-entry probabilities. -/
theorem checked_mean_mixture [NeZero n] (K : RationalMarkovMatrix n)
    (cert : DirichletCertificate n)
    (laws : Finset (Fin n) → Fin n → ℚ) (mean : Fin n → Fin n → ℚ)
    (h : checkJointClassReceipt K cert laws mean = true) (x y : Fin n) :
    (mean x y : ℝ) = ∑ C ∈ bottomClasses K,
      ((realizedModel K).pathLaw (Measure.dirac (decode x))).real
        (eventuallyObserved (fun z => decide (encode z ∈ C)) true) * (laws C y : ℝ) := by
  obtain ⟨hc, -, hmean⟩ := checkJointClassReceipt_sound K cert laws mean h
  rw [hmean x y, ← checked_classes_exact K cert hc]
  push_cast
  apply Finset.sum_congr rfl
  intro C hC
  rw [checked_class_absorption_actual K cert hc C hC x]

end PermanssonResearch.ApplicationBridge.OccupationReceipt
