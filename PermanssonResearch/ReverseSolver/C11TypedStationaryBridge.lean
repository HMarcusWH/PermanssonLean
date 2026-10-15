import PermanssonResearch.ReverseSolver.C11StationaryFamily
import PermanssonResearch.ReverseSolver.RationalBSCCNative
import PermanssonResearch.MultipleLimit.FiniteClassInvariantMeasure
import PermanssonResearch.MultipleLimit.ClassStationarySelectionLaw
import Mathlib.Tactic

/-!
# C11-A — exact rational stationary vectors are genuine typed class measures

Use the actual alpha/P/U induced kernel of the constructed D0 family,
not an arbitrary externally specified strategic world. Every listed
candidate's matrix may differ from the baseline matrix. The proof
transports the exact rational equations through singleton atoms and
identifies the ENTIRE probability measure using C2's unique class law.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace C11

set_option autoImplicit false

open PermanssonLean
open FiniteStrategicRealization
open C10
open PermanssonResearch.MultipleLimit.FiniteKernelRealBridge
open PermanssonResearch.MultipleLimit.FiniteCesaroAlgebra
open PermanssonResearch.MultipleLimit.FiniteInvariantMeasureTransport
open PermanssonResearch.MultipleLimit.FiniteClassInvariantMeasure
open PermanssonResearch.MultipleLimit.FiniteClosedSupport
open PermanssonResearch.MultipleLimit.FiniteClassInvariantUniqueness
open PermanssonResearch.MultipleLimit.KernelCommunication
open PermanssonResearch.MultipleLimit.RecurrentClassDecomposition
open PermanssonResearch.MultipleLimit.ClassStationarySelectionLaw

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

def realWeights {n : ℕ} (r : ClassStationaryCandidate n)
    (y : JointState Unit (Fin n)) : ℝ :=
  (r.weights (encode y) : ℝ)

/-- Genuine typed singleton transition = exact rational entry. -/
theorem typed_realTransition_eq {n : ℕ}
    (L : RationalMarkovMatrix n) (x z : Fin n) :
    realTransition (realizedModel L).inducedKernel (decode x) (decode z) =
      (L.entry x z : ℝ) := by
  have hs : (encode ⁻¹' ({z} : Set (Fin n))) =
      ({decode z} : Set (JointState Unit (Fin n))) := by
    ext y
    rcases y with ⟨u, j⟩
    cases u
    simp [encode, decode]
  change ((realizedModel L).inducedKernel (decode x)
    ({decode z} : Set (JointState Unit (Fin n)))).toReal = _
  rw [← hs, inducedKernel_encodedEntry]
  exact ENNReal.toReal_ofReal (show 0 ≤ (L.entry x z : ℝ) by
    exact_mod_cast L.entry_nonneg x z)

theorem realWeights_nonneg {n : ℕ}
    (L : RationalMarkovMatrix n) (r : ClassStationaryCandidate n)
    (hc : checkClassStationary L r = true) :
    ∀ y : JointState Unit (Fin n), 0 ≤ realWeights r y := by
  intro y
  change 0 ≤ ((r.weights (encode y) : ℚ) : ℝ)
  exact_mod_cast checked_nonnegative L r hc (encode y)

theorem realWeights_total {n : ℕ}
    (L : RationalMarkovMatrix n) (r : ClassStationaryCandidate n)
    (hc : checkClassStationary L r = true) :
    (∑ y : JointState Unit (Fin n), realWeights r y) = 1 := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]
  change (∑ x : Fin n, ((r.weights x : ℚ) : ℝ)) = 1
  exact_mod_cast checked_normalized L r hc

theorem realWeights_stationary {n : ℕ}
    (L : RationalMarkovMatrix n) (r : ClassStationaryCandidate n)
    (hc : checkClassStationary L r = true) :
    ∀ y : JointState Unit (Fin n),
      pushVector (realTransition (realizedModel L).inducedKernel)
        (realWeights r) y = realWeights r y := by
  intro y
  rcases y with ⟨u, j⟩
  cases u
  unfold pushVector
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]
  change (∑ i : Fin n,
    ((r.weights i : ℚ) : ℝ) *
      realTransition (realizedModel L).inducedKernel
        (decode i) (decode j)) = ((r.weights j : ℚ) : ℝ)
  simp_rw [typed_realTransition_eq L]
  exact_mod_cast (checked_balance L r hc j).symm

theorem realWeights_supported {n : ℕ}
    (L : RationalMarkovMatrix n) (r : ClassStationaryCandidate n)
    (hc : checkClassStationary L r = true) :
    IsSupportedReal (realWeights r) (decodedClass r.classStates) := by
  intro y hy
  have hOutside : encode y ∉ r.classStates := by
    simpa only [decodedClass, Set.mem_setOf_eq] using hy
  change ((r.weights (encode y) : ℚ) : ℝ) = 0
  exact_mod_cast checked_supported L r hc (encode y) hOutside

noncomputable def certifiedProbability {n : ℕ}
    (L : RationalMarkovMatrix n) (r : ClassStationaryCandidate n)
    (hc : checkClassStationary L r = true) :
    ProbabilityMeasure (JointState Unit (Fin n)) :=
  ⟨vectorMeasure (realWeights r),
   vectorMeasure_isProbability (realWeights r)
     (realWeights_nonneg L r hc) (realWeights_total L r hc)⟩

theorem certifiedProbability_invariant {n : ℕ}
    (L : RationalMarkovMatrix n) (r : ClassStationaryCandidate n)
    (hc : checkClassStationary L r = true) :
    Kernel.Invariant (realizedModel L).inducedKernel
      (certifiedProbability L r hc).toMeasure := by
  exact vectorMeasure_invariant (realizedModel L).inducedKernel
    (realWeights r) (realWeights_nonneg L r hc)
    (realWeights_stationary L r hc)

theorem certifiedProbability_class_mass_one {n : ℕ}
    (L : RationalMarkovMatrix n) (r : ClassStationaryCandidate n)
    (hc : checkClassStationary L r = true) :
    (certifiedProbability L r hc).toMeasure
      (decodedClass r.classStates) = 1 := by
  change (vectorMeasure (realWeights r)) (decodedClass r.classStates) = 1
  exact vectorMeasure_mass_one_of_support (realWeights r)
    (realWeights_nonneg L r hc) (realWeights_total L r hc)
    (decodedClass r.classStates) (realWeights_supported L r hc)

/-- Whole-measure equality to C2's unique genuine class-supported measure,
for ANY matrix L applied as an actual typed intervention from baseline K₀. -/
theorem checked_stationary_eq_native {n : ℕ} [NeZero n]
    (K₀ L : RationalMarkovMatrix n)
    (r : ClassStationaryCandidate n)
    (hc : checkClassStationary L r = true) :
    certifiedProbability L r hc =
      stationaryForSet
        (rationalStrategicIntervention K₀ L).intervention.apply.inducedKernel
        (decodedClass r.classStates) := by
  let T := (rationalStrategicIntervention K₀ L).intervention.apply.inducedKernel
  have hClass : decodedClass r.classStates ∈ RecurrentClasses T :=
    (bottomClasses_native_iff K₀ L r.classStates).mp
      (checkClassStationary_sound L r hc).2.1
  have hCert : Kernel.Invariant T (certifiedProbability L r hc).toMeasure ∧
      (certifiedProbability L r hc).toMeasure
        (decodedClass r.classStates) = 1 := by
    constructor
    · simpa only [T, rationalStrategicIntervention_applied] using
        certifiedProbability_invariant L r hc
    · exact certifiedProbability_class_mass_one L r hc
  obtain ⟨π, hπ, unique⟩ :=
    exists_unique_stationary_probability_on_class T
      (decodedClass r.classStates) hClass
  calc
    certifiedProbability L r hc = π := unique _ hCert
    _ = stationaryForSet T (decodedClass r.classStates) := by
      symm
      exact unique _ (stationaryForSet_spec T hClass)

/-- Strictly positive rational mass on every vertex of its irreducible
bottom class; not a separate unproved full-support axiom. -/
theorem checked_stationary_positive_on_class {n : ℕ}
    (K₀ L : RationalMarkovMatrix n)
    (r : ClassStationaryCandidate n)
    (hc : checkClassStationary L r = true)
    (x : Fin n) (hx : x ∈ r.classStates) :
    0 < r.weights x := by
  -- C2's strict class-support lemma requires an actual nonempty
  -- physical state type. The accepted exact certificate supplies it;
  -- no implicit nonemptiness assumption is introduced for Fin 0.
  letI : Nonempty (JointState Unit (Fin n)) :=
    ⟨((), ⟨0, (checkClassStationary_sound L r hc).1⟩)⟩
  let T := (rationalStrategicIntervention K₀ L).intervention.apply.inducedKernel
  have hClass : decodedClass r.classStates ∈ RecurrentClasses T :=
    (bottomClasses_native_iff K₀ L r.classStates).mp
      (checkClassStationary_sound L r hc).2.1
  obtain ⟨c, _, hclass⟩ := (recurrentClasses_mem_iff T _).mp hClass
  have hcomm : ∀ i ∈ decodedClass r.classStates,
      ∀ j ∈ decodedClass r.classStates,
        PermanssonResearch.MultipleLimit.FiniteInvariantUniqueness.Reachable
          (realTransition T) i j := by
    rw [← hclass]
    exact class_real_irreducible T c
  have hstationary : ∀ y,
      pushVector (realTransition T) (realWeights r) y = realWeights r y := by
    simpa only [T, rationalStrategicIntervention_applied] using
      realWeights_stationary L r hc
  have hpos := strictly_positive_on_class (realTransition T)
    (realTransition_nonneg T) (decodedClass r.classStates) hcomm
    (realWeights r)
    (realWeights_nonneg L r hc) (realWeights_total L r hc)
    hstationary (realWeights_supported L r hc)
    (decode x)
    (show decode x ∈ decodedClass r.classStates by
      simpa [decodedClass] using hx)
  change (0 : ℝ) < ((r.weights x : ℚ) : ℝ) at hpos
  exact_mod_cast hpos

end C11
end ReverseSolver
end PermanssonResearch
