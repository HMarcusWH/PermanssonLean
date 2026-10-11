import PermanssonResearch.MultipleLimit.FiniteKernelInvariantUniqueness
import PermanssonResearch.MultipleLimit.FiniteClassInvariantExistence
import PermanssonResearch.MultipleLimit.RecurrentClassDecomposition
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Tactic

/-!
# Lane C2 — TRUE class-supported stationary probability measures

Combines:
(1) a generic irrational-capable Markov kernel's exact real atom matrix,
(2) stationary existence via redirect-outside-class and finite Cesaro compactness,
(3) class-supported real minimum-ratio uniqueness, and
(4) exact real-vector-to-ENNReal probability measure transport.

For every closed recurrent communicating class C of a nonempty finite
Markov kernel, the theorem constructs exactly one actual ProbabilityMeasure
π whose whole measure is K-invariant and whose mass on C is one.

No aperiodicity, rationality, assumed stationary law or iid assumption.
A.s. EMPIRICAL OCCUPATION convergence remains a separate task.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteClassInvariantMeasure

open KernelCommunication
open RecurrentClassDecomposition
open FiniteKernelRealBridge
open FiniteKernelInvariantUniqueness
open FiniteInvariantMeasureTransport
open FiniteCesaroAlgebra
open FiniteClosedSupport
open FiniteClassInvariantExistence
open FiniteClassInvariantUniqueness

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- A graph-closed set is closed in exact real singleton masses. -/
theorem kernelClosed_to_realClosed
    (C : Set Y) (hC : ClosedSubset K C) :
    IsClosedReal (realTransition K) C := by
  intro i hi j hj
  have hnot : ¬PositiveEdge K i j := by
    intro hp
    exact hj (hC i hi j hp)
  have hzero : K i ({j} : Set Y) = 0 :=
    le_antisymm (not_lt.mp hnot) bot_le
  simp [realTransition, hzero]

/-- In one communicating class, positive REAL matrix edges
connect every pair of class members. -/
theorem class_real_irreducible (c : Y) :
    ∀ i ∈ CommunicatingClass K c,
      ∀ j ∈ CommunicatingClass K c,
        FiniteInvariantUniqueness.Reachable
          (realTransition K) i j := by
  intro i hi j hj
  have hij : KernelCommunication.Reachable K i j :=
    (communicates_trans K (communicates_symm K hi) hj).1
  exact reachable_real_of_kernel K hij

/-- Genuine recurrent-class support of an EXACT real invariant
vector after converting it to the original measure space. -/
theorem vectorMeasure_mass_one_of_support
    (v : Y → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hvtotal : (∑ i : Y, v i) = 1)
    (C : Set Y) (hsupp : IsSupportedReal v C) :
    (vectorMeasure v) C = 1 := by
  classical
  letI : IsProbabilityMeasure (vectorMeasure v) :=
    vectorMeasure_isProbability v hv hvtotal
  let s : Finset Y := Finset.univ.filter (fun i => i ∉ C)
  have hs : (↑s : Set Y) = Cᶜ := by
    ext i
    simp [s]
  have hcomplement : (vectorMeasure v) Cᶜ = 0 := by
    calc
      (vectorMeasure v) Cᶜ =
          (vectorMeasure v) (↑s : Set Y) :=
        congrArg (vectorMeasure v) hs.symm
      _ = ∑ i ∈ s, (vectorMeasure v) ({i} : Set Y) :=
        (sum_measure_singleton).symm
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hout : i ∉ C := by simpa [s] using hi
        rw [vectorMeasure_singleton, hsupp i hout]
        simp
  have hCm : MeasurableSet C := (Set.toFinite C).measurableSet
  have hparts := prob_add_prob_compl (μ := vectorMeasure v) hCm
  simpa only [hcomplement, add_zero] using hparts

/-- An existing class-supported probability measure must have
zero REAL point mass outside that class. -/
theorem realPointMass_supported_of_class
    (μ : ProbabilityMeasure Y) (C : Set Y)
    (hC : μ.toMeasure C = 1) :
    IsSupportedReal (realPointMass μ) C := by
  intro i hi
  have hCm : MeasurableSet C := (Set.toFinite C).measurableSet
  have hcompl : μ.toMeasure Cᶜ = 0 := by
    rw [prob_compl_eq_one_sub hCm, hC]
    simp
  have hsub : ({i} : Set Y) ⊆ Cᶜ := by
    intro j hj
    have hji : j = i := by simpa using hj
    subst j
    exact hi
  have hpoint : μ.toMeasure ({i} : Set Y) = 0 :=
    le_antisymm ((measure_mono hsub).trans_eq hcompl) bot_le
  simp [realPointMass, hpoint]

/-- Actual stationary probability measures EXIST and are UNIQUE
when SUPPORTED ON A FIXED CLOSED RECURRENT COMMUNICATING CLASS. -/
theorem exists_unique_stationary_probability_on_class
    (C : Set Y) (hC : C ∈ RecurrentClasses K) :
    ∃! μ : ProbabilityMeasure Y,
      Kernel.Invariant K μ.toMeasure ∧
      μ.toMeasure C = 1 := by
  classical
  obtain ⟨c, hclosed, hclass⟩ := (recurrentClasses_mem_iff K C).mp hC
  subst C
  letI : Nonempty Y := ⟨c⟩
  let D := CommunicatingClass K c
  have hmem : c ∈ D := mem_communicatingClass K c
  have hrealclosed : IsClosedReal (realTransition K) D :=
    kernelClosed_to_realClosed K D hclosed
  have hcomm : ∀ i ∈ D, ∀ j ∈ D,
      FiniteInvariantUniqueness.Reachable (realTransition K) i j :=
    class_real_irreducible K c
  obtain ⟨v, hv, hvtotal, hstat, hvSupp⟩ :=
    exists_stationary_supported
      (realTransition K)
      (realTransition_nonneg K)
      (realTransition_row_sum K)
      D c hmem hrealclosed
  let π : ProbabilityMeasure Y :=
    ⟨vectorMeasure v, vectorMeasure_isProbability v hv hvtotal⟩
  have hπInvariant : Kernel.Invariant K π.toMeasure :=
    vectorMeasure_invariant K v hv hstat
  have hπD : π.toMeasure D = 1 :=
    vectorMeasure_mass_one_of_support v hv hvtotal D hvSupp
  refine ⟨π, ⟨hπInvariant, hπD⟩, ?_⟩
  intro σ hσ
  have hσrealSupport : IsSupportedReal (realPointMass σ) D :=
    realPointMass_supported_of_class σ D hσ.2
  have hrealeq : realPointMass σ = v :=
    stationary_probability_unique_on_class
      (realTransition K) (realTransition_nonneg K)
      D hcomm (realPointMass σ) v
      (realPointMass_nonneg σ) hv
      (realPointMass_total σ) hvtotal
      (realPointMass_stationary K σ hσ.1) hstat
      hσrealSupport hvSupp
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_singleton
  intro i
  have hi : realPointMass σ i = v i := congrFun hrealeq i
  change (σ.toMeasure ({i} : Set Y)).toReal = v i at hi
  calc
    σ.toMeasure ({i} : Set Y) =
        ENNReal.ofReal ((σ.toMeasure ({i} : Set Y)).toReal) :=
      (ENNReal.ofReal_toReal (measure_ne_top σ.toMeasure _)).symm
    _ = ENNReal.ofReal (v i) := congrArg ENNReal.ofReal hi
    _ = π.toMeasure ({i} : Set Y) := by
      change ENNReal.ofReal (v i) = vectorMeasure v {i}
      exact (vectorMeasure_singleton v i).symm

end FiniteClassInvariantMeasure
end MultipleLimit
end PermanssonResearch
