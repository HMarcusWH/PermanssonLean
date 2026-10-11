import PermanssonResearch.MultipleLimit.FiniteInvariantMeasureTransport
import PermanssonResearch.MultipleLimit.KernelCommunication
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Tactic

/-!
# Lane C2 — uniqueness of genuine invariant measures on irreducible finite chains

An arbitrary finite Markov kernel K may have irrational transition
weights. This file reads exact real singleton masses, shows an
invariant MEASURE gives a stationary REAL row probability vector, and
transports the independently proved real irreducible uniqueness
theorem back to equality of WHOLE Markov probability measures.

Existence is already constructed via finite Cesaro compactness and
measure-level transport: together the two results give unique
invariant probability on any finite irreducible K without
aperiodicity. Applying this on a closed communicating CLASS,
rather than on a globally irreducible full state space, is a
separate explicit reindexing/transport obligation.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteKernelInvariantUniqueness

open FiniteKernelRealBridge
open FiniteInvariantUniqueness
open FiniteCesaroAlgebra

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

noncomputable def realPointMass (μ : ProbabilityMeasure Y) (i : Y) : ℝ :=
  (μ.toMeasure ({i} : Set Y)).toReal

theorem realPointMass_nonneg (μ : ProbabilityMeasure Y) (i : Y) :
    0 ≤ realPointMass μ i :=
  ENNReal.toReal_nonneg

theorem realPointMass_total (μ : ProbabilityMeasure Y) :
    (∑ i : Y, realPointMass μ i) = 1 := by
  classical
  change (∑ i : Y, (μ.toMeasure ({i} : Set Y)).toReal) = 1
  rw [← ENNReal.toReal_sum (fun i hi => measure_ne_top μ.toMeasure _)]
  have hsum : (∑ i : Y, μ.toMeasure ({i} : Set Y)) =
      μ.toMeasure Set.univ := by
    simpa using (sum_measure_singleton
      (μ := μ.toMeasure) (s := (Finset.univ : Finset Y)))
  rw [hsum]
  simp

theorem realPointMass_stationary
    (μ : ProbabilityMeasure Y) (hInv : Kernel.Invariant K μ.toMeasure)
    (j : Y) :
    pushVector (realTransition K) (realPointMass μ) j =
      realPointMass μ j := by
  have hInvMeasure : μ.toMeasure.bind K = μ.toMeasure := hInv
  have hsum :
      (∑ i : Y, K i ({j} : Set Y) *
          μ.toMeasure ({i} : Set Y)) =
        μ.toMeasure ({j} : Set Y) := by
    calc
      _ = ∫⁻ i, K i ({j} : Set Y) ∂μ.toMeasure :=
        (lintegral_fintype (fun i : Y => K i ({j} : Set Y))).symm
      _ = (μ.toMeasure.bind K) ({j} : Set Y) :=
        (Measure.bind_apply (measurableSet_singleton j)
          (Kernel.aemeasurable K)).symm
      _ = μ.toMeasure ({j} : Set Y) :=
        congrArg (fun ξ : Measure Y => ξ ({j} : Set Y)) hInvMeasure
  have hreal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_sum (fun i hi => by finiteness)] at hreal
  simp_rw [ENNReal.toReal_mul] at hreal
  simpa only [pushVector, realTransition, realPointMass, mul_comm] using hreal

/-- Actual positive-edge reachability in the real kernel is
exactly suitable for irreducibility of its finite real matrix. -/
theorem reachable_real_of_kernel {i j : Y}
    (hij : KernelCommunication.Reachable K i j) :
    FiniteInvariantUniqueness.Reachable (realTransition K) i j := by
  induction hij with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hprev hedge ih =>
      apply Relation.ReflTransGen.tail ih
      change 0 < (K _ ({_} : Set Y)).toReal
      exact ENNReal.toReal_pos hedge.ne'
        (kernel_singleton_ne_top K _ _)

/-- A unique invariant probability measure for any globally irreducible
finite Markov kernel, with NO aperiodicity, stationarity-of-start or
rational-matrix assumption. -/
theorem invariant_probability_unique_irreducible
    (hirr : ∀ i j : Y, KernelCommunication.Reachable K i j)
    (μ ν : ProbabilityMeasure Y)
    (hμ : Kernel.Invariant K μ.toMeasure)
    (hν : Kernel.Invariant K ν.toMeasure) :
    μ = ν := by
  have hvec :
      realPointMass μ = realPointMass ν :=
    stationary_probability_unique
      (realTransition K) (realTransition_nonneg K)
      (fun i j => reachable_real_of_kernel K (hirr i j))
      (realPointMass μ) (realPointMass ν)
      (realPointMass_nonneg μ) (realPointMass_nonneg ν)
      (realPointMass_total μ) (realPointMass_total ν)
      (realPointMass_stationary K μ hμ)
      (realPointMass_stationary K ν hν)
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_singleton
  intro i
  have hi : realPointMass μ i = realPointMass ν i :=
    congrFun hvec i
  change (μ.toMeasure ({i} : Set Y)).toReal =
    (ν.toMeasure ({i} : Set Y)).toReal at hi
  calc
    μ.toMeasure ({i} : Set Y) =
        ENNReal.ofReal ((μ.toMeasure ({i} : Set Y)).toReal) :=
      (ENNReal.ofReal_toReal (measure_ne_top μ.toMeasure _)).symm
    _ = ENNReal.ofReal ((ν.toMeasure ({i} : Set Y)).toReal) :=
      congrArg ENNReal.ofReal hi
    _ = ν.toMeasure ({i} : Set Y) :=
      ENNReal.ofReal_toReal (measure_ne_top ν.toMeasure _)

/-- Existentially construct, AND prove uniqueness of, a true
stationary Markov probability on any nonempty finite irreducible K. -/
theorem exists_unique_invariant_probability_irreducible
    [Nonempty Y]
    (hirr : ∀ i j : Y, KernelCommunication.Reachable K i j) :
    ∃! μ : ProbabilityMeasure Y, Kernel.Invariant K μ.toMeasure := by
  obtain ⟨ρ, hρprob, hρinv⟩ :=
    FiniteInvariantMeasureTransport.exists_stationary_probability K
  let π : ProbabilityMeasure Y := ⟨ρ, hρprob⟩
  refine ⟨π, hρinv, ?_⟩
  intro ν hν
  exact (invariant_probability_unique_irreducible K hirr ν π hν hρinv)

end FiniteKernelInvariantUniqueness
end MultipleLimit
end PermanssonResearch
