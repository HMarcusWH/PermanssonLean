import PermanssonResearch.MultipleLimit.RecurrentClassDecomposition
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Tactic

/-!
# Lane C2 — graph-closed finite classes have actual one-step probability one

A graph closure statement from positive atomic transition masses is NOT
merely a combinatorial slogan: for a FINITE state space with measurable
singletons, it forces the entire genuine Markov transition kernel to
assign unit mass to the class.

This module proves that fact by exact finite additivity and the original
Markov normalization; it assumes no aperiodicity or rational entries.
It does not claim every sample path stays in its class pointwise: that
stronger statement needs the canonical-path almost-sure continuation proof.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteClassClosure

open KernelCommunication
open RecurrentClassDecomposition

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- Graph-closed C is a one-step K-invariant region in the exact
measure-theoretic sense. Zero-mass excluded singletons cannot contribute
probability outside C. -/
theorem closedSubset_kernel_mass_one
    (C : Set Y) (hclosed : ClosedSubset K C)
    (i : Y) (hi : i ∈ C) :
    K i C = 1 := by
  classical
  let s : Finset Y := Finset.univ.filter (fun j => j ∉ C)
  have hs : (↑s : Set Y) = Cᶜ := by
    ext j
    simp [s]
  have hcomp : K i Cᶜ = 0 := by
    calc
      K i Cᶜ = K i (↑s : Set Y) := congrArg (K i) hs.symm
      _ = ∑ j ∈ s, K i ({j} : Set Y) :=
        (sum_measure_singleton).symm
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hjout : j ∉ C := by simpa [s] using hj
        have hnpos : ¬ PositiveEdge K i j := by
          intro hp
          exact hjout (hclosed i hi j hp)
        exact le_antisymm (not_lt.mp hnpos) bot_le
  have hCmeas : MeasurableSet C := (Set.toFinite C).measurableSet
  have htotal : K i C + K i Cᶜ = 1 :=
    prob_add_prob_compl hCmeas
  simpa only [hcomp, add_zero] using htotal

theorem recurrentStates_kernel_mass_one
    (i : Y) (hi : i ∈ RecurrentStates K) :
    K i (RecurrentStates K) = 1 :=
  closedSubset_kernel_mass_one K (RecurrentStates K)
    (recurrentStates_closed K) i hi

theorem recurrentClass_kernel_mass_one
    (C : Set Y) (hC : C ∈ RecurrentClasses K)
    (i : Y) (hi : i ∈ C) :
    K i C = 1 :=
  closedSubset_kernel_mass_one K C
    (recurrentClasses_closed K hC) i hi

end FiniteClassClosure
end MultipleLimit
end PermanssonResearch
