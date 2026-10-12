import PermanssonResearch.MultipleLimit.PositiveKernelPowers
import PermanssonResearch.MultipleLimit.FiniteClassClosure
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Lane C2 — finite uniform positive entry into the recurrent-class union

For any FIXED nonempty finite Markov chain with measurable singleton
states, there is a common finite transition horizon N and a strictly
positive lower probability epsilon of being in the recurrent-class union.
The proof uses genuine kernel powers, finite maximal-reachability,
measure-theoretic class invariance, exact Chapman–Kolmogorov equations
and compact *finite* minima of finitely many positive numbers.

The constants DEPEND on the chain. No universal lower bound across all
finite stochastic kernels is asserted. This is the structural precursor
to a.s. entry via geometric tail bounds, NOT that conclusion by itself.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace UniformClassEntry

open KernelCommunication
open RecurrentClassDecomposition
open PositiveKernelPowers
open FiniteClassClosure

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- A closed finite target accumulates (never loses) Markov probability
mass as the time horizon grows. This works for arbitrary ENNReal
transition probabilities, without period or irreducibility hypotheses. -/
theorem closedKernel_power_mass_monotone
    (C : Set Y) (hclosed : ClosedSubset K C) (y : Y) :
    Monotone (fun n : ℕ => (K ^ n) y C) := by
  classical
  have hC : MeasurableSet C := (Set.toFinite C).measurableSet
  refine monotone_nat_of_le_succ (fun n => ?_)
  rw [Kernel.pow_succ_apply_eq_lintegral K n y hC]
  calc
    (K ^ n) y C =
        ∫⁻ z, C.indicator (fun _ : Y => (1 : ℝ≥0∞)) z ∂((K ^ n) y) :=
      (lintegral_indicator_one hC).symm
    _ ≤ ∫⁻ z, K z C ∂((K ^ n) y) := by
      apply lintegral_mono
      intro z
      by_cases hz : z ∈ C
      · simp [Set.indicator_of_mem hz,
          closedSubset_kernel_mass_one K C hclosed z hz]
      · simp [Set.indicator_of_notMem hz]

/-- For every initial state, the actual kernel reaches the finite
recurrent-state UNION with strictly positive probability at some
finite horizon. This is a kernel-power statement, not just graph
reachability. -/
theorem eventually_positive_recurrent_mass (y : Y) :
    ∃ n : ℕ, 0 < (K ^ n) y (RecurrentStates K) := by
  obtain ⟨c, hc, n, hpos⟩ := positive_power_to_closed_class K y
  refine ⟨n, lt_of_lt_of_le hpos ?_⟩
  apply measure_mono
  intro z hz
  have hzc : z = c := by simpa using hz
  subst z
  exact hc

/-- Finiteness lets us synchronize all state-dependent positive entry
horizons to ONE common N, using monotonic mass in the closed recurrent
union. N is chain-dependent, never a universal constant. -/
theorem exists_uniform_recurrent_horizon :
    ∃ N : ℕ, ∀ y : Y, 0 < (K ^ N) y (RecurrentStates K) := by
  classical
  have hpoint : ∀ y : Y,
      ∃ n : ℕ, 0 < (K ^ n) y (RecurrentStates K) :=
    eventually_positive_recurrent_mass K
  let n : Y → ℕ := fun y => Classical.choose (hpoint y)
  let N : ℕ := Finset.univ.sup n
  refine ⟨N, ?_⟩
  intro y
  have hn : n y ≤ N := Finset.le_sup (Finset.mem_univ y)
  have hmon := closedKernel_power_mass_monotone K
    (RecurrentStates K) (recurrentStates_closed K) y
  exact lt_of_lt_of_le (Classical.choose_spec (hpoint y)) (hmon hn)

/-- The finite family of positive N-step probabilities has a
strictly positive common lower bound epsilon, with no rational
approximation and no assumed class-hitting or ergodic statement. -/
theorem exists_uniform_positive_recurrent_block [Nonempty Y] :
    ∃ N : ℕ, ∃ ε : ℝ≥0∞, 0 < ε ∧
      ∀ y : Y, ε ≤ (K ^ N) y (RecurrentStates K) := by
  classical
  obtain ⟨N, hN⟩ := exists_uniform_recurrent_horizon K
  let v : Y → ℝ≥0∞ := fun y => (K ^ N) y (RecurrentStates K)
  have huniv : (Finset.univ : Finset Y).Nonempty := Finset.univ_nonempty
  let ε : ℝ≥0∞ := Finset.univ.inf' huniv v
  refine ⟨N, ε, ?_, ?_⟩
  · exact (Finset.lt_inf'_iff huniv).2 (fun y hy => hN y)
  · intro y
    exact Finset.inf'_le v (Finset.mem_univ y)

end UniformClassEntry
end MultipleLimit
end PermanssonResearch
