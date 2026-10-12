import PermanssonResearch.MultipleLimit.RecurrentClassDecomposition
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Lane C2 — stationary mass and irreducible-class support

These unconditional IMPLICATIONS hold for arbitrary finite stochastic
kernels with potentially irrational transition masses. Invariance is an
explicit hypothesis because this module does NOT construct an invariant
probability measure.

If a stationary law has positive mass at a state, positive one-step
transitions and therefore all positive-probability reachable states
must also have positive stationary mass. Consequently, an invariant
probability supported on a closed irreducible communicating class has
strictly positive mass at every state of that class.

Existence, uniqueness and almost-sure empirical ergodicity remain
separate open requirements; this is not their certification.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteInvariantSupport

open KernelCommunication
open RecurrentClassDecomposition

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- An invariant finite measure cannot assign zero mass to a state
whose incoming positive transition comes from a positive-mass state.
Uses the genuine kernel–measure bind and lintegral positivity. -/
theorem positive_invariant_mass_of_edge
    (π : Measure Y) (hπ : Kernel.Invariant K π)
    {i j : Y}
    (hi : 0 < π ({i} : Set Y))
    (hij : PositiveEdge K i j) :
    0 < π ({j} : Set Y) := by
  have hf : Measurable (fun x : Y => K x ({j} : Set Y)) :=
    Kernel.measurable_coe K (measurableSet_singleton j)
  have hsub : ({i} : Set Y) ⊆
      Function.support (fun x : Y => K x ({j} : Set Y)) := by
    intro x hx
    have heq : x = i := by simpa using hx
    subst x
    exact ne_of_gt hij
  have hp : 0 <
      π (Function.support (fun x : Y => K x ({j} : Set Y))) :=
    lt_of_lt_of_le hi (measure_mono hsub)
  have hl : 0 < ∫⁻ x, K x ({j} : Set Y) ∂π :=
    (lintegral_pos_iff_support hf).2 hp
  calc
    0 < ∫⁻ x, K x ({j} : Set Y) ∂π := hl
    _ = (π.bind K) {j} :=
      (Measure.bind_apply (measurableSet_singleton j)
        (Kernel.aemeasurable K)).symm
    _ = π {j} := congrArg (fun ν : Measure Y => ν {j}) hπ

/-- Positivity propagates along every actual positive-edge path. -/
theorem positive_invariant_mass_of_reachable
    (π : Measure Y) (hπ : Kernel.Invariant K π)
    {i j : Y}
    (hi : 0 < π ({i} : Set Y))
    (hij : Reachable K i j) :
    0 < π ({j} : Set Y) := by
  induction hij with
  | refl => exact hi
  | tail hprev hedge ih =>
      exact positive_invariant_mass_of_edge K π hπ ih hedge

/-- Any finite measure assigning positive mass to a set has a positive
atomic mass at some state of the set; all atomic quantities are exact. -/
theorem exists_positive_atom_of_positive_set
    (π : Measure Y) (C : Set Y) (hC : 0 < π C) :
    ∃ i ∈ C, 0 < π ({i} : Set Y) := by
  classical
  let s : Finset Y := Finset.univ.filter (· ∈ C)
  have hs : (↑s : Set Y) = C := by
    ext i
    simp [s]
  have hsum : (∑ i ∈ s, π ({i} : Set Y)) = π C := by
    rw [sum_measure_singleton]
    rw [hs]
  by_contra hn
  push_neg at hn
  have hz : ∀ i ∈ s, π ({i} : Set Y) = 0 := by
    intro i hi
    have hle : π ({i} : Set Y) ≤ 0 :=
      hn i (by simpa [s] using hi)
    exact le_antisymm hle bot_le
  have hzero : (∑ i ∈ s, π ({i} : Set Y)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hz i hi
  exact (ne_of_gt hC) (by simpa [hzero] using hsum.symm)

/-- An invariant probability law supported on an irreducible class
cannot exclude any state of that class. This proves full support
*conditionally on existence*, not the existence of such a law. -/
theorem invariant_class_full_support
    (π : Measure Y) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant K π)
    (c : Y)
    (hπC : π (CommunicatingClass K c) = 1)
    {j : Y} (hj : j ∈ CommunicatingClass K c) :
    0 < π ({j} : Set Y) := by
  have hCpositive : 0 < π (CommunicatingClass K c) := by
    rw [hπC]
    norm_num
  obtain ⟨i, hi, hpi⟩ :=
    exists_positive_atom_of_positive_set π (CommunicatingClass K c)
      hCpositive
  have hij : Reachable K i j :=
    (communicates_trans K (communicates_symm K hi) hj).1
  exact positive_invariant_mass_of_reachable K π hπ hpi hij

end FiniteInvariantSupport
end MultipleLimit
end PermanssonResearch
