import PermanssonResearch.MultipleLimit.FrozenObservedEvent
import PermanssonResearch.MultipleLimit.ExactSixStateObservedGR
import PermanssonResearch.MultipleLimit.ExactSixStateCanonical
import PermanssonResearch.MultipleLimit.CanonicalKernelMarginals
import PermanssonResearch.MultipleLimit.CanonicalClassContinuation
import Mathlib.Tactic

/-!
# C6 — actual sparse six-state alpha-only regime-target disruption

Baseline is C2/C3's genuine six-state alpha/P/U model. The replacement
changes ONLY the action-selection rows for u and a0, sending both to u.
All other rows are literally unchanged. It is installed through D0's
existing typed admissible strategic intervention, preserving P and U.
The ORIGINAL six-state model and its frozen v0.1.8 region/descriptor
are left untouched.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactSixStateTargetDisruption

open PermanssonLean
open PermanssonLean.RegimeSpecification
open ReverseSolver.FiniteStrategicRealization
open ExactSixState
open ExactSixStateCanonical
open ExactSixStateTyped
open ExactSixStateObservedGR
open ExactSixStateKernelRegion
open FiniteCanonicalPath
open CanonicalKernelMarginals
open CanonicalClassContinuation
open FrozenObservedEvent
open KernelCommunication

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

abbrev SixY := JointState Unit (Fin 6)
def u : SixY := decode (1 : Fin 6)
def a0 : SixY := decode (2 : Fin 6)
def t : SixY := decode (0 : Fin 6)

/-- Exact rational sparse alpha-only replacement. u is absorbing and
a0 points directly to u. No other rational transition row changes. -/
def disruptedEntry (i j : Fin 6) : ℚ :=
  if i = 1 ∨ i = 2 then
    if j = 1 then 1 else 0
  else
    transition i j

theorem disruptedEntry_nonneg (i j : Fin 6) :
    0 ≤ disruptedEntry i j := by
  unfold disruptedEntry
  split_ifs with h1 h2
  · norm_num
  · norm_num
  · exact transition_nonneg i j

theorem disruptedEntry_row_sum (i : Fin 6) :
    (∑ j : Fin 6, disruptedEntry i j) = 1 := by
  fin_cases i <;> norm_num [disruptedEntry, transition, Fin.sum_univ_succ]

/-- A fully normalized rational Markov kernel with exact sparse changes. -/
def disruptedMatrix : ReverseSolver.RationalMarkovMatrix 6 where
  entry := disruptedEntry
  entry_nonneg := disruptedEntry_nonneg
  row_sum_one := disruptedEntry_row_sum

noncomputable def intervention :=
  rationalStrategicIntervention sixStateMatrix disruptedMatrix

noncomputable def disruptedModel :=
  realizedModel disruptedMatrix

private noncomputable abbrev Kd := disruptedModel.inducedKernel

/-- The original typed intervention applies to the SAME alpha/P/U
baseline model and reconstructs the actual proposed replacement. -/
theorem intervention_apply :
    intervention.intervention.apply = disruptedModel := rfl

theorem intervention_world_fixed :
    disruptedModel.world = typedModel.world :=
  rationalStrategicIntervention_world_fixed sixStateMatrix disruptedMatrix

theorem intervention_update_fixed :
    disruptedModel.generator.update = typedModel.generator.update :=
  rationalStrategicIntervention_update_fixed sixStateMatrix disruptedMatrix

/-- Every other row retains its original rational transition probabilities. -/
theorem disruptedEntry_unchanged
    (i j : Fin 6) (hi : i ≠ 1 ∧ i ≠ 2) :
    disruptedEntry i j = transition i j := by
  simp [disruptedEntry, hi.1, hi.2]

theorem disruptedEntry_u (j : Fin 6) :
    disruptedEntry 1 j = (if j = 1 then 1 else 0) := by
  simp [disruptedEntry]

theorem disruptedEntry_a0 (j : Fin 6) :
    disruptedEntry 2 j = (if j = 1 then 1 else 0) := by
  simp [disruptedEntry]

/-- Genuine typed next-state singleton atom. It uses D0's certified
physical alpha/P/U realization, not an unrelated reference matrix. -/
theorem disrupted_typed_atom (i j : Fin 6) :
    Kd (decode i) ({decode j} : Set SixY) =
      ENNReal.ofReal ((disruptedEntry i j : ℚ) : ℝ) := by
  have hset : ({decode j} : Set SixY) =
      encode ⁻¹' ({j} : Set (Fin 6)) := by
    ext y
    rcases y with ⟨s, k⟩
    cases s
    simp [decode, encode]
  rw [hset]
  exact inducedKernel_encodedEntry disruptedMatrix i j

/-- The two exact changed whole kernel rows, not only a single atom. -/
theorem disrupted_row_to_u (i : Fin 6)
    (hi : i = 1 ∨ i = 2) :
    Kd (decode i) = Measure.dirac u := by
  apply Measure.ext_of_singleton
  intro y
  rcases y with ⟨s, j⟩
  cases s
  change Kd (decode i) ({decode j} : Set SixY) =
    Measure.dirac (decode (1 : Fin 6)) ({decode j} : Set SixY)
  rw [disrupted_typed_atom]
  rcases hi with hi | hi
  · subst i
    fin_cases j <;> norm_num [disruptedEntry, decode]
  · subst i
    fin_cases j <;> norm_num [disruptedEntry, decode]

theorem disrupted_row_u : Kd u = Measure.dirac u :=
  disrupted_row_to_u 1 (Or.inl rfl)

theorem disrupted_row_a0 : Kd a0 = Measure.dirac u :=
  disrupted_row_to_u 2 (Or.inr rfl)

/-- u is a genuine closed singleton, even though it was transient
under the baseline kernel. -/
theorem disrupted_u_closed : ClosedSubset Kd ({u} : Set SixY) := by
  intro y hy z hpositive
  have hyu : y = u := Set.mem_singleton_iff.mp hy
  subst y
  rw [disrupted_row_u] at hpositive
  by_contra hnot
  have hzero : (Measure.dirac u) ({z} : Set SixY) = 0 := by
    have hz : z ≠ u := by simpa using hnot
    simp [hz]
  exact (ne_of_gt hpositive) hzero

/-- The proper five-state original regime region remains exactly closed
under the intervened physical process; no access to excluded t is added. -/
theorem disrupted_no_entry_t (y : SixY) :
    Kd y ({t} : Set SixY) = 0 := by
  obtain ⟨s,i⟩ := y
  cases s
  change Kd (decode i) ({decode (0 : Fin 6)} : Set SixY) = 0
  rw [disrupted_typed_atom]
  fin_cases i <;> norm_num [disruptedEntry, transition]

theorem disrupted_region_closed :
    ClosedSubset Kd typedRegion := by
  intro y hy z hz
  rw [typedRegion_eq_compl_singleton]
  by_contra hnot
  have hzt : z = t := by simpa [t] using hnot
  subst z
  exact (ne_of_gt hz) (disrupted_no_entry_t y)

/-- Under the genuine intervened infinite Markov path law, the state at
time one is exactly u from BOTH declared baseline comparison starts. -/
theorem time_one_dirac_u (i : Fin 6)
    (hi : i = 1 ∨ i = 2) :
    (canonicalPathLaw Kd (Measure.dirac (decode i))).map
      (fun w : ℕ → SixY => w 1) = Measure.dirac u := by
  have h := canonical_eval_eq_kernel_pow Kd (decode i) 1
  rw [pow_one] at h
  exact h.trans (disrupted_row_to_u i hi)

/-- Exact time-one support under the real infinite path law,
not an assumption of independent state draws. -/
theorem time_one_u_ae (i : Fin 6)
    (hi : i = 1 ∨ i = 2) :
    ∀ᵐ w ∂canonicalPathLaw Kd (Measure.dirac (decode i)),
      w 1 = u := by
  rw [ae_iff]
  change (canonicalPathLaw Kd (Measure.dirac (decode i)))
    {w : ℕ → SixY | w 1 ≠ u} = 0
  have hset : {w : ℕ → SixY | w 1 ≠ u} =
      (fun w : ℕ → SixY => w 1) ⁻¹' ({u} : Set SixY)ᶜ := by
    ext w
    simp
  rw [hset, ← Measure.map_apply (measurable_pi_apply 1)
    (measurableSet_singleton u).compl]
  rw [time_one_dirac_u i hi]
  simp

/-- Genuine almost-sure absorption of the ORIGINAL canonical infinite
path for the intervened model from either frozen basin start. -/
theorem eventually_u_ae (i : Fin 6)
    (hi : i = 1 ∨ i = 2) :
    ∀ᵐ w ∂canonicalPathLaw Kd (Measure.dirac (decode i)),
      ∃ N : ℕ, ∀ n ≥ N, w n = u := by
  filter_upwards [
    time_one_u_ae i hi,
    closed_stay_after_entry_ae Kd (diracProba (decode i))
      ({u} : Set SixY) disrupted_u_closed
  ] with w h1 hstay
  refine ⟨1, ?_⟩
  intro n hn
  exact Set.mem_singleton_iff.mp
    (hstay 1 (Set.mem_singleton_iff.mpr h1) n hn)

/-- The frozen baseline Boolean descriptor is FALSE on u. -/
theorem descriptor_u_false :
    observedDescriptor u = false := by
  norm_num [observedDescriptor, u, observedRecurrent, encode, decode]

/-- Actual intervened trajectories from the original nontrivial basin
eventually have frozen observed value FALSE, not TRUE. -/
theorem eventually_false_ae (i : Fin 6)
    (hi : i = 1 ∨ i = 2) :
    ∀ᵐ w ∂canonicalPathLaw Kd (Measure.dirac (decode i)),
      w ∈ eventuallyObserved observedDescriptor false := by
  filter_upwards [eventually_u_ae i hi] with w h
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun n hn => by rw [hN n hn, descriptor_u_false]⟩

end
end ExactSixStateTargetDisruption
end MultipleLimit
end PermanssonResearch
