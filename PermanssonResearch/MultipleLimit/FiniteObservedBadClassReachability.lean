import PermanssonResearch.MultipleLimit.FiniteObservedSupportReachability
import Mathlib.Tactic

/-!
# C8-02 — bad recurrent support and exact complement-event mass

A finite canonical trajectory fails the eventual-true event precisely
when its selected recurrent class contains a false-labelled state,
almost surely, not necessarily on all conceivable exceptional paths.
A graph-reachable BAD destination has positive canonical selection mass.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteObservedBadClassReachability

set_option autoImplicit false

open KernelCommunication
open CanonicalClassSelector
open CanonicalClassWeights
open FiniteCanonicalPath
open FiniteObservedClassSupport
open FiniteObservedEventMass
open FiniteObservedSupportReachability
open FrozenObservedEvent

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [Nonempty Y]
variable [DecidableEq Y] [StandardBorelSpace Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- Bad means SOME member of the recurrent communicating class
violates the frozen Boolean descriptor. Transient labels do not count. -/
noncomputable def badRecurrentRepresentatives (h : Y → Bool) : Finset Y := by
  classical
  exact (recurrentRepresentatives K).filter
    (fun i => ¬ AllTrueClass K h i)

/-- Exact complement probability from the TRUE K-canonical path,
not from a baseline selector evaluated on an intervened kernel. -/
theorem eventual_true_complement_mass_eq_bad_sum
    (h : Y → Bool) (μ : ProbabilityMeasure Y) :
    (canonicalPathLaw K μ.toMeasure) (eventuallyObserved h true)ᶜ =
    ∑ i ∈ badRecurrentRepresentatives K h,
      (canonicalPathLaw K μ.toMeasure)
        ((selectedRepresentative K) ⁻¹' ({i} : Set Y)) := by
  classical
  let P := canonicalPathLaw K μ.toMeasure
  let B := badRecurrentRepresentatives K h
  have hevents : (eventuallyObserved h true)ᶜ =ᵐ[P]
      ((selectedRepresentative K) ⁻¹' (↑B : Set Y)) := by
    filter_upwards [eventuallyObserved_iff_selectedGood_ae K h μ]
      with w hw
    change (¬ w ∈ eventuallyObserved h true) =
      (selectedRepresentative K w ∈ (↑B : Set Y))
    apply propext
    simpa [B, badRecurrentRepresentatives,
      selectedRepresentative_mem K w] using not_congr hw
  calc
    P (eventuallyObserved h true)ᶜ =
        P ((selectedRepresentative K) ⁻¹' (↑B : Set Y)) :=
      measure_congr hevents
    _ = ∑ i ∈ B,
          P ((selectedRepresentative K) ⁻¹' ({i} : Set Y)) := by
      exact (sum_measure_preimage_singleton
        (μ := P) B
        (fun i hi => (measurableSet_singleton i).preimage
          (selectedRepresentative_measurable K))).symm

/-- The exact complementary-event form of G2. No nonzero probability
cutoff is introduced: a tiny but genuinely positive path still counts. -/
theorem eventual_true_complement_positive_iff_reachable_bad
    (h : Y → Bool) (y : Y) :
    0 < (canonicalPathLaw K (Measure.dirac y))
      (eventuallyObserved h true)ᶜ ↔
      ∃ i ∈ badRecurrentRepresentatives K h, Reachable K y i := by
  classical
  rw [eventual_true_complement_mass_eq_bad_sum K h (diracProba y)]
  constructor
  · intro hpos
    by_contra hn
    push_neg at hn
    have hzero (i : Y) (hi : i ∈ badRecurrentRepresentatives K h) :
        canonicalPathLaw K (Measure.dirac y)
          ((selectedRepresentative K) ⁻¹' ({i} : Set Y)) = 0 := by
      by_contra hne
      exact hn i hi ((selected_weight_nonzero_iff_reachable K y i
        (Finset.mem_filter.mp hi).1).mp hne)
    have hsum :
        (∑ i ∈ badRecurrentRepresentatives K h,
          canonicalPathLaw K (Measure.dirac y)
            ((selectedRepresentative K) ⁻¹' ({i} : Set Y))) = 0 :=
      Finset.sum_eq_zero (fun i hi => hzero i hi)
    exact (ne_of_gt hpos) hsum
  · rintro ⟨i, hi, hreach⟩
    have hne := (selected_weight_nonzero_iff_reachable K y i
      (Finset.mem_filter.mp hi).1).mpr hreach
    have hpositive : 0 < canonicalPathLaw K (Measure.dirac y)
        ((selectedRepresentative K) ⁻¹' ({i} : Set Y)) :=
      lt_of_le_of_ne bot_le (Ne.symm hne)
    exact lt_of_lt_of_le hpositive
      (Finset.single_le_sum
        (fun j hj => bot_le)
        (show i ∈ badRecurrentRepresentatives K h from hi))

/-- G2 in its original probability-below-one form: the complement
of a genuine probability-one event has positive mass exactly when
the event itself is not almost sure. -/
theorem eventual_true_lt_one_iff_reachable_bad
    (h : Y → Bool) (y : Y) :
    (canonicalPathLaw K (Measure.dirac y))
      (eventuallyObserved h true) < 1 ↔
      ∃ i ∈ badRecurrentRepresentatives K h, Reachable K y i := by
  have hmeas : MeasurableSet (eventuallyObserved h true) :=
    eventuallyObserved_measurable h true Measurable.of_discrete
  have hmass : (canonicalPathLaw K (Measure.dirac y))
      (eventuallyObserved h true)ᶜ =
        1 - (canonicalPathLaw K (Measure.dirac y))
          (eventuallyObserved h true) :=
    prob_compl_eq_one_sub hmeas
  have hcomp :
      (canonicalPathLaw K (Measure.dirac y))
        (eventuallyObserved h true) < 1 ↔
      0 < (canonicalPathLaw K (Measure.dirac y))
        (eventuallyObserved h true)ᶜ := by
    rw [hmass]
    exact (tsub_pos_iff_lt).symm
  exact hcomp.trans
    (eventual_true_complement_positive_iff_reachable_bad K h y)

end FiniteObservedBadClassReachability
end MultipleLimit
end PermanssonResearch
