import PermanssonLean.Regime.SurvivalBridge
import Mathlib.Tactic

/-!
# C-Exit — measurable actual first-exit path cylinders

Horizon L counts transitions, with first possible exit at time 1 from B.
The event records destination at a *finite* n+1 index; it never evaluates
Y_τ for τ=∞. Event unions omit time-zero exits intentionally.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit

universe uS uX uA uH
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]
open PermanssonLean PermanssonLean.RegimeSpecification

/-- A first exit at transition n+1 into the measurable outside part of D. -/
def firstExitAtDestination
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) (D : Set (JointState S X)) :
    Set (ℕ → JointState S X) :=
  survivesThroughSet spec n ∩
    (fun w : ℕ → JointState S X => w (n + 1)) ⁻¹'
      (D \ spec.region)

/-- First exit by L transitions; at L=0 this is empty. -/
def firstExitWithinDestination
    (spec : RegimeSpecification (JointState S X) H)
    (L : ℕ) (D : Set (JointState S X)) :
    Set (ℕ → JointState S X) :=
  ⋃ n : Fin L, firstExitAtDestination spec (n : ℕ) D

/-- First exit at some positive finite time. -/
def firstExitEverDestination
    (spec : RegimeSpecification (JointState S X) H)
    (D : Set (JointState S X)) :
    Set (ℕ → JointState S X) :=
  ⋃ n : ℕ, firstExitAtDestination spec n D

theorem firstExitAtDestination_measurable
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) (D : Set (JointState S X))
    (hD : MeasurableSet D) :
    MeasurableSet (firstExitAtDestination spec n D) := by
  exact (measurableSet_survivesThroughSet spec n).inter
    ((hD.diff spec.region_measurable).preimage (measurable_pi_apply (n + 1)))

theorem firstExitWithinDestination_measurable
    (spec : RegimeSpecification (JointState S X) H)
    (L : ℕ) (D : Set (JointState S X))
    (hD : MeasurableSet D) :
    MeasurableSet (firstExitWithinDestination spec L D) := by
  exact MeasurableSet.iUnion fun n =>
    firstExitAtDestination_measurable spec (n : ℕ) D hD

theorem firstExitEverDestination_measurable
    (spec : RegimeSpecification (JointState S X) H)
    (D : Set (JointState S X))
    (hD : MeasurableSet D) :
    MeasurableSet (firstExitEverDestination spec D) := by
  exact MeasurableSet.iUnion fun n =>
    firstExitAtDestination_measurable spec n D hD

theorem firstExitWithinDestination_zero
    (spec : RegimeSpecification (JointState S X) H)
    (D : Set (JointState S X)) :
    firstExitWithinDestination spec 0 D = ∅ := by
  simp [firstExitWithinDestination]

theorem firstExitAtDestination_disjoint
    (spec : RegimeSpecification (JointState S X) H)
    (D : Set (JointState S X)) {n m : ℕ} (hne : n ≠ m) :
    Disjoint (firstExitAtDestination spec n D)
      (firstExitAtDestination spec m D) := by
  apply Set.disjoint_left.mpr
  intro w hn hm
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstay : w (n+1) ∈ spec.region := hm.1 (n+1) (by omega)
    exact hn.2.2 hstay
  · have hstay : w (m+1) ∈ spec.region := hn.1 (m+1) (by omega)
    exact hm.2.2 hstay

/-- Exact pathwise stopping-time semantics without a dangerous index at ∞. -/
theorem firstExitAt_eq_exitTime_succ
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) (D : Set (JointState S X))
    (w : ℕ → JointState S X) :
    w ∈ firstExitAtDestination spec n D ↔
      exitTime spec w = (n+1 : ℕ∞) ∧ w (n+1) ∈ D := by
  classical
  constructor
  · rintro ⟨hs, hD, hout⟩
    have hex : ∃ t : ℕ, w t ∉ spec.region := ⟨n+1, hout⟩
    have hmin : Nat.find hex ≤ n+1 := Nat.find_min' hex hout
    have hn : n < Nat.find hex := by
      by_contra h
      have hz : w (Nat.find hex) ∈ spec.region :=
        hs (Nat.find hex) (by omega)
      exact (Nat.find_spec hex) hz
    have hval : Nat.find hex = n+1 := by omega
    constructor
    · simp [exitTime, dif_pos hex, hval]
    · exact hD
  · rintro ⟨ht, hD⟩
    by_cases hex : ∃ t : ℕ, w t ∉ spec.region
    · have hval : Nat.find hex = n+1 := by
        simpa [exitTime, dif_pos hex] using ht
      refine ⟨?_, hD, ?_⟩
      · intro t htle
        by_contra hnot
        have hmin := Nat.find_min' hex hnot
        omega
      · simpa [← hval] using (Nat.find_spec hex)
    · have htop : exitTime spec w = ⊤ := by simp [exitTime, dif_neg hex]
      rw [htop] at ht
      exact (ENat.coe_ne_top (n+1) ht.symm).elim

theorem firstExitAtDestination_mask
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) (D : Set (JointState S X)) :
    firstExitAtDestination spec n D =
      firstExitAtDestination spec n (D \ spec.region) := by
  simp [firstExitAtDestination, Set.diff_diff]

theorem firstExitAtDestination_subset_ever
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) (D : Set (JointState S X)) :
    firstExitAtDestination spec n D ⊆ firstExitEverDestination spec D := by
  intro w hw
  exact Set.mem_iUnion.mpr ⟨n, hw⟩

end PermanssonResearch.RegimeExit
