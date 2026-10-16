import PermanssonResearch.RegimeExit.FiniteHistoryEvent
import PermanssonResearch.RegimeExit.ExitEvents
import Mathlib.Tactic

/-!
# C-Exit C — all-measurable stopped-path continuation via finite histories

The actual first-exit event depends only on the full prefix through
time n+1. This file represents its measurable finite-history subset
and proves a whole-future Ionescu--Tulcea mixture over those histories.

The next theorem, still OPEN, is that shifting the future kernel after
entry depends only on the terminal state. No hidden strong Markov
hypothesis or normalization is inserted.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit

set_option autoImplicit false
open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA uH
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X]
variable [MeasurableSpace A] [MeasurableSpace H]

/-- The measurable finite prefix that records the ORIGINAL first exit
at transition n+1 into D outside B. Time zero and all intermediate
states remain in B; the exit endpoint is part of the prefix. -/
def firstExitHistoryAt
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) (D : Set (JointState S X)) :
    Set ((i : Finset.Iic (n+1)) → JointState S X) :=
  {h | (∀ t : Finset.Iic n,
      h ⟨t.1, Finset.mem_Iic.mpr
        (Nat.le_succ_of_le (Finset.mem_Iic.mp t.2))⟩ ∈ spec.region)
    ∧ h ⟨n+1, Finset.mem_Iic.mpr le_rfl⟩ ∈ D \ spec.region}

/-- The first-exit history is genuinely measurable. The outside
mask is applied at exactly n+1, not at n or at an infinite time. -/
theorem firstExitHistoryAt_measurable
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) (D : Set (JointState S X))
    (hD : MeasurableSet D) :
    MeasurableSet (firstExitHistoryAt spec n D) := by
  unfold firstExitHistoryAt
  apply MeasurableSet.inter
  · have hset :
        {h : (i : Finset.Iic (n+1)) → JointState S X |
          ∀ t : Finset.Iic n,
            h ⟨t.1, Finset.mem_Iic.mpr
              (Nat.le_succ_of_le (Finset.mem_Iic.mp t.2))⟩ ∈
                spec.region} =
        ⋂ t : Finset.Iic n,
          (fun h : (i : Finset.Iic (n+1)) → JointState S X =>
            h ⟨t.1, Finset.mem_Iic.mpr
              (Nat.le_succ_of_le (Finset.mem_Iic.mp t.2))⟩) ⁻¹'
                spec.region := by
          ext h
          simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    have hi : MeasurableSet
        (⋂ t : Finset.Iic n,
          (fun h : (i : Finset.Iic (n+1)) → JointState S X =>
            h ⟨t.1, Finset.mem_Iic.mpr
              (Nat.le_succ_of_le (Finset.mem_Iic.mp t.2))⟩) ⁻¹'
                spec.region) := by
      apply MeasurableSet.iInter
      intro t
      exact spec.region_measurable.preimage (measurable_pi_apply _)
    rw [← hset] at hi
    exact hi
  · exact (hD.diff spec.region_measurable).preimage
      (measurable_pi_apply _)

/-- The original first-exit path event is EXACTLY the inverse image
of the finite-history event under the prefix map. -/
theorem firstExitAt_eq_history_preimage
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) (D : Set (JointState S X)) :
    firstExitAtDestination spec n D =
      (Preorder.frestrictLe (n+1)) ⁻¹'
        firstExitHistoryAt spec n D := by
  ext w
  change ((∀ t ≤ n, w t ∈ spec.region) ∧
    w (n+1) ∈ D \ spec.region) ↔
    ((∀ t : Finset.Iic n, w t.1 ∈ spec.region) ∧
    w (n+1) ∈ D \ spec.region)
  constructor
  · rintro ⟨hs, he⟩
    exact ⟨fun t => hs t.1 (Finset.mem_Iic.mp t.2), he⟩
  · rintro ⟨hs, he⟩
    exact ⟨fun t ht => hs ⟨t, Finset.mem_Iic.mpr ht⟩, he⟩

/-- The actual stopped first-exit path law, intersected with an
ARBITRARY measurable full-path event, equals the genuine conditional
absolute-time continuation integrated over first-exit histories. -/
theorem firstExitHistory_continuation_integral
    (N : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) (y : JointState S X)
    (D : Set (JointState S X)) (hD : MeasurableSet D)
    (F : Set (ℕ → JointState S X)) (hF : MeasurableSet F) :
    N.pathLaw (Measure.dirac y)
      (firstExitAtDestination spec n D ∩ F) =
    ∫⁻ h in firstExitHistoryAt spec n D,
      (canonicalHistoryContinuation N (n+1) h) F
      ∂((N.pathLaw (Measure.dirac y)).map
        (Preorder.frestrictLe (n+1))) := by
  rw [firstExitAt_eq_history_preimage]
  change N.pathLaw (Measure.dirac y)
    {w : ℕ → JointState S X |
      Preorder.frestrictLe (n+1) w ∈ firstExitHistoryAt spec n D
        ∧ w ∈ F} = _
  exact pointPathLaw_history_event N y (n+1)
    (firstExitHistoryAt spec n D) F
    (firstExitHistoryAt_measurable spec n D hD) hF

/-- Full-future (arbitrary measurable event) first-exit mixture over
history prefixes. The yet unproved further factorization must replace
the whole history by its arrival endpoint, not an arbitrary guess. -/
theorem firstExitHistory_shifted_future_integral
    (N : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) (y : JointState S X)
    (D : Set (JointState S X)) (hD : MeasurableSet D)
    (F : Set (ℕ → JointState S X)) (hF : MeasurableSet F) :
    N.pathLaw (Measure.dirac y)
      (firstExitAtDestination spec n D ∩
        (pathTailShift (S := S) (X := X) (n+1)) ⁻¹' F) =
    ∫⁻ h in firstExitHistoryAt spec n D,
      (canonicalHistoryContinuation N (n+1) h)
        ((pathTailShift (S := S) (X := X) (n+1)) ⁻¹' F)
      ∂((N.pathLaw (Measure.dirac y)).map
        (Preorder.frestrictLe (n+1))) := by
  exact firstExitHistory_continuation_integral N spec n y D hD
    ((pathTailShift (S := S) (X := X) (n+1)) ⁻¹' F)
    (hF.preimage (measurable_pathTailShift (S := S) (X := X) (n+1)))

end PermanssonResearch.RegimeExit
