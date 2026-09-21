import PermanssonLean.Regime.KilledKernel
import PermanssonLean.StrategicWorld.PathLaw
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.MeasureTheory.Measure.DiracProba

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonLean

universe uS uX uA uH

variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]

namespace RegimeSpecification

/-- A trajectory remains in B through time n, including coordinate zero. -/
def SurvivesThrough
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) (w : ℕ → JointState S X) : Prop :=
  ∀ t ≤ n, w t ∈ spec.region

/-- The measurable finite-horizon survival event. -/
def survivesThroughSet
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) : Set (ℕ → JointState S X) :=
  {w | SurvivesThrough spec n w}

theorem measurableSet_survivesThroughSet
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) :
    MeasurableSet (survivesThroughSet spec n) := by
  have hEq :
      survivesThroughSet spec n =
        ⋂ t : Fin (n + 1),
          (fun w : ℕ → JointState S X => w (t : ℕ)) ⁻¹' spec.region := by
    ext w
    simp only [survivesThroughSet, SurvivesThrough, Set.mem_setOf_eq, Set.mem_iInter,
      Set.mem_preimage]
    constructor
    · intro h t
      exact h t (Nat.lt_succ_iff.mp t.isLt)
    · intro h t ht
      exact h ⟨t, Nat.lt_succ_iff.mpr ht⟩
  rw [hEq]
  exact MeasurableSet.iInter fun t =>
    spec.region_measurable.preimage (measurable_pi_apply (t : ℕ))

/-- Indefinite pathwise retention in B. -/
def SurvivesForever
    (spec : RegimeSpecification (JointState S X) H)
    (w : ℕ → JointState S X) : Prop :=
  ∀ t : ℕ, w t ∈ spec.region

def survivesForeverSet
    (spec : RegimeSpecification (JointState S X) H) :
    Set (ℕ → JointState S X) :=
  {w | SurvivesForever spec w}

theorem measurableSet_survivesForeverSet
    (spec : RegimeSpecification (JointState S X) H) :
    MeasurableSet (survivesForeverSet spec) := by
  have hEq :
      survivesForeverSet spec =
        ⋂ t : ℕ, (fun w : ℕ → JointState S X => w t) ⁻¹' spec.region := by
    ext w
    simp [survivesForeverSet, SurvivesForever]
  rw [hEq]
  exact MeasurableSet.iInter fun t =>
    spec.region_measurable.preimage (measurable_pi_apply t)

/-- First exit time from B, valued in extended naturals.

It is infinity exactly when the trajectory never leaves B.
-/
noncomputable def exitTime
    (spec : RegimeSpecification (JointState S X) H)
    (w : ℕ → JointState S X) : ℕ∞ := by
  classical
  exact if h : ∃ t : ℕ, w t ∉ spec.region
    then (Nat.find h : ℕ∞)
    else ⊤

theorem exitTime_eq_top_iff
    (spec : RegimeSpecification (JointState S X) H)
    (w : ℕ → JointState S X) :
    exitTime spec w = ⊤ ↔ SurvivesForever spec w := by
  classical
  by_cases h : ∃ t : ℕ, w t ∉ spec.region
  · rw [exitTime, dif_pos h]
    constructor
    · intro htop
      exact (ENat.coe_ne_top (Nat.find h) htop).elim
    · intro hforever
      exact False.elim ((Nat.find_spec h) (hforever (Nat.find h)))
  · rw [exitTime, dif_neg h]
    constructor
    · intro _
      intro t
      by_contra ht
      exact h ⟨t, ht⟩
    · intro _
      rfl

theorem exitTime_gt_nat_iff
    (spec : RegimeSpecification (JointState S X) H)
    (w : ℕ → JointState S X) (n : ℕ) :
    (n : ℕ∞) < exitTime spec w ↔ SurvivesThrough spec n w := by
  classical
  by_cases h : ∃ t : ℕ, w t ∉ spec.region
  · rw [exitTime, dif_pos h]
    norm_cast
    constructor
    · intro hn t ht
      by_contra hnot
      have hmin : Nat.find h ≤ t := Nat.find_min' h hnot
      omega
    · intro hsurv
      by_contra hnotlt
      have hle : Nat.find h ≤ n := Nat.le_of_not_gt hnotlt
      exact (Nat.find_spec h) (hsurv (Nat.find h) hle)
  · rw [exitTime, dif_neg h]
    constructor
    · intro _
      intro t ht
      by_contra hnot
      exact h ⟨t, hnot⟩
    · intro _
      exact ENat.coe_lt_top n

theorem exitTime_gt_event
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) :
    {w : ℕ → JointState S X | (n : ℕ∞) < exitTime spec w} =
      survivesThroughSet spec n := by
  ext w
  exact exitTime_gt_nat_iff spec w n


/-- The time-zero marginal of the canonical path law is exactly the declared
initial law. This is a convenient projection form of `pathLaw_prefix_zero`. -/
theorem StrategicWorldModel.pathLaw_eval_zero
    (M : StrategicWorldModel S X A)
    (mu0 : Measure (JointState S X))
    [IsProbabilityMeasure mu0] :
    (M.pathLaw mu0).map (fun w : ℕ → JointState S X => w 0) = mu0 := by
  letI : Unique (Finset.Iic (0 : ℕ)) := {
    default := ⟨0, by simp⟩
    uniq := fun i => by
      apply Subtype.ext
      exact Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.property)
  }
  let e := MeasurableEquiv.piUnique
    (fun _ : Finset.Iic (0 : ℕ) => JointState S X)
  have h := StrategicWorldModel.pathLaw_prefix_zero M mu0
  change
    (M.pathLaw mu0).map (Preorder.frestrictLe 0) =
      mu0.map e.symm at h
  calc
    (M.pathLaw mu0).map (fun w : ℕ → JointState S X => w 0) =
        ((M.pathLaw mu0).map (Preorder.frestrictLe 0)).map e := by
      rw [Measure.map_map e.measurable (by fun_prop)]
      congr 1
    _ = (mu0.map e.symm).map e := by rw [h]
    _ = mu0 := by
      rw [Measure.map_map e.measurable e.symm.measurable]
      simpa using (Measure.map_id mu0)

/-- Point-initialized finite-horizon survival probability. -/
noncomputable def survivalProbability
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X) (n : ℕ) : ℝ≥0∞ :=
  M.pathLaw (Measure.dirac y) (survivesThroughSet spec n)

/-- Point-initialized indefinite-retention probability. -/
noncomputable def survivalForeverProbability
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X) : ℝ≥0∞ :=
  M.pathLaw (Measure.dirac y) (survivesForeverSet spec)

end RegimeSpecification

end PermanssonLean
