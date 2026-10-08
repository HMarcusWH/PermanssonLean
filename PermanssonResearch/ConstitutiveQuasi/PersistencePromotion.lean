import PermanssonResearch.ConstitutiveQuasi.Robustness
import Mathlib.Tactic

/-!
# CQ-1: promote real-valued survival bounds to the frozen ENNReal persistence gate

A clamped error budget is needed because IsFinitePersistent requires eta <= 1.
No approximate-model persistence is inferred without an explicit real survival
bound, probability mass finiteness, and the frozen region-wide quantifier.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch
namespace ConstitutiveQuasi

universe uS uX uA uH
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]

/-- The real error is clamped to the interval [0,1] before conversion to
the existing finite-persistence error type. -/
noncomputable def clampedPersistenceError (eta : ℝ≥0∞) (e : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (min 1 (eta.toReal + e))

/-- Transfer a region-wide survival floor under an explicit nonnegative
real error, retaining the exact IsFinitePersistent semantics. -/
theorem finitePersistence_of_real_error
    (M : PermanssonLean.StrategicWorldModel S X A)
    (spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H)
    (L : ℕ) (eta : ℝ≥0∞) (heta : eta ≤ 1)
    (e : ℝ) (he : 0 ≤ e)
    (hfloor : ∀ y ∈ spec.region,
      (1 - eta).toReal - e ≤
        (PermanssonLean.RegimeSpecification.survivalProbability M spec y L).toReal) :
    PermanssonLean.RegimeSpecification.IsFinitePersistent M spec L
      (clampedPersistenceError eta e) := by
  let etaStar := clampedPersistenceError eta e
  have hη0 : 0 ≤ eta.toReal := ENNReal.toReal_nonneg
  have hsum : 0 ≤ eta.toReal + e := add_nonneg hη0 he
  have hmin0 : 0 ≤ min (1 : ℝ) (eta.toReal + e) := le_min (by norm_num) hsum
  have hstar_le_one : etaStar ≤ 1 := by
    change ENNReal.ofReal (min 1 (eta.toReal + e)) ≤ 1
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
  have hstar_real : etaStar.toReal = min 1 (eta.toReal + e) := by
    dsimp [etaStar, clampedPersistenceError]
    exact ENNReal.toReal_ofReal hmin0
  have hηreal : (1 - eta).toReal = 1 - eta.toReal := by
    rw [ENNReal.toReal_sub_of_le heta ENNReal.one_ne_top]
    simp
  refine ⟨hstar_le_one, ?_⟩
  intro y hy
  have hfinite :
      PermanssonLean.RegimeSpecification.survivalProbability M spec y L ≠ ⊤ :=
    measure_ne_top (M.pathLaw (Measure.dirac y))
      (PermanssonLean.RegimeSpecification.survivesThroughSet spec L)
  apply (ENNReal.toReal_le_toReal (by
    exact ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤)
      (tsub_le_self : 1 - etaStar ≤ 1)) hfinite).1
  rw [ENNReal.toReal_sub_of_le hstar_le_one ENNReal.one_ne_top]
  simp only [ENNReal.toReal_one, hstar_real]
  have hlow := hfloor y hy
  rw [hηreal] at hlow
  have hprob :
      0 ≤ (PermanssonLean.RegimeSpecification.survivalProbability M spec y L).toReal :=
    ENNReal.toReal_nonneg
  rcases le_total 1 (eta.toReal + e) with hlarge | hsmall
  · rw [min_eq_left hlarge]
    linarith
  · rw [min_eq_right hsmall]
    linarith

end ConstitutiveQuasi
end PermanssonResearch
