import PermanssonResearch.MultipleLimit.TypedCanonicalHitting
import PermanssonResearch.MultipleLimit.TypedInitialMixture
import PermanssonResearch.MultipleLimit.EventualHittingFromLimits
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Lane C1 — unconditional finite hitting for the literal alpha/P/U process

The exact rational finite-horizon hitting values have already been
transferred to the actual canonical infinite path law. Here their proven
geometric limit, without any independence assumption, makes the
never-hit event null, first at every physical point start and then at
all initial probability laws by the certified canonical mixture identity.

Permanent absorbing continuation and the random terminal occupation law
are separate obligations.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace TypedEventualHitting

open TypedStrategicWitness TypedCanonicalHitting
open ExactRationalAbsorption
open PermanssonResearch.ReverseSolver

noncomputable section

def absorbingSet : Finset Y := {a, b}

def hitEvent (T : ℕ) : Set (ℕ → Y) :=
  (Preorder.frestrictLe T) ⁻¹'
    successPrefixEvent (typedTarget absorbingTarget) T

theorem hitEvent_measurable (T : ℕ) : MeasurableSet (hitEvent T) :=
  (measurableSet_successPrefixEvent (typedTarget absorbingTarget) T).preimage
    (Preorder.measurable_frestrictLe T)

/-- The frozen hitting target is literally the two absorbing states,
not a numerically similar invented target. -/
theorem targetGoal_eq_absorbingSet :
    (typedTarget absorbingTarget).goal = (absorbingSet : Set Y) := by
  ext z
  rcases z with ⟨s, x⟩
  cases s <;> cases x <;> decide

theorem neverHit_subset_success_compl (T : ℕ) :
    NeverHit absorbingSet ⊆ (hitEvent T)ᶜ := by
  intro w hw hhit
  change Preorder.frestrictLe T w ∈
    successPrefixEvent (typedTarget absorbingTarget) T at hhit
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hhit
  have hgoal : (Preorder.frestrictLe T w) i ∈
      (typedTarget absorbingTarget).goal := hi.1
  change w (i : ℕ) ∈ (typedTarget absorbingTarget).goal at hgoal
  rw [targetGoal_eq_absorbingSet] at hgoal
  exact hw (i : ℕ) hgoal

private theorem half_power_tends_zero :
    Tendsto (fun T : ℕ => (1/2 : ℝ)^T) atTop (𝓝 (0 : ℝ)) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem point_hitting_u_real (T : ℕ) :
    (model.pathLaw (Measure.dirac u)).real (hitEvent T) =
      1 - (1/2 : ℝ)^T := by
  have hh := typed_u_absorption_hitting_all_horizons T
  change (model.pathLaw (Measure.dirac u)).real (hitEvent T) = _ at hh
  calc
    (model.pathLaw (Measure.dirac u)).real (hitEvent T) =
      ((1 - (1/2 : ℚ)^T : ℚ) : ℝ) := hh
    _ = 1 - (1/2 : ℝ)^T := by norm_num

theorem point_hitting_t_real (T : ℕ) :
    (model.pathLaw (Measure.dirac t)).real (hitEvent (T+1)) =
      1 - (1/2 : ℝ)^T := by
  have hh := typed_t_absorption_hitting_all_horizons T
  change (model.pathLaw (Measure.dirac t)).real (hitEvent (T+1)) = _ at hh
  calc
    (model.pathLaw (Measure.dirac t)).real (hitEvent (T+1)) =
      ((1 - (1/2 : ℚ)^T : ℚ) : ℝ) := hh
    _ = 1 - (1/2 : ℝ)^T := by norm_num

theorem point_hitting_a_real (T : ℕ) :
    (model.pathLaw (Measure.dirac a)).real (hitEvent T) = 1 := by
  unfold hitEvent
  rw [typed_pathLaw_hitting_real]
  have h := congrArg (fun q : ℚ => (q : ℝ)) (hitting_a_all T)
  simpa [a, codeState] using h

theorem point_hitting_b_real (T : ℕ) :
    (model.pathLaw (Measure.dirac b)).real (hitEvent T) = 1 := by
  unfold hitEvent
  rw [typed_pathLaw_hitting_real]
  have h := congrArg (fun q : ℚ => (q : ℝ)) (hitting_b_all T)
  simpa [b, codeState] using h

theorem never_hit_from_u_null :
    model.pathLaw (Measure.dirac u) (NeverHit absorbingSet) = 0 := by
  apply EventualHittingFromLimits.null_of_success_probability_tendsto_one
    (model.pathLaw (Measure.dirac u)) (NeverHit absorbingSet)
    hitEvent hitEvent_measurable neverHit_subset_success_compl
  have hp := half_power_tends_zero
  have hlim : Tendsto
      (fun T : ℕ => 1 - (1/2 : ℝ)^T) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub hp
  simpa only [point_hitting_u_real] using hlim

theorem never_hit_from_t_null :
    model.pathLaw (Measure.dirac t) (NeverHit absorbingSet) = 0 := by
  apply EventualHittingFromLimits.null_of_success_probability_tendsto_one
    (model.pathLaw (Measure.dirac t)) (NeverHit absorbingSet)
    (fun T => hitEvent (T+1))
    (fun T => hitEvent_measurable (T+1))
    (fun T => neverHit_subset_success_compl (T+1))
  have hp := half_power_tends_zero
  have hlim : Tendsto
      (fun T : ℕ => 1 - (1/2 : ℝ)^T) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub hp
  simpa only [point_hitting_t_real] using hlim

theorem never_hit_from_a_null :
    model.pathLaw (Measure.dirac a) (NeverHit absorbingSet) = 0 := by
  apply EventualHittingFromLimits.null_of_success_probability_tendsto_one
    (model.pathLaw (Measure.dirac a)) (NeverHit absorbingSet)
    hitEvent hitEvent_measurable neverHit_subset_success_compl
  simp_rw [point_hitting_a_real]
  exact tendsto_const_nhds

theorem never_hit_from_b_null :
    model.pathLaw (Measure.dirac b) (NeverHit absorbingSet) = 0 := by
  apply EventualHittingFromLimits.null_of_success_probability_tendsto_one
    (model.pathLaw (Measure.dirac b)) (NeverHit absorbingSet)
    hitEvent hitEvent_measurable neverHit_subset_success_compl
  simp_rw [point_hitting_b_real]
  exact tendsto_const_nhds

/-- Every pure physical initial state hits a or b almost surely. -/
theorem never_hit_point_null (y : Y) :
    model.pathLaw (Measure.dirac y) (NeverHit absorbingSet) = 0 := by
  rcases y with ⟨ys, yx⟩
  cases ys <;> cases yx
  · exact never_hit_from_t_null
  · exact never_hit_from_u_null
  · exact never_hit_from_a_null
  · exact never_hit_from_b_null

/-- Exact arbitrary initial-law mixture closes the all-starting-law case.
No point-start/mixture promotion is assumed as an axiom. -/
theorem never_hit_initial_null (μ : ProbabilityMeasure Y) :
    model.pathLaw μ.toMeasure (NeverHit absorbingSet) = 0 := by
  rw [TypedInitialMixture.typed_pathLaw_event_initial_mixture
    μ (NeverHit absorbingSet) (neverHit_measurable absorbingSet)]
  simp [never_hit_point_null]

theorem canonical_eventually_hits_ae (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂model.pathLaw μ.toMeasure,
      ∃ T : ℕ, w T ∈ absorbingSet := by
  rw [ae_iff]
  have heq :
      {w : ℕ → Y | ¬ ∃ T : ℕ, w T ∈ absorbingSet} =
        NeverHit absorbingSet := by
    ext w
    simp [NeverHit]
  rw [heq]
  exact never_hit_initial_null μ

end
end TypedEventualHitting
end MultipleLimit
end PermanssonResearch
