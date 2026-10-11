import PermanssonResearch.MultipleLimit.TypedTerminalEndpointLaw
import PermanssonResearch.MultipleLimit.TypedInitialMixture
import PermanssonLean.Regime.ExitTime
import Mathlib.Tactic

/-!
# Lane C1 — terminal weights for arbitrary initial laws

All terminal events refer to the actual infinite alpha/P/U path law.  The
point-started a/b results below follow from the canonical time-zero marginal
and the already-certified absorbing continuation.  Mixed laws are then
derived using the genuine infinite-path initial-mixture theorem.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace TypedTerminalMixture

open TypedStrategicWitness TypedAlmostSureAbsorption
open TypedAbsorbingContinuation TypedTerminalEndpointLaw
open TypedInitialMixture
open PermanssonLean

noncomputable section

/-- Under the genuine canonical law, time zero equals a deterministic start. -/
private theorem starts_at_ae (z : Y) :
    ∀ᵐ w ∂model.pathLaw (Measure.dirac z), w 0 = z := by
  rw [ae_iff]
  change model.pathLaw (Measure.dirac z)
    {w : ℕ → Y | w 0 ≠ z} = 0
  have hset : {w : ℕ → Y | w 0 ≠ z} =
      (fun w : ℕ → Y => w 0) ⁻¹' ({z} : Set Y)ᶜ := by
    ext w
    simp
  rw [hset, ← Measure.map_apply (measurable_pi_apply 0)
    (measurableSet_singleton z).compl]
  rw [PermanssonLean.RegimeSpecification.StrategicWorldModel.pathLaw_eval_zero]
  simp

/-- A path started at an absorbing point has that exact terminal
destination almost surely, including when absorption occurs at time zero. -/
theorem terminal_eq_start_ae (z : Y) (hz : z = a ∨ z = b) :
    ∀ᵐ w ∂model.pathLaw (Measure.dirac z),
      terminalDestination w = z := by
  filter_upwards [starts_at_ae z,
    stays_after_absorbing_ae
      (⟨Measure.dirac z, inferInstance⟩ : ProbabilityMeasure Y)] with w hzero hstay
  have hzmem : z ∈ ({a, b} : Finset Y) := by
    rcases hz with rfl | rfl <;> simp
  have hfixed : EventuallyAt w z :=
    ⟨0, fun n hn => by simpa [hzero] using hstay 0 (by simpa [hzero] using hzmem) n hn⟩
  have hgood : EventuallyAt w a ∨ EventuallyAt w b := by
    rcases hz with rfl | rfl
    · exact Or.inl hfixed
    · exact Or.inr hfixed
  exact eventuallyAt_unique (terminalDestination_correct w hgood) hfixed

/-- A point-started absorbing state gives a 0/1 law for each terminal event. -/
theorem terminal_point_weight (z dest : Y) (hz : z = a ∨ z = b) :
    model.pathLaw (Measure.dirac z)
      {w : ℕ → Y | terminalDestination w = dest} =
      if z = dest then 1 else 0 := by
  have heq := terminal_eq_start_ae z hz
  by_cases h : z = dest
  · subst dest
    have hevents :
        {w : ℕ → Y | terminalDestination w = z} =ᵐ[model.pathLaw (Measure.dirac z)]
          (Set.univ : Set (ℕ → Y)) := by
      filter_upwards [heq] with w hw
      simp [hw]
    simpa using (measure_congr hevents).trans (measure_univ)
  · have hevents :
        {w : ℕ → Y | terminalDestination w = dest} =ᵐ[model.pathLaw (Measure.dirac z)]
          (∅ : Set (ℕ → Y)) := by
      filter_upwards [heq] with w hw
      simp [hw, h]
    simpa [h] using (measure_congr hevents).trans (measure_empty)

/-- Exact conditional endpoint-a mass of each initial point. -/
theorem terminal_point_a (z : Y) :
    model.pathLaw (Measure.dirac z)
      {w : ℕ → Y | terminalDestination w = a} =
      if z = a then 1 else if z = b then 0 else (1/3 : ℝ≥0∞) := by
  rcases z with ⟨zs, zx⟩
  cases zs <;> cases zx
  · simpa [t, u, a, b] using terminal_a_weight_t
  · simpa [t, u, a, b] using terminal_a_weight_u
  · simpa [t, u, a, b] using
      (terminal_point_weight a a (Or.inl rfl))
  · simpa [t, u, a, b] using
      (terminal_point_weight b a (Or.inr rfl))

/-- Exact conditional endpoint-b mass of each initial point. -/
theorem terminal_point_b (z : Y) :
    model.pathLaw (Measure.dirac z)
      {w : ℕ → Y | terminalDestination w = b} =
      if z = b then 1 else if z = a then 0 else (2/3 : ℝ≥0∞) := by
  rcases z with ⟨zs, zx⟩
  cases zs <;> cases zx
  · simpa [t, u, a, b] using
      (terminal_b_weight_t.trans
        (by norm_num : ENNReal.ofReal (2/3 : ℝ) = (2/3 : ℝ≥0∞)))
  · simpa [t, u, a, b] using
      (terminal_b_weight_u.trans
        (by norm_num : ENNReal.ofReal (2/3 : ℝ) = (2/3 : ℝ≥0∞)))
  · simpa [t, u, a, b] using
      (terminal_point_weight a b (Or.inl rfl))
  · simpa [t, u, a, b] using
      (terminal_point_weight b b (Or.inr rfl))

/-- The terminal-a weight of an *arbitrary* initial law, without assuming
a point start or an exogenous endpoint distribution. -/
theorem terminal_a_weight_initial (μ : ProbabilityMeasure Y) :
    model.pathLaw μ.toMeasure
      {w : ℕ → Y | terminalDestination w = a} =
      ∑ y : Y, μ.toMeasure {y} *
        (if y = a then 1 else if y = b then 0 else (1/3 : ℝ≥0∞)) := by
  calc
    model.pathLaw μ.toMeasure
        {w : ℕ → Y | terminalDestination w = a} =
      ∑ y : Y, μ.toMeasure {y} *
        model.pathLaw (Measure.dirac y)
          {w : ℕ → Y | terminalDestination w = a} :=
      typed_pathLaw_event_initial_mixture μ _
        ((measurableSet_singleton a).preimage measurable_terminalDestination)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      rw [terminal_point_a y]

/-- Similarly, arbitrary-start terminal-b probability is completely known. -/
theorem terminal_b_weight_initial (μ : ProbabilityMeasure Y) :
    model.pathLaw μ.toMeasure
      {w : ℕ → Y | terminalDestination w = b} =
      ∑ y : Y, μ.toMeasure {y} *
        (if y = b then 1 else if y = a then 0 else (2/3 : ℝ≥0∞)) := by
  calc
    model.pathLaw μ.toMeasure
        {w : ℕ → Y | terminalDestination w = b} =
      ∑ y : Y, μ.toMeasure {y} *
        model.pathLaw (Measure.dirac y)
          {w : ℕ → Y | terminalDestination w = b} :=
      typed_pathLaw_event_initial_mixture μ _
        ((measurableSet_singleton b).preimage measurable_terminalDestination)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      rw [terminal_point_b y]

/-- Closed-form terminal-a weight for an arbitrary starting probability law
on the genuine four-state model. -/
theorem terminal_a_weight_closed (μ : ProbabilityMeasure Y) :
    model.pathLaw μ.toMeasure
      {w : ℕ → Y | terminalDestination w = a} =
    μ.toMeasure {a} +
      (μ.toMeasure {t} + μ.toMeasure {u}) * (1/3 : ℝ≥0∞) := by
  rw [terminal_a_weight_initial]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp [t, u, a, b]
  ring

/-- Closed-form terminal-b weight for the same arbitrary initial law. -/
theorem terminal_b_weight_closed (μ : ProbabilityMeasure Y) :
    model.pathLaw μ.toMeasure
      {w : ℕ → Y | terminalDestination w = b} =
    μ.toMeasure {b} +
      (μ.toMeasure {t} + μ.toMeasure {u}) * (2/3 : ℝ≥0∞) := by
  rw [terminal_b_weight_initial]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp [t, u, a, b]
  ring

end
end TypedTerminalMixture
end MultipleLimit
end PermanssonResearch
