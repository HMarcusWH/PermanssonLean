import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Algebra.Order.Ring.Pow

open MeasureTheory ProbabilityTheory Set

namespace PermanssonLean

/-!
# Event total variation and Proposition 5.4 arithmetic

The paper uses the probability-theory convention

`||μ - ν||_TV = sup_A |μ(A) - ν(A)|`

rather than the signed-measure variation norm.  Mathlib does not currently
expose this exact probability-distance object, so we freeze the convention
locally before proving the finite-horizon path envelope.

This file establishes:
* the source-faithful event-supremum total-variation definition;
* its elementary probability-measure bounds and symmetry;
* the kernel-uniform pointwise hypothesis used by Proposition 5.4;
* the geometric envelope `1 - (1 - ε)^T`;
* Bernoulli's inequality `1 - (1 - ε)^T ≤ T ε`.

The kernel-to-path propagation theorem itself is intentionally left to the
next layer; no claim is upgraded to PROVED merely by introducing this support
infrastructure.
-/

namespace ProbabilitySupport

universe uΩ uY

variable {Ω : Type uΩ} {Y : Type uY}
variable [MeasurableSpace Ω] [MeasurableSpace Y]

/-- Candidate event discrepancies used by the paper's total-variation
convention. -/
def eventTVCandidates (μ ν : Measure Ω) : Set ℝ :=
  {r | ∃ s : Set Ω, MeasurableSet s ∧ r = |μ.real s - ν.real s|}

/-- Probability total variation in the paper's convention:
`sup_A |μ(A) - ν(A)|`, with the supremum taken over measurable events. -/
noncomputable def eventTotalVariation (μ ν : Measure Ω) : ℝ :=
  sSup (eventTVCandidates μ ν)

theorem eventTVCandidates_nonempty (μ ν : Measure Ω) :
    (eventTVCandidates μ ν).Nonempty := by
  refine ⟨0, ∅, MeasurableSet.empty, ?_⟩
  simp

theorem eventTVCandidates_bddAbove
    (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    BddAbove (eventTVCandidates μ ν) := by
  refine ⟨1, ?_⟩
  intro r hr
  rcases hr with ⟨s, hs, rfl⟩
  have hμ0 : 0 ≤ μ.real s := measureReal_nonneg
  have hν0 : 0 ≤ ν.real s := measureReal_nonneg
  have hμ1 : μ.real s ≤ 1 := measureReal_le_one
  have hν1 : ν.real s ≤ 1 := measureReal_le_one
  rw [abs_le]
  constructor <;> linarith

theorem eventTotalVariation_nonneg
    (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ eventTotalVariation μ ν := by
  unfold eventTotalVariation
  apply le_csSup (eventTVCandidates_bddAbove μ ν)
  exact ⟨∅, MeasurableSet.empty, by simp⟩

theorem eventTotalVariation_le_one
    (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    eventTotalVariation μ ν ≤ 1 := by
  unfold eventTotalVariation
  apply csSup_le (eventTVCandidates_nonempty μ ν)
  intro r hr
  rcases hr with ⟨s, hs, rfl⟩
  have hμ0 : 0 ≤ μ.real s := measureReal_nonneg
  have hν0 : 0 ≤ ν.real s := measureReal_nonneg
  have hμ1 : μ.real s ≤ 1 := measureReal_le_one
  have hν1 : ν.real s ≤ 1 := measureReal_le_one
  rw [abs_le]
  constructor <;> linarith

/-- Every measurable event discrepancy is bounded by event total variation. -/
theorem abs_measureReal_sub_le_eventTotalVariation
    (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s : Set Ω} (hs : MeasurableSet s) :
    |μ.real s - ν.real s| ≤ eventTotalVariation μ ν := by
  unfold eventTotalVariation
  apply le_csSup (eventTVCandidates_bddAbove μ ν)
  exact ⟨s, hs, rfl⟩

theorem eventTotalVariation_symm
    (μ ν : Measure Ω) :
    eventTotalVariation μ ν = eventTotalVariation ν μ := by
  have hsets : eventTVCandidates μ ν = eventTVCandidates ν μ := by
    ext r
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, by rw [abs_sub_comm]⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, by rw [abs_sub_comm]⟩
  unfold eventTotalVariation
  rw [hsets]

theorem eventTotalVariation_self
    (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    eventTotalVariation μ μ = 0 := by
  apply le_antisymm
  · unfold eventTotalVariation
    apply csSup_le (eventTVCandidates_nonempty μ μ)
    intro r hr
    rcases hr with ⟨s, hs, rfl⟩
    simp
  · exact eventTotalVariation_nonneg μ μ

/-- The uniform one-step total-variation hypothesis in Proposition 5.4,
written pointwise rather than as a second explicit supremum over states. -/
def HasUniformEventTVBound
    (K Ktilde : Kernel Y Ω) (ε : ℝ) : Prop :=
  ∀ y, eventTotalVariation (K y) (Ktilde y) ≤ ε

/-- The sharp geometric envelope appearing in Proposition 5.4. -/
def geometricTVEnvelope (ε : ℝ) (T : ℕ) : ℝ :=
  1 - (1 - ε) ^ T

@[simp] theorem geometricTVEnvelope_zero (ε : ℝ) :
    geometricTVEnvelope ε 0 = 0 := by
  simp [geometricTVEnvelope]

@[simp] theorem geometricTVEnvelope_one (ε : ℝ) :
    geometricTVEnvelope ε 1 = ε := by
  simp [geometricTVEnvelope]

theorem geometricTVEnvelope_nonneg
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (T : ℕ) :
    0 ≤ geometricTVEnvelope ε T := by
  have hbase0 : 0 ≤ 1 - ε := by linarith
  have hbase1 : 1 - ε ≤ 1 := by linarith
  have hp0 : 0 ≤ (1 - ε) ^ T := pow_nonneg hbase0 _
  have hp1 : (1 - ε) ^ T ≤ 1 := by
    simpa using (pow_le_one₀ (n := T) hbase0 hbase1)
  unfold geometricTVEnvelope
  linarith

theorem geometricTVEnvelope_le_one
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (T : ℕ) :
    geometricTVEnvelope ε T ≤ 1 := by
  have hbase0 : 0 ≤ 1 - ε := by linarith
  have hp0 : 0 ≤ (1 - ε) ^ T := pow_nonneg hbase0 _
  unfold geometricTVEnvelope
  linarith

/-- Bernoulli's inequality gives the second half of Proposition 5.4:
`1 - (1 - ε)^T ≤ T ε`. -/
theorem geometricTVEnvelope_le_linear
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (T : ℕ) :
    geometricTVEnvelope ε T ≤ (T : ℝ) * ε := by
  have hbase : (-1 : ℝ) ≤ 1 - ε := by linarith
  have hbern :
      1 + (T : ℝ) * ((1 - ε) - 1) ≤ (1 - ε) ^ T :=
    one_add_mul_sub_le_pow hbase T
  unfold geometricTVEnvelope
  linarith

end ProbabilitySupport

end PermanssonLean
