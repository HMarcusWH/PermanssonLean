import PermanssonResearch.Probability.BoundedOrbitAverages
import Mathlib.MeasureTheory.MeasurableSpace.Invariants

namespace PermanssonResearch.Probability.Hopf

open MeasureTheory Set

noncomputable section

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The actual sigma-algebra of ambient measurable sets invariant under the
preimage of the transformation. -/
abbrev invariantSigma (T : Ω → Ω) : MeasurableSpace Ω := MeasurableSpace.invariants T

theorem invariantSigma_le (T : Ω → Ω) : invariantSigma T ≤ mΩ :=
  MeasurableSpace.invariants_le T

theorem measurableSet_invariantSigma {T : Ω → Ω} {s : Set Ω} :
    MeasurableSet[invariantSigma T] s ↔ MeasurableSet s ∧ T ⁻¹' s = s := Iff.rfl

theorem upperAverage_measurable_invariant {T : Ω → Ω} {f : Ω → ℝ}
    (hT : Measurable T) (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ ω, |f ω| ≤ M) : Measurable[invariantSigma T] (upperAverage T f) := by
  apply MeasurableSpace.measurable_invariants_dom.mpr
  refine ⟨upperAverage_measurable hT hf, ?_⟩
  intro s hs
  have hi : upperAverage T f ∘ T = upperAverage T f := by
    funext ω
    exact upperAverage_invariant M hM hb ω
  rw [hi]

end
end PermanssonResearch.Probability.Hopf
