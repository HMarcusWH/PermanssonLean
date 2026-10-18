import PermanssonResearch.MultipleLimit.FiniteCanonicalPath
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-! Absolute continuity is proved for the complete infinite canonical path
law by its actual initial-law composition, hence transfers every almost-sure
statement, without requiring a finite-state or positive-atom assumption. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultipleLimit.CanonicalInitial

variable {Y : Type*} [MeasurableSpace Y]

theorem pathLaw_absolutelyContinuous (K : Kernel Y Y) [IsMarkovKernel K]
    (μ π : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (h : μ ≪ π) :
    FiniteCanonicalPath.canonicalPathLaw K μ ≪ FiniteCanonicalPath.canonicalPathLaw K π := by
  unfold FiniteCanonicalPath.canonicalPathLaw Kernel.trajMeasure
  exact (h.map (MeasurableEquiv.measurable _)).comp_right _

theorem pathLaw_ae_transfer (K : Kernel Y Y) [IsMarkovKernel K]
    (μ π : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (h : μ ≪ π) (p : (ℕ → Y) → Prop)
    (hp : ∀ᵐ w ∂FiniteCanonicalPath.canonicalPathLaw K π, p w) :
    ∀ᵐ w ∂FiniteCanonicalPath.canonicalPathLaw K μ, p w :=
  (pathLaw_absolutelyContinuous K μ π h).ae_le hp

end PermanssonResearch.MultipleLimit.CanonicalInitial
