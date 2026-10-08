import PermanssonResearch.ConstitutiveQuasi.PathOutput
import PermanssonResearch.ConstitutiveQuasi.BoundedTV

/-!
# CQ-1 finite-prefix regression theorems

These are positive boundary/sanity checks, not yet a complete adversarial
counterexample catalogue for the full constitutive quasi-regime certificate.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace ConstitutiveQuasi

universe uY
variable {Y : Type uY} [MeasurableSpace Y]

/-- At zero transitions, the initial state alone determines the score. -/
theorem expected_zero_independent_of_kernel
    (K Ktilde : Kernel Y Y) [IsMarkovKernel K] [IsMarkovKernel Ktilde]
    (y : Y) (f : FinitePathProperty Y 0) :
    f.fromKernel 0 K y = f.fromKernel 0 Ktilde y := by
  unfold FinitePathProperty.fromKernel
  rw [PermanssonLean.ProbabilitySupport.finitePrefixLaw_zero_eq K Ktilde y]

/-- A single transition has exactly the one-step TV error envelope. -/
theorem expected_one_le_uniformTV
    [MeasurableSpace.CountableOrCountablyGenerated Y Y]
    (K Ktilde : Kernel Y Y) [IsMarkovKernel K] [IsMarkovKernel Ktilde]
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hTV : PermanssonLean.ProbabilitySupport.HasUniformEventTVBound K Ktilde δ)
    (y : Y) (f : FinitePathProperty Y 1) :
    |f.fromKernel 1 K y - f.fromKernel 1 Ktilde y| ≤ δ := by
  simpa using finitePathExpectation_abs_le_geometric
    K Ktilde hδ0 hδ1 hTV y 1 f

end ConstitutiveQuasi
end PermanssonResearch
