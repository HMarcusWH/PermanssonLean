import PermanssonResearch.MultipleLimit.CanonicalClassWeights
import PermanssonResearch.MultipleLimit.CanonicalClassContinuation
import PermanssonResearch.MultipleLimit.FiniteCanonicalPath
import Mathlib.Tactic

/-!
# C10 — native infinite-path class selection equals eventual closed-class hitting

A generic finite-state result on the ACTUAL canonical Ionescu–Tulcea path
law, valid for arbitrary probability kernels and closed state subsets.
It does not assume rationality or finite-horizon approximation. On the
probability-one eventual-recurrent-residence event, a trajectory has ever
entered a closed set precisely when its selected terminal class lies there.
This is a step toward the numerical absorption/semantic correspondence;
the subsequent first-step harmonicity and Dirichlet uniqueness connection
must still be proved, and are NOT consequences of this statement alone.
-/

open MeasureTheory ProbabilityTheory Filter

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

open PermanssonResearch.MultipleLimit.KernelCommunication
open PermanssonResearch.MultipleLimit.CanonicalClassSelector
open PermanssonResearch.MultipleLimit.CanonicalClassContinuation
open PermanssonResearch.MultipleLimit.CanonicalClassWeights
open PermanssonResearch.MultipleLimit.FiniteCanonicalPath

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [Nonempty Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- A selected final class belongs to an exact closed target iff some
finite-time state actually entered that target, canonical almost surely. -/
theorem selected_in_closed_iff_ever_hit_ae
    (C : Set Y) (hclosed : ClosedSubset K C)
    (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      (selectedRepresentative K w ∈ C ↔ ∃ n : ℕ, w n ∈ C) := by
  filter_upwards
    [selected_class_eventual_ae K μ,
     closed_stay_after_entry_ae K μ C hclosed]
    with w hsel hstay
  constructor
  · intro hs
    obtain ⟨N,hN⟩ := hsel
    have hreach : Reachable K (selectedRepresentative K w) (w N) :=
      (hN N le_rfl).1
    exact ⟨N, closed_reachable K hclosed hs hreach⟩
  · rintro ⟨n,hn⟩
    obtain ⟨N,hN⟩ := hsel
    let m := max n N
    have hC : w m ∈ C := hstay n hn m (Nat.le_max_left _ _)
    have hback : Reachable K (w m) (selectedRepresentative K w) :=
      (hN m (Nat.le_max_right _ _)).2
    exact closed_reachable K hclosed hC hback

/-- Equality of the actual infinite-path event probabilities; the
canonical representative is never reused across distinct kernels. -/
theorem canonical_selected_closed_mass_eq_ever_hit
    (C : Set Y) (hclosed : ClosedSubset K C) (y : Y) :
    (canonicalPathLaw K (Measure.dirac y))
        ((selectedRepresentative K) ⁻¹' C) =
    (canonicalPathLaw K (Measure.dirac y))
        {w : ℕ → Y | ∃ n : ℕ, w n ∈ C} := by
  let P := canonicalPathLaw K (Measure.dirac y)
  have hprob := selected_in_closed_iff_ever_hit_ae K C hclosed
    (diracProba y)
  change ∀ᵐ w ∂P, (_ ↔ _) at hprob
  exact measure_congr (by
    filter_upwards [hprob] with w hw
    exact propext hw)

end C10
end ReverseSolver
end PermanssonResearch