import PermanssonResearch.ReverseSolver.TypedMenuCertification
import Mathlib.Tactic

/-!
# D0-F: end-to-end typed finite-menu certificate

A single proof-carrying interface to the existing D0-E theorems.
This is a *theorem* about the constructed rational strategic-world family,
not a proof that a Python JSON report has been decoded into Lean terms.
The finite list fixes stationary interventions for the whole horizon;
there is no D1 feedback policy and no unlisted-model optimality claim.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace EndToEndCertificate

open PermanssonLean
open TypedMenuCertification
open FiniteStrategicRealization
open FiniteStrategicPathBridge

universe uI

/-- Fully bundled D0 certificate for the selected fixed intervention:
eligibility, maximal canonical typed hitting value over the complete listed
menu, exact correspondence with the rational value, and preservation of
both structural world transition P and strategic update U.
No external "exact_values" assumption enters this theorem. -/
theorem selected_end_to_end {I : Type uI} [DecidableEq I] {n : ℕ}
    (baseline : RationalMarkovMatrix n)
    (rational : RationalMatrixMenu I n)
    (rt : RationalHittingTarget n) (x : Fin n) (T : ℕ) :
    let selected := selectRationalMember rational rt x T
    let typed := typedFiniteMenu baseline rational
    (selected ∈ typed.indices) ∧
    (∀ j ∈ typed.indices,
      memberValue typed (typedTarget rt) (decode x) T j ≤
        memberValue typed (typedTarget rt) (decode x) T selected) ∧
    ((rationalMemberValue rational rt x T selected : ℝ) =
      memberValue typed (typedTarget rt) (decode x) T selected) ∧
    ((typed.choice selected).intervention.apply.world =
      (realizedModel baseline).world) ∧
    ((typed.choice selected).intervention.apply.generator.update =
      (realizedModel baseline).generator.update) := by
  dsimp
  exact ⟨
    certifiedSelected_mem baseline rational rt x T,
    certifiedSelected_dominatesTyped baseline rational rt x T,
    certifiedSelected_exactValue baseline rational rt x T,
    certifiedSelected_preserves_world baseline rational rt x T,
    certifiedSelected_preserves_update baseline rational rt x T
  ⟩

end EndToEndCertificate
end ReverseSolver
end PermanssonResearch
