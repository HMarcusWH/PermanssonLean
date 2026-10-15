import PermanssonResearch.RegimeExit.ShiftedHistoryJoint
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Tactic

/-!
# C-Exit C — arbitrary future events on actual first-exit trajectories

The first-exit event is a finite prefix event, and the future-path
observable is shifted at the same n+1 time. The exact stopped-event
probability is therefore an integral over the prefix-conditioned
canonical infinite-future kernel. No independence assumption,
last-state kernel substitution, or conditional normalization is used.

The stronger endpoint-only mixture is STILL OPEN until the
stationary last-state reduction is proved.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit

set_option autoImplicit false
open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA uH
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X]
variable [MeasurableSpace A] [MeasurableSpace H]

/-- Correct stopped-path future identity, still indexed by the
ENTIRE measurable first-exit prefix. The test F is arbitrary in
the σ-algebra of infinite paths. This is not yet the stronger
state-only strong-Markov formula. -/
theorem firstExit_shifted_history_future_integral
    (N : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) (y : JointState S X)
    (D : Set (JointState S X)) (hD : MeasurableSet D)
    (F : Set (ℕ → JointState S X)) (hF : MeasurableSet F) :
    N.pathLaw (Measure.dirac y)
      (firstExitAtDestination spec n D ∩
        (pathTailShift (S := S) (X := X) (n+1)) ⁻¹' F) =
    ∫⁻ h in firstExitHistoryAt spec n D,
      (canonicalShiftedHistoryKernel N (n+1) h) F
      ∂((N.pathLaw (Measure.dirac y)).map
        (Preorder.frestrictLe (n+1))) := by
  let P := N.pathLaw (Measure.dirac y)
  let μ := P.map (Preorder.frestrictLe (n+1))
  let G := firstExitHistoryAt spec n D
  let K := canonicalShiftedHistoryKernel N (n+1)
  let shift := pathTailShift (S := S) (X := X) (n+1)
  have hG : MeasurableSet G :=
    firstExitHistoryAt_measurable spec n D hD
  calc
    P (firstExitAtDestination spec n D ∩ shift ⁻¹' F) =
      (P.map (fun w : ℕ → JointState S X =>
        (Preorder.frestrictLe (n+1) w, shift w))) (G ×ˢ F) := by
      rw [Measure.map_apply (by fun_prop) (hG.prod hF)]
      rw [firstExitAt_eq_history_preimage]
      rfl
    _ = (μ ⊗ₘ K) (G ×ˢ F) := by
      exact congrArg (fun q : Measure
        (((i : Finset.Iic (n+1)) → JointState S X) ×
          (ℕ → JointState S X)) => q (G ×ˢ F))
        (pointPathLaw_shifted_history_joint N y (n+1))
    _ = ∫⁻ h in G, K h F ∂μ := by
      exact Measure.compProd_apply_prod hG hF

/-- Countable sum of correct actual first-exit future probabilities
equals the corresponding countable sum of unnormalized history
continuations. This is NOT yet the endpoint-only routing mixture. -/
theorem firstExit_shifted_history_future_tsum
    (N : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X)
    (D : Set (JointState S X)) (hD : MeasurableSet D)
    (F : Set (ℕ → JointState S X)) (hF : MeasurableSet F) :
    (∑' n : ℕ,
      N.pathLaw (Measure.dirac y)
        (firstExitAtDestination spec n D ∩
          (pathTailShift (S := S) (X := X) (n+1)) ⁻¹' F)) =
    ∑' n : ℕ,
      ∫⁻ h in firstExitHistoryAt spec n D,
        (canonicalShiftedHistoryKernel N (n+1) h) F
        ∂((N.pathLaw (Measure.dirac y)).map
          (Preorder.frestrictLe (n+1))) := by
  apply tsum_congr
  intro n
  exact firstExit_shifted_history_future_integral
    N spec n y D hD F hF

end PermanssonResearch.RegimeExit
