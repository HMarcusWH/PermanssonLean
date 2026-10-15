import PermanssonResearch.RegimeExit.FiniteHistoryTail
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Tactic

/-!
# C-Exit C — all-measurable future-event continuation from finite histories

A probability law on infinite paths can be conditioned against an actual
finite prefix via the Ionescu--Tulcea continuation kernel. The future
test event A below is ANY measurable set of infinite full paths, not just
a finite cylinder. This result is for absolute-time future paths;
the stationary shift-to-last-state reduction remains OPEN.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit

set_option autoImplicit false
open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA
variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

/-- Exact distribution of an infinite-path event intersected with an
arbitrary finite-history event. The right-hand side is an actual
integral over the genuine prefix law, not a normalized guess. -/
theorem pointPathLaw_history_event
    (N : StrategicWorldModel S X A)
    (z : JointState S X) (m : ℕ)
    (H : Set ((i : Finset.Iic m) → JointState S X))
    (F : Set (ℕ → JointState S X))
    (hH : MeasurableSet H) (hF : MeasurableSet F) :
    N.pathLaw (Measure.dirac z)
      {w : ℕ → JointState S X |
        Preorder.frestrictLe m w ∈ H ∧ w ∈ F} =
      ∫⁻ h in H, (canonicalHistoryContinuation N m h) F
        ∂((N.pathLaw (Measure.dirac z)).map
          (Preorder.frestrictLe m)) := by
  let P := N.pathLaw (Measure.dirac z)
  let μ := P.map (Preorder.frestrictLe m)
  let κ := canonicalHistoryContinuation N m
  calc
    P {w : ℕ → JointState S X |
        Preorder.frestrictLe m w ∈ H ∧ w ∈ F} =
      (P.map (fun w : ℕ → JointState S X =>
        (Preorder.frestrictLe m w, w))) (H ×ˢ F) := by
      rw [Measure.map_apply (by fun_prop) (hH.prod hF)]
      rfl
    _ = (μ ⊗ₘ κ) (H ×ˢ F) := by
      exact congrArg (fun q : Measure
        (((i : Finset.Iic m) → JointState S X) ×
          (ℕ → JointState S X)) => q (H ×ˢ F))
            (pointPathLaw_history_joint N z m)
    _ = ∫⁻ h in H, κ h F ∂μ := by
      exact Measure.compProd_apply_prod hH hF

end PermanssonResearch.RegimeExit
