import PermanssonResearch.RegimeExit.StopHistory
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Tactic

/-!
# C-Exit C — infinite future shifted from an observed finite history

A canonical stationary chain conditioned on a full history has a genuine
probability kernel of future paths, with the first future coordinate
equal to the current history endpoint. This is an exact WHOLE-PATH
factorization. It does not yet prove that the law is independent
of the earlier history given only the final state.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit

set_option autoImplicit false
open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA
variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

/-- The true infinite-future kernel after observing an absolute-time
history through m. It starts with the state at time m. -/
noncomputable def canonicalShiftedHistoryKernel
    (N : StrategicWorldModel S X A) (m : ℕ) :
    Kernel ((i : Finset.Iic m) → JointState S X)
      (ℕ → JointState S X) :=
  (canonicalHistoryContinuation N m).map
    (pathTailShift (S := S) (X := X) m)

/-- State-valued history kernels yield actual probability measures
on entire infinite future paths. -/
instance canonicalShiftedHistoryKernel_isMarkov
    (N : StrategicWorldModel S X A) (m : ℕ) :
    IsMarkovKernel (canonicalShiftedHistoryKernel N m) := by
  unfold canonicalShiftedHistoryKernel
  exact IsMarkovKernel.map
    (canonicalHistoryContinuation N m)
    (measurable_pathTailShift (S := S) (X := X) m)

/-- The observed prefix and *shifted* entire future have exactly
the distribution obtained by composing the observed prefix marginal
with the shifted Ionescu--Tulcea continuation kernel. -/
theorem pointPathLaw_shifted_history_joint
    (N : StrategicWorldModel S X A)
    (z : JointState S X) (m : ℕ) :
    (N.pathLaw (Measure.dirac z)).map
      (fun w : ℕ → JointState S X =>
        (Preorder.frestrictLe m w,
          pathTailShift (S := S) (X := X) m w)) =
    ((N.pathLaw (Measure.dirac z)).map
        (Preorder.frestrictLe m)) ⊗ₘ
      canonicalShiftedHistoryKernel N m := by
  let P := N.pathLaw (Measure.dirac z)
  let μ := P.map (Preorder.frestrictLe m)
  let κ := canonicalHistoryContinuation N m
  let shift := pathTailShift (S := S) (X := X) m
  have hShift : Measurable shift :=
    measurable_pathTailShift (S := S) (X := X) m
  have hProd : Measurable (Prod.map id shift) :=
    measurable_id.prodMap hShift
  calc
    P.map (fun w : ℕ → JointState S X =>
        (Preorder.frestrictLe m w, shift w)) =
      (P.map (fun w : ℕ → JointState S X =>
        (Preorder.frestrictLe m w, w))).map
          (Prod.map id shift) := by
        rw [Measure.map_map hProd (by fun_prop)]
        rfl
    _ = (μ ⊗ₘ κ).map (Prod.map id shift) := by
        rw [pointPathLaw_history_joint N z m]
    _ = μ ⊗ₘ κ.map shift :=
        (Measure.compProd_map
          (measurable_pathTailShift (S := S) (X := X) m)).symm

end PermanssonResearch.RegimeExit
