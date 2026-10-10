import PermanssonResearch.ReverseSolver.HistoryTypedFeedback
import PermanssonResearch.ReverseSolver.FiniteStrategicPathBridge
import Mathlib.Tactic

/-!
# D1-D2: genuine history-conditioned canonical strategic-world kernels

For every typed observed prefix select the admissible feedback model for
THAT history; sample from its actual alpha -> P -> U inducedKernel. The
physical world-transition P and strategic update U remain unchanged.
This is a controlled trajectory, NOT one frozen strategic intervention.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace HistoryDependentTyped

open HistoryDependent ControlledKernel FiniteStrategicRealization
open FiniteStrategicPathBridge PermanssonLean

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov
universe uC

abbrev TypedHistory (n i : ℕ) :=
  (j : Finset.Iic i) → JointState Unit (Fin n)

/-- A genuine typed alpha/P/U model selected from all observed history. -/
noncomputable def historySelectedModel
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D i : ℕ) (H : TypedHistory n i) :=
  feedbackModel sys
    (historyFeedback sys σ D i (prefixEncode i H))

/-- World transition P is always the baseline primitive. -/
theorem historySelected_world_fixed
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D i : ℕ) (H : TypedHistory n i) :
    (historySelectedModel sys σ D i H).world =
      (realizedModel sys.baseline).world :=
  feedback_preserves_world sys (historyFeedback sys σ D i (prefixEncode i H))

/-- Strategic update U is always the baseline primitive. -/
theorem historySelected_update_fixed
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D i : ℕ) (H : TypedHistory n i) :
    (historySelectedModel sys σ D i H).generator.update =
      (realizedModel sys.baseline).generator.update :=
  feedback_preserves_update sys (historyFeedback sys σ D i (prefixEncode i H))

/-- Real Mathlib kernel whose typed induced alpha/P/U row depends on the
entire prefix, not simply its last encoded state. -/
noncomputable def typedHistoryStep
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D i : ℕ) : Kernel (TypedHistory n i) (JointState Unit (Fin n)) where
  toFun := fun H =>
    (historySelectedModel sys σ D i H).inducedKernel
      (H ⟨i, Finset.mem_Iic.mpr le_rfl⟩)
  measurable' := Measurable.of_discrete

instance typedHistoryStep_isMarkov
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D i : ℕ) : IsMarkovKernel (typedHistoryStep sys σ D i) := by
  refine ⟨fun H => ?_⟩
  change IsProbabilityMeasure
    ((historySelectedModel sys σ D i H).inducedKernel
      (H ⟨i, Finset.mem_Iic.mpr le_rfl⟩))
  infer_instance

theorem typedLast_eq_decode_encodedLast {n i : ℕ} (H : TypedHistory n i) :
    H ⟨i, Finset.mem_Iic.mpr le_rfl⟩ =
      decode (HistoryDependent.last (prefixEncode i H)) := by
  simpa [HistoryDependent.last, prefixEncode] using
    (decode_encode (H ⟨i, Finset.mem_Iic.mpr le_rfl⟩)).symm

/-- Exact full measurable-event one-step equality, for EVERY typed prefix,
including any zero-probability or unreachable history. -/
theorem typedHistoryStep_worldCylinder
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D i : ℕ) (H : TypedHistory n i)
    {E : Set (Fin n)} (hE : MeasurableSet E) :
    typedHistoryStep sys σ D i H (encode ⁻¹' E) =
      HistoryDependent.historyStep sys σ D i
        (prefixEncode i H) E := by
  let h := prefixEncode i H
  let y := HistoryDependent.last h
  have hy : H ⟨i, Finset.mem_Iic.mpr le_rfl⟩ = decode y :=
    typedLast_eq_decode_encodedLast H
  change (historySelectedModel sys σ D i H).inducedKernel
      (H ⟨i, Finset.mem_Iic.mpr le_rfl⟩) (encode ⁻¹' E) = _
  rw [hy]
  change (realizedModel (feedbackMatrix sys
      (historyFeedback sys σ D i h))).inducedKernel
        (decode y) (encode ⁻¹' E) =
    rationalFiniteKernel (sys.matrix (σ.choose D i h)) y E
  rw [inducedKernel_worldCylinder _ y hE,
    historyFeedback_current_measure sys σ D i h]

/-- Exact typed successor atom as the selected history-dependent rational row. -/
theorem typedHistoryStep_decode_singleton
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D i : ℕ) (H : TypedHistory n i) (z : Fin n) :
    typedHistoryStep sys σ D i H {decode z} =
      ENNReal.ofReal
        (HistoryDependent.selectedEntry sys σ D i (prefixEncode i H) z : ℝ) := by
  have hset : encode ⁻¹' ({z} : Set (Fin n)) = {decode z} := by
    ext p
    rcases p with ⟨u,v⟩
    cases u
    simp [encode, decode]
  rw [← hset, typedHistoryStep_worldCylinder sys σ D i H
    (measurableSet_singleton z)]
  exact HistoryDependent.historyStep_singleton sys σ D i
    (prefixEncode i H) z

end HistoryDependentTyped
end ReverseSolver
end PermanssonResearch
