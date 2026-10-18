import PermanssonResearch.GrammarRobust.CompatibleOverlap
import PermanssonLean.StrategicWorld.PathLaw

/-! Actual typed assembly for B-OVERLAP. Only the strategic action and update
kernels are patched. The world primitive is the original object. -/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch.GrammarRobust

open PermanssonLean

variable {S X A : Type*} [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

noncomputable def overlapModel (M : StrategicWorldModel S X A)
    (actions : List (RowPatch (JointState S X) A))
    (updates : List (RowPatch (UpdateInput S X A) S)) : StrategicWorldModel S X A :=
  let α := applyCompatiblePatches actions ⟨M.generator.action, M.generator.action_isMarkov⟩
  let U := applyCompatiblePatches updates ⟨M.generator.update, M.generator.update_isMarkov⟩
  { generator :=
      { action := α.kernel
        update := U.kernel
        action_isMarkov := α.isMarkov
        update_isMarkov := U.isMarkov }
    world := M.world
    world_isMarkov := M.world_isMarkov }

@[simp] theorem overlapModel_world (M : StrategicWorldModel S X A)
    (actions : List (RowPatch (JointState S X) A))
    (updates : List (RowPatch (UpdateInput S X A) S)) :
    (overlapModel M actions updates).world = M.world := rfl

/-- Permuting either compatible family preserves the complete actual model. -/
theorem overlapModel_eq_of_membership (M : StrategicWorldModel S X A)
    (as bs : List (RowPatch (JointState S X) A))
    (us vs : List (RowPatch (UpdateInput S X A) S))
    (ha : ∀ p ∈ as, ∀ q ∈ as, p.Compatible q)
    (hu : ∀ p ∈ us, ∀ q ∈ us, p.Compatible q)
    (hab : ∀ p, p ∈ as ↔ p ∈ bs)
    (huv : ∀ p, p ∈ us ↔ p ∈ vs) :
    overlapModel M as us = overlapModel M bs vs := by
  have hα := applyCompatiblePatches_eq_of_membership as bs ha hab
    ⟨M.generator.action, M.generator.action_isMarkov⟩
  have hU := applyCompatiblePatches_eq_of_membership us vs hu huv
    ⟨M.generator.update, M.generator.update_isMarkov⟩
  unfold overlapModel
  dsimp only
  congr 2

/-- Equality of actual models transports the canonical infinite law for every
initial probability, with no path-space or stationarity surrogate. -/
theorem overlapModel_pathLaw_eq_of_membership (M : StrategicWorldModel S X A)
    (as bs : List (RowPatch (JointState S X) A))
    (us vs : List (RowPatch (UpdateInput S X A) S))
    (ha : ∀ p ∈ as, ∀ q ∈ as, p.Compatible q)
    (hu : ∀ p ∈ us, ∀ q ∈ us, p.Compatible q)
    (hab : ∀ p, p ∈ as ↔ p ∈ bs)
    (huv : ∀ p, p ∈ us ↔ p ∈ vs)
    (μ : Measure (JointState S X)) [IsProbabilityMeasure μ] :
    (overlapModel M as us).pathLaw μ = (overlapModel M bs vs).pathLaw μ := by
  rw [overlapModel_eq_of_membership M as bs us vs ha hu hab huv]

end PermanssonResearch.GrammarRobust
