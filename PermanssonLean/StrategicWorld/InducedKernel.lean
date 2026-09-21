import PermanssonLean.StrategicWorld.Model
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.MapComap

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonLean

universe uS uX uA

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

namespace StrategicWorldModel

/-- Reassociate the history retained by `Kernel.compProd` with the paper-level input
expected by the strategic update kernel:
`(y, (a, x')) ↦ ((y, a), x')`. -/
def updateInputReassoc :
    JointState S X × (A × X) → UpdateInput S X A :=
  fun z => ((z.1, z.2.1), z.2.2)

theorem measurable_updateInputReassoc :
    Measurable (updateInputReassoc (S := S) (X := X) (A := A)) := by
  fun_prop

/-- The update kernel `U`, reindexed to consume the history shape produced after
sampling an action and the next world state. -/
noncomputable def reassociatedUpdate
    (M : StrategicWorldModel S X A) :
    Kernel (JointState S X × (A × X)) S :=
  M.generator.update.comap
    (updateInputReassoc (S := S) (X := X) (A := A))
    measurable_updateInputReassoc

/-- Sequentially sample `a ~ α(· | y)` and then `x' ~ P(· | y,a)`,
retaining both realized values. -/
noncomputable def actionWorldKernel
    (M : StrategicWorldModel S X A) :
    Kernel (JointState S X) (A × X) :=
  M.generator.action ⊗ₖ M.world

/-- Retain the complete one-step sampled history `((a,x'),s')` before projecting
to the next joint state. -/
noncomputable def oneStepHistoryKernel
    (M : StrategicWorldModel S X A) :
    Kernel (JointState S X) ((A × X) × S) :=
  M.actionWorldKernel ⊗ₖ M.reassociatedUpdate

/-- Canonical induced joint one-step kernel

`α → P → U → (s',x')`

from the typed strategic-world model. The temporary realized action is dropped only
after the update kernel has consumed it. -/
noncomputable def inducedKernel
    (M : StrategicWorldModel S X A) :
    Kernel (JointState S X) (JointState S X) :=
  M.oneStepHistoryKernel.map
    (fun z : (A × X) × S => (z.2, z.1.2))

theorem reassociatedUpdate_isMarkov
    (M : StrategicWorldModel S X A) :
    IsMarkovKernel M.reassociatedUpdate := by
  letI : IsMarkovKernel M.generator.update := M.generator.update_isMarkov
  unfold reassociatedUpdate
  infer_instance

theorem actionWorldKernel_isMarkov
    (M : StrategicWorldModel S X A) :
    IsMarkovKernel M.actionWorldKernel := by
  letI : IsMarkovKernel M.generator.action := M.generator.action_isMarkov
  letI : IsMarkovKernel M.world := M.world_isMarkov
  unfold actionWorldKernel
  infer_instance

theorem oneStepHistoryKernel_isMarkov
    (M : StrategicWorldModel S X A) :
    IsMarkovKernel M.oneStepHistoryKernel := by
  letI : IsMarkovKernel M.generator.action := M.generator.action_isMarkov
  letI : IsMarkovKernel M.world := M.world_isMarkov
  letI : IsMarkovKernel M.generator.update := M.generator.update_isMarkov
  letI : IsMarkovKernel M.actionWorldKernel := actionWorldKernel_isMarkov M
  letI : IsMarkovKernel M.reassociatedUpdate := reassociatedUpdate_isMarkov M
  unfold oneStepHistoryKernel
  infer_instance

/-- The paper's typed composition `α → P → U` induces a Markov kernel on
the joint strategic-world state space. -/
theorem inducedKernel_isMarkov
    (M : StrategicWorldModel S X A) :
    IsMarkovKernel M.inducedKernel := by
  letI : IsMarkovKernel M.oneStepHistoryKernel := oneStepHistoryKernel_isMarkov M
  unfold inducedKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- Setwise semantic expansion of the induced kernel. This is the paper-level
one-step law with the integration order `α → P → U`. -/
theorem inducedKernel_apply
    (M : StrategicWorldModel S X A)
    (y : JointState S X) {E : Set (JointState S X)}
    (hE : MeasurableSet E) :
    M.inducedKernel y E =
      ∫⁻ a, ∫⁻ x',
        M.generator.update ((y, a), x') {s' | (s', x') ∈ E}
        ∂M.world (y, a)
      ∂M.generator.action y := by
  letI : IsMarkovKernel M.generator.action := M.generator.action_isMarkov
  letI : IsMarkovKernel M.world := M.world_isMarkov
  letI : IsMarkovKernel M.generator.update := M.generator.update_isMarkov
  rw [inducedKernel, Kernel.map_apply' _ (by fun_prop) _ hE]
  rw [oneStepHistoryKernel, Kernel.compProd_apply]
  rw [actionWorldKernel, Kernel.lintegral_compProd]
  · rfl
  · fun_prop
  · exact hE.preimage (by fun_prop)

/-- Indicator-integral form of `inducedKernel_apply`, matching the displayed
triple-integral definition used in the paper. -/
theorem inducedKernel_apply_indicator
    (M : StrategicWorldModel S X A)
    (y : JointState S X) {E : Set (JointState S X)}
    (hE : MeasurableSet E) :
    M.inducedKernel y E =
      ∫⁻ a, ∫⁻ x', ∫⁻ s',
        E.indicator (fun _ => (1 : ℝ≥0∞)) (s', x')
        ∂M.generator.update ((y, a), x')
      ∂M.world (y, a)
      ∂M.generator.action y := by
  rw [inducedKernel_apply M y hE]
  congr with a
  congr with x'
  rw [lintegral_indicator_const]
  · simp
  · exact hE.preimage (by fun_prop)

end StrategicWorldModel

end PermanssonLean
