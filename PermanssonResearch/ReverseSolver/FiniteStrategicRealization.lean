import PermanssonResearch.ReverseSolver.CanonicalAllHorizonCorrespondence
import PermanssonLean.Intervention.Apply
import Mathlib.Probability.Kernel.Deterministic
import Mathlib.Tactic

/-!
# D0-D: a genuine finite strategic-world realization of rational Markov rows

This is a constructive realization, NOT an assertion that an arbitrary
externally supplied rational matrix matches an arbitrary strategic-world model.

Strategic memory is Unit, world states and actions are Fin n.  The action
kernel selects the next world value with the desired rational row weights,
P deterministically copies that selected action into the next world state,
and U deterministically updates the trivial strategic memory.  In particular,
P and U are completely independent of the selected rational matrix.

The original canonical alpha -> P -> U semantics are used to prove a
world-cylinder equality for ALL measurable events.  The finite instance
is intentionally simple enough to give a non-vacuous exact model witness
without assuming the D0-B ExactMenuValueCorrespondence.exact_values field.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch
namespace ReverseSolver
namespace FiniteStrategicRealization

open PermanssonLean

noncomputable section

/-- Include the ordinary rational matrix on X = Fin n as an action kernel,
where the incoming strategic-world state is ((), x). -/
def liftedRationalAction {n : ℕ} (K : RationalMarkovMatrix n) :
    Kernel (JointState Unit (Fin n)) (Fin n) :=
  (rationalFiniteKernel K).comap
    (fun y : JointState Unit (Fin n) => y.2) measurable_snd

theorem liftedRationalAction_isMarkov {n : ℕ}
    (K : RationalMarkovMatrix n) :
    IsMarkovKernel (liftedRationalAction K) := by
  letI : IsMarkovKernel (rationalFiniteKernel K) :=
    rationalFiniteKernel_isMarkov K
  unfold liftedRationalAction
  infer_instance

/-- The world primitive P copies the chosen action to the next world state.
It does not depend on which rational matrix the strategic generator uses. -/
def copiedActionWorld (n : ℕ) :
    Kernel (WorldInput Unit (Fin n) (Fin n)) (Fin n) :=
  Kernel.deterministic (fun z => z.2) (by exact Measurable.of_discrete)

/-- U erases the action and observation into the unique strategic memory. -/
def trivialStrategicUpdate (n : ℕ) :
    Kernel (UpdateInput Unit (Fin n) (Fin n)) Unit :=
  Kernel.deterministic (fun _ => ()) (by exact measurable_const)

/-- A fully typed, normalized alpha/P/U factorization of rational K. -/
def realizedGenerator {n : ℕ} (K : RationalMarkovMatrix n) :
    StrategicGenerator Unit (Fin n) (Fin n) where
  action := liftedRationalAction K
  update := trivialStrategicUpdate n
  action_isMarkov := liftedRationalAction_isMarkov K
  update_isMarkov := by
    unfold trivialStrategicUpdate
    infer_instance

def realizedModel {n : ℕ} (K : RationalMarkovMatrix n) :
    StrategicWorldModel Unit (Fin n) (Fin n) where
  generator := realizedGenerator K
  world := copiedActionWorld n
  world_isMarkov := by
    unfold copiedActionWorld
    infer_instance

/-- All rational choices in this construction have the exact same P. -/
theorem realizedModel_world_fixed {n : ℕ}
    (K L : RationalMarkovMatrix n) :
    (realizedModel K).world = (realizedModel L).world := rfl

/-- The joint-state decoder and projection have no hidden state choices. -/
def decode {n : ℕ} (x : Fin n) : JointState Unit (Fin n) := ((), x)
def encode {n : ℕ} (y : JointState Unit (Fin n)) : Fin n := y.2

@[simp] theorem encode_decode {n : ℕ} (x : Fin n) :
    encode (decode x) = x := rfl

@[simp] theorem decode_encode {n : ℕ} (y : JointState Unit (Fin n)) :
    decode (encode y) = y := by
  rcases y with ⟨u, x⟩
  cases u
  rfl

/-- THE D0-D one-step bridge for this constructed factorization:
for every measurable world event D, the canonical alpha/P/U-induced kernel
has exactly the rational kernel's mass on its encoded world cylinder. -/
theorem inducedKernel_worldCylinder {n : ℕ}
    (K : RationalMarkovMatrix n) (x : Fin n)
    {D : Set (Fin n)} (hD : MeasurableSet D) :
    (realizedModel K).inducedKernel (decode x) (encode ⁻¹' D) =
      rationalFiniteKernel K x D := by
  change (realizedModel K).inducedKernel ((), x) (Prod.snd ⁻¹' D) =
    rationalFiniteKernel K x D
  rw [StrategicWorldModel.inducedKernel_apply
    (realizedModel K) ((), x) (hD.preimage measurable_snd)]
  simp [realizedModel, realizedGenerator, liftedRationalAction,
    copiedActionWorld, trivialStrategicUpdate,
    Kernel.deterministic_apply]
  change (∫⁻ z : Fin n, D.indicator (fun _ => (1 : ℝ≥0∞)) z
    ∂rationalFiniteKernel K x) = (rationalFiniteKernel K) x D
  exact lintegral_indicator_one hD

/-- The original matrix entries themselves are the induced probabilities of
the encoded one-step atoms, not merely independently computed scores. -/
theorem inducedKernel_encodedEntry {n : ℕ}
    (K : RationalMarkovMatrix n) (x z : Fin n) :
    (realizedModel K).inducedKernel (decode x) (encode ⁻¹' {z}) =
      ENNReal.ofReal (K.entry x z : ℝ) := by
  rw [inducedKernel_worldCylinder K x (measurableSet_singleton z)]
  exact rationalFiniteKernel_singleton K x z

/-- The frozen family admits action-selection replacements only.
This permissive research family is part of the *constructed* example, not
an admissibility assertion about externally supplied models or games. -/
def researchActionFamily {n : ℕ} (K : RationalMarkovMatrix n) :
    InterventionFamily (realizedModel K) Unit where
  targetOf _ := .actionSelection
  admissible _ _ := True

/-- Replace the action-selection kernel while holding the original P and U. -/
def rationalActionReplacement {n : ℕ} (L : RationalMarkovMatrix n) :
    InterventionReplacement Unit (Fin n) (Fin n) .actionSelection :=
  ⟨liftedRationalAction L, liftedRationalAction_isMarkov L⟩

/-- A genuine typed, admissible STRATEGIC intervention in the constructed
family: the chosen matrix changes only alpha, never P or U. -/
def rationalStrategicIntervention {n : ℕ}
    (K L : RationalMarkovMatrix n) :
    AdmissibleStrategicIntervention (researchActionFamily K) where
  intervention := {
    component := ()
    replacement := rationalActionReplacement L
  }
  accepted := by trivial
  strategic := by
    simp [TypedIntervention.IsStrategic, researchActionFamily]

/-- Applying the concrete action replacement reconstructs the desired
typed factorization.  This equality is definitional for this family alone. -/
theorem rationalStrategicIntervention_applied {n : ℕ}
    (K L : RationalMarkovMatrix n) :
    (rationalStrategicIntervention K L).intervention.apply =
      realizedModel L := rfl

/-- Every member's actual induced kernel, after typed intervention,
agrees on every world event with the requested rational row. -/
theorem intervenedKernel_worldCylinder {n : ℕ}
    (K L : RationalMarkovMatrix n) (x : Fin n)
    {D : Set (Fin n)} (hD : MeasurableSet D) :
    (rationalStrategicIntervention K L).intervention.apply.inducedKernel
        (decode x) (encode ⁻¹' D) =
      rationalFiniteKernel L x D := by
  rw [rationalStrategicIntervention_applied]
  exact inducedKernel_worldCylinder L x hD

/-- The intervention leaves both the original P and U unchanged. -/
theorem rationalStrategicIntervention_world_fixed {n : ℕ}
    (K L : RationalMarkovMatrix n) :
    (rationalStrategicIntervention K L).intervention.apply.world =
      (realizedModel K).world :=
  (rationalStrategicIntervention K L).world_eq

theorem rationalStrategicIntervention_update_fixed {n : ℕ}
    (K L : RationalMarkovMatrix n) :
    (rationalStrategicIntervention K L).intervention.apply.generator.update =
      (realizedModel K).generator.update := by
  rw [rationalStrategicIntervention_applied]
  rfl

end
end FiniteStrategicRealization
end ReverseSolver
end PermanssonResearch
