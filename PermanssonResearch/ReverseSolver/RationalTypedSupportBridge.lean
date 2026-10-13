import PermanssonResearch.ReverseSolver.MenuMarginOptimization
import PermanssonResearch.ReverseSolver.TypedMenuCertification
import PermanssonResearch.ReverseSolver.FiniteStrategicRealization
import Mathlib.Tactic

/-!
# C9-05 — exact rational positive-edge/graph transport to typed alpha/P/U

The D0 constructive model with memory Unit and world Fin n has *exactly*
the rational positive one-step support in its genuine induced kernel.
This is NOT a statement that external strategic-world kernels admit a
rational representation. For a full regime protocol screen we additionally
require the original frozen descriptor and full B₁-start correspondence.

Finite BSCC enumeration and numerical absorption-value execution are
separate C10 obligations, not claimed by this structural adapter.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace RationalTypedSupportBridge

set_option autoImplicit false
attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

open PermanssonLean
open PermanssonLean.RegimeSpecification
open FiniteStrategicRealization
open PermanssonResearch.MultipleLimit.KernelCommunication
open PermanssonResearch.MultipleLimit.OppositeClassConstitutiveMargin

/-- Rational transition support uses strict exact positive entries. -/
def RationalPositiveEdge {n : ℕ} (L : RationalMarkovMatrix n)
    (x z : Fin n) : Prop :=
  0 < L.entry x z

def RationalReachable {n : ℕ} (L : RationalMarkovMatrix n)
    (x z : Fin n) : Prop :=
  Relation.ReflTransGen (RationalPositiveEdge L) x z

/-- The actual D0-constructed strategic intervention kernel's
singleton probability, not an unrelated rational reference matrix. -/
theorem rationalTyped_positiveEdge_iff {n : ℕ}
    (baseline L : RationalMarkovMatrix n) (x z : Fin n) :
    PositiveEdge
      (rationalStrategicIntervention baseline L).intervention.apply.inducedKernel
      (decode x) (decode z) ↔ RationalPositiveEdge L x z := by
  have hset : ({decode z} : Set (JointState Unit (Fin n))) =
      encode ⁻¹' ({z} : Set (Fin n)) := by
    ext y
    rcases y with ⟨u, t⟩
    cases u
    simp [encode, decode]
  unfold PositiveEdge RationalPositiveEdge
  rw [hset, intervenedKernel_worldCylinder baseline L x
      (measurableSet_singleton z)]
  rw [rationalFiniteKernel_singleton L x z]
  simp only [ENNReal.ofReal_pos]
  exact_mod_cast (show 0 < L.entry x z ↔ 0 < L.entry x z from Iff.rfl)

/-- Positive-edge reachable paths correspond in BOTH directions
through the genuine D0 typed kernel and its Unit×Fin n state encoding. -/
theorem rationalTyped_reachable_iff {n : ℕ}
    (baseline L : RationalMarkovMatrix n) (x z : Fin n) :
    RationalReachable L x z ↔
      Reachable
        (rationalStrategicIntervention baseline L).intervention.apply.inducedKernel
        (decode x) (decode z) := by
  let K :=
    (rationalStrategicIntervention baseline L).intervention.apply.inducedKernel
  constructor
  · intro h
    induction h with
    | refl => exact reachable_refl K (decode x)
    | @tail a b hab hab' ih =>
      exact reachable_trans K ih
        (reachable_single K ((rationalTyped_positiveEdge_iff
          baseline L a b).mpr hab'))
  · intro h
    have htransport (a b : JointState Unit (Fin n))
        (hab : Reachable K a b) :
        RationalReachable L (encode a) (encode b) := by
      induction hab with
      | refl => exact Relation.ReflTransGen.refl
      | @tail a b hab hab' ih =>
        have hedge : PositiveEdge K
            (decode (encode a)) (decode (encode b)) := by
          simpa only [decode_encode] using hab'
        exact Relation.ReflTransGen.tail ih
          ((rationalTyped_positiveEdge_iff baseline L
            (encode a) (encode b)).mp hedge)
    simpa only [encode_decode] using htransport (decode x) (decode z) h

/-- A transported Boolean descriptor is exactly the frozen original
descriptor when it agrees on every encoded physical state. -/
theorem frozenDescriptor_eq_transport {n : ℕ}
    (hY : JointState Unit (Fin n) → Bool)
    (hR : Fin n → Bool)
    (hdesc : ∀ x : Fin n, hY (decode x) = hR x) :
    hY = fun y => hR (encode y) := by
  funext y
  have hh := hdesc (encode y)
  simpa only [decode_encode] using hh

/-- The full original comparison set is preserved by an exact
finite-index representation, not by checking a favorable single start. -/
theorem all_frozen_comparison_starts_iff {n : ℕ}
    (B : Set (JointState Unit (Fin n)))
    (BR : Finset (Fin n))
    (hBR : ∀ x : Fin n, x ∈ BR ↔ decode x ∈ B)
    (P : JointState Unit (Fin n) → Prop) :
    (∀ y ∈ B, P y) ↔ (∀ x ∈ BR, P (decode x)) := by
  constructor
  · intro h x hx
    exact h (decode x) ((hBR x).mp hx)
  · intro h y hy
    have hx : encode y ∈ BR := (hBR (encode y)).mpr (by
      simpa only [decode_encode] using hy)
    have hp := h (encode y) hx
    simpa only [decode_encode] using hp

/-- The true typed opposing-class predicate is screened at ALL frozen
B₁ starts through an exact BR representation, holding both spec.target
and spec.descriptor unchanged. This is a logical transport, not a
claimed executable BSCC algorithm. -/
theorem typed_frozenB1_screen_iff {n : ℕ} [NeZero n]
    (baseline L : RationalMarkovMatrix n)
    (spec : RegimeSpecification (JointState Unit (Fin n)) Bool)
    (B₁ : ConstitutiveComparisonSet (realizedModel baseline) spec)
    (BR : Finset (Fin n))
    (hBR : ∀ x : Fin n, x ∈ BR ↔ decode x ∈ B₁.states) :
    (∀ y ∈ B₁.states,
      OpposingClassReachable
        (rationalStrategicIntervention baseline L).intervention.apply.inducedKernel
        spec.descriptor spec.target y) ↔
    (∀ x ∈ BR,
      OpposingClassReachable
        (rationalStrategicIntervention baseline L).intervention.apply.inducedKernel
        spec.descriptor spec.target (decode x)) := by
  exact all_frozen_comparison_starts_iff B₁.states BR hBR _

end RationalTypedSupportBridge
end ReverseSolver
end PermanssonResearch
