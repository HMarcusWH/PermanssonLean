import PermanssonResearch.ReverseSolver.FiniteStrategicPathBridge
import PermanssonResearch.ReverseSolver.ValueCorrespondence
import Mathlib.Tactic

/-!
# D0-E: complete typed finite menu and unconditional rational-optimum transfer

No equality-of-values hypothesis is added. Every member is constructed as an
actual admissible action-selection intervention of one frozen baseline with
shared P and U. Every target, initial state and full hitting event is the
proved measurable encoding of the finite rational query.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace TypedMenuCertification

open PermanssonLean
open FiniteStrategicRealization
open FiniteStrategicPathBridge

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

universe uI

noncomputable section

/-- Exactly the listed rational indices, interpreted as actual admissible
strategic interventions. The baseline is absent unless explicitly listed. -/
def typedFiniteMenu {I : Type uI} [DecidableEq I] {n : ℕ}
    (baseline : RationalMarkovMatrix n)
    (rational : RationalMatrixMenu I n) :
    FrozenMenu (realizedModel baseline) (researchActionFamily baseline) I where
  indices := rational.items.toFinset
  nonempty := by
    cases h : rational.items with
    | nil => exact (rational.items_nonempty h).elim
    | cons a tail =>
        exact ⟨a, by simp [h]⟩
  choice := fun i => rationalStrategicIntervention baseline (rational.matrix i)

/-- The two menus contain precisely the same indices (duplicates in the
rational list represent a single eligible typed index). -/
theorem typedFiniteMenu_mem_iff {I : Type uI} [DecidableEq I] {n : ℕ}
    (baseline : RationalMarkovMatrix n)
    (rational : RationalMatrixMenu I n) (i : I) :
    i ∈ (typedFiniteMenu baseline rational).indices ↔
      i ∈ rational.items := by
  simp [typedFiniteMenu]

/-- For every finite rational menu, model and horizon, construct the previously
CONDITIONAL D0-B correspondence from genuine D0-D and D0-C theorems. -/
def certifiedExactCorrespondence {I : Type uI} [DecidableEq I] {n : ℕ}
    (baseline : RationalMarkovMatrix n)
    (rational : RationalMatrixMenu I n)
    (rt : RationalHittingTarget n) (x : Fin n) (T : ℕ) :
    ExactMenuValueCorrespondence (realizedModel baseline)
      (researchActionFamily baseline)
      (typedFiniteMenu baseline rational) rational
      (typedTarget rt) (decode x) rt x T where
  rational_eligible := by
    intro i hi
    exact (typedFiniteMenu_mem_iff baseline rational i).2 hi
  typed_covered := by
    intro i hi
    exact (typedFiniteMenu_mem_iff baseline rational i).1 hi
  exact_values := by
    intro i hi
    unfold rationalMemberValue memberValue
    change
      (rationalHittingValue (rational.matrix i) rt T x : ℝ) =
      hittingValue (typedTarget rt)
        (rationalStrategicIntervention baseline
          (rational.matrix i)).intervention.apply.inducedKernel
        (decode x) T
    rw [rationalStrategicIntervention_applied]
    exact (typedHittingValue_eq_rational_all_horizons
      (rational.matrix i) rt x T).symm

/-- A computably chosen rational argmax is a genuine member of the typed
frozen menu. This theorem does not require a choice axiom for selecting i*. -/
theorem certifiedSelected_mem {I : Type uI} [DecidableEq I] {n : ℕ}
    (baseline : RationalMarkovMatrix n)
    (rational : RationalMatrixMenu I n)
    (rt : RationalHittingTarget n) (x : Fin n) (T : ℕ) :
    selectRationalMember rational rt x T ∈
      (typedFiniteMenu baseline rational).indices :=
  selectedRational_eligible (typedFiniteMenu baseline rational) rational
    (typedTarget rt) (decode x) rt x T
    (certifiedExactCorrespondence baseline rational rt x T)

/-- Unconditional, all-horizon typed menu optimality among the precisely
listed fixed action-selection interventions of this constructed finite
strategic-world model. -/
theorem certifiedSelected_dominatesTyped {I : Type uI}
    [DecidableEq I] {n : ℕ}
    (baseline : RationalMarkovMatrix n)
    (rational : RationalMatrixMenu I n)
    (rt : RationalHittingTarget n) (x : Fin n) (T : ℕ) :
    ∀ j ∈ (typedFiniteMenu baseline rational).indices,
      memberValue (typedFiniteMenu baseline rational)
        (typedTarget rt) (decode x) T j ≤
      memberValue (typedFiniteMenu baseline rational)
        (typedTarget rt) (decode x) T
        (selectRationalMember rational rt x T) :=
  selectedRational_dominatesTyped (typedFiniteMenu baseline rational) rational
    (typedTarget rt) (decode x) rt x T
    (certifiedExactCorrespondence baseline rational rt x T)

/-- The selected intervention itself is structurally strategic: the baseline
world-transition primitive P remains frozen. -/
theorem certifiedSelected_preserves_world {I : Type uI}
    [DecidableEq I] {n : ℕ}
    (baseline : RationalMarkovMatrix n)
    (rational : RationalMatrixMenu I n)
    (rt : RationalHittingTarget n) (x : Fin n) (T : ℕ) :
    ((typedFiniteMenu baseline rational).choice
      (selectRationalMember rational rt x T)).intervention.apply.world =
        (realizedModel baseline).world :=
  selectedRational_world_eq (typedFiniteMenu baseline rational) rational
    (typedTarget rt) (decode x) rt x T

/-- This particular constructed family also preserves U under every listed
action-selection replacement; this is stronger than holding P fixed. -/
theorem certifiedSelected_preserves_update {I : Type uI}
    [DecidableEq I] {n : ℕ}
    (baseline : RationalMarkovMatrix n)
    (rational : RationalMatrixMenu I n)
    (rt : RationalHittingTarget n) (x : Fin n) (T : ℕ) :
    ((typedFiniteMenu baseline rational).choice
      (selectRationalMember rational rt x T)).intervention.apply.generator.update =
        (realizedModel baseline).generator.update :=
  rationalStrategicIntervention_update_fixed _ _

/-- Exact rational and actual typed optimum values coincide without
introducing or passing the old exact_values condition as an assumption. -/
theorem certifiedSelected_exactValue {I : Type uI}
    [DecidableEq I] {n : ℕ}
    (baseline : RationalMarkovMatrix n)
    (rational : RationalMatrixMenu I n)
    (rt : RationalHittingTarget n) (x : Fin n) (T : ℕ) :
    (rationalMemberValue rational rt x T
      (selectRationalMember rational rt x T) : ℝ) =
    memberValue (typedFiniteMenu baseline rational)
      (typedTarget rt) (decode x) T
      (selectRationalMember rational rt x T) :=
  (certifiedExactCorrespondence baseline rational rt x T).exact_values _
    (selectRationalMember_mem rational rt x T)

end
end TypedMenuCertification
end ReverseSolver
end PermanssonResearch
