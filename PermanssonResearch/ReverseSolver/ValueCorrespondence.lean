import PermanssonResearch.ReverseSolver.CertifiedSelection
import PermanssonResearch.ReverseSolver.FrozenMenu
import Mathlib.Tactic

/-!
# D0-B: explicit rational/typed-menu value correspondence

A finite stochastic matrix must not be mistaken for a strategic-world
intervention. A complete menu correspondence records membership in BOTH
directions and exact equality of every candidate's rational and canonical
model-defined hitting values. Conditional on that correspondence, the
computable rational winner is proved optimal among the original typed menu.

This does NOT derive the equality-of-values field from row entries: that
independent forward-law/matrix-kernel theorem remains a separate obligation.
-/

namespace PermanssonResearch
namespace ReverseSolver

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe uS uX uA uC uI
variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

/-- Proof-carrying *conditional* mapping between finite rational evaluation
and a frozen menu of actual admissible strategic interventions. This does
not make an arbitrary matrix admissible. -/
structure ExactMenuValueCorrespondence
    (M : PermanssonLean.StrategicWorldModel S X A)
    {Component : Type uC}
    (F : PermanssonLean.InterventionFamily M Component)
    {I : Type uI}
    (typed : FrozenMenu M F I)
    {n : ℕ} (rational : RationalMatrixMenu I n)
    (target : FrozenHittingTarget (PermanssonLean.JointState S X))
    (y : PermanssonLean.JointState S X)
    (rationalTarget : RationalHittingTarget n)
    (rationalStart : Fin n)
    (T : ℕ) : Prop where
  rational_eligible : ∀ i ∈ rational.items, i ∈ typed.indices
  typed_covered : ∀ i ∈ typed.indices, i ∈ rational.items
  exact_values : ∀ i ∈ rational.items,
    (rationalMemberValue rational rationalTarget rationalStart T i : ℝ) =
      memberValue typed target y T i

/-- Every selected rational index is a genuinely eligible typed intervention. -/
theorem selectedRational_eligible
    {M : PermanssonLean.StrategicWorldModel S X A}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {I : Type uI}
    (typed : FrozenMenu M F I)
    {n : ℕ} (rational : RationalMatrixMenu I n)
    (target : FrozenHittingTarget (PermanssonLean.JointState S X))
    (y : PermanssonLean.JointState S X)
    (rt : RationalHittingTarget n) (ry : Fin n) (T : ℕ)
    (h : ExactMenuValueCorrespondence M F typed rational target y rt ry T) :
    selectRationalMember rational rt ry T ∈ typed.indices :=
  h.rational_eligible _ (selectRationalMember_mem rational rt ry T)

/-- Conditional end-to-end result: if the explicit rational evaluation
correspondence is *proved* for the entire typed menu, the computable list
argmax realizes the maximum of the canonical model-defined probabilities. -/
theorem selectedRational_dominatesTyped
    {M : PermanssonLean.StrategicWorldModel S X A}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {I : Type uI}
    (typed : FrozenMenu M F I)
    {n : ℕ} (rational : RationalMatrixMenu I n)
    (target : FrozenHittingTarget (PermanssonLean.JointState S X))
    (y : PermanssonLean.JointState S X)
    (rt : RationalHittingTarget n) (ry : Fin n) (T : ℕ)
    (h : ExactMenuValueCorrespondence M F typed rational target y rt ry T) :
    ∀ j ∈ typed.indices,
      memberValue typed target y T j ≤
        memberValue typed target y T
          (selectRationalMember rational rt ry T) := by
  intro j hj
  have hrj := h.typed_covered j hj
  have hrs := selectRationalMember_mem rational rt ry T
  have hdom := selectRationalMember_dominates rational rt ry T j hrj
  have hc : (rationalMemberValue rational rt ry T j : ℝ) ≤
      (rationalMemberValue rational rt ry T
        (selectRationalMember rational rt ry T) : ℝ) := by
    exact_mod_cast hdom
  calc
    memberValue typed target y T j =
        (rationalMemberValue rational rt ry T j : ℝ) :=
          (h.exact_values j hrj).symm
    _ ≤ (rationalMemberValue rational rt ry T
          (selectRationalMember rational rt ry T) : ℝ) := hc
    _ = memberValue typed target y T
          (selectRationalMember rational rt ry T) :=
            h.exact_values _ hrs

/-- The selected concrete intervention preserves P; no matrix factorization
or numerical data may mutate the original typed strategic-world primitive. -/
theorem selectedRational_world_eq
    {M : PermanssonLean.StrategicWorldModel S X A}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {I : Type uI}
    (typed : FrozenMenu M F I)
    {n : ℕ} (rational : RationalMatrixMenu I n)
    (target : FrozenHittingTarget (PermanssonLean.JointState S X))
    (y : PermanssonLean.JointState S X)
    (rt : RationalHittingTarget n) (ry : Fin n) (T : ℕ) :
    (typed.choice (selectRationalMember rational rt ry T)).intervention.apply.world =
      M.world :=
  (typed.choice (selectRationalMember rational rt ry T)).world_eq

end ReverseSolver
end PermanssonResearch
