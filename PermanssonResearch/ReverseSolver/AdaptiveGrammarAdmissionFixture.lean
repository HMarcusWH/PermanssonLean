import PermanssonResearch.ReverseSolver.AdaptiveGrammarControl
import PermanssonResearch.GrammarRobust.AdversarialAdmission
import Mathlib.Tactic

/-!
D-08 restricted grammar and controlled-menu integration.

A CertifiedMenu admission predicate is linked to the *frozen*
restrictive partition rule. A concrete nonvacuous CertifiedMenu with
source-bound atom certificates is still a separate acceptance obligation.
-/
open MeasureTheory ProbabilityTheory
namespace PermanssonResearch.ReverseSolver.AdaptiveGrammarAdmissionFixture
open PermanssonLean
open PermanssonResearch.GrammarRobust
open PermanssonResearch.GrammarRobust.BooleanDynamics
open PermanssonResearch.GrammarRobust.AdversarialAdmission
open PermanssonResearch.ReverseSolver.AdaptiveGrammarControl
set_option autoImplicit false

theorem forbidden_joint_not_in_restricted_menu
    {S X A C : Type*}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    [DecidableEq C] [Fintype C] {n : ℕ}
    (M : StrategicWorldModel S X A)
    (D : CertifiedMenu M C n)
    (names : PatchSelection S X A → Finset (Fin 2))
    (hlink : ∀ selection, D.admitted selection ↔
      AdversarialAdmission.restricted.allowed (names selection))
    (c : C)
    (hjoint : names (D.selection c) = joint) : False := by
  have hc : AdversarialAdmission.restricted.allowed (names (D.selection c)) :=
    (hlink _).mp (D.selection_admitted c)
  rw [hjoint] at hc
  exact AdversarialAdmission.restricted_joint_rejected hc

theorem admitted_block_row_normalized
    {S X A C : Type*}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    [DecidableEq C] [Fintype C] {n : ℕ}
    (M : StrategicWorldModel S X A) (D : CertifiedMenu M C n)
    (c : C) (y : Fin n) :
    (∑ z : Fin n, (D.rational c).entry y z) = 1 :=
  (D.rational c).row_sum_one y

end PermanssonResearch.ReverseSolver.AdaptiveGrammarAdmissionFixture
