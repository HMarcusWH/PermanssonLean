import PermanssonResearch.GrammarRobust.LowerSetTransport
import Mathlib.Tactic

/-!
NEXT-06 / B-02: actual positive local-order transport under a map that is
NOT globally injective (and therefore not a global order isomorphism).
The local strict lower set of 2 has a complete lift. Positivity is a fixed
predeclared property and not chosen after seeing the order map.
-/

namespace PermanssonResearch.GrammarRobust.LocalOrderPositiveFixture

open PermanssonResearch.GrammarRobust

/-- Collapse the entire tail of naturals to 2. This loses global injectivity. -/
def folded (n : ℕ) : ℕ := min n 2

theorem folded_eq_on_lower (n : ℕ) (hn : n ≤ 2) : folded n = n :=
  Nat.min_eq_left hn

theorem folded_not_injective : ¬ Function.Injective folded := by
  intro hinj
  have h : folded 2 = folded 3 := by decide
  have heq : (2 : ℕ) = 3 := hinj h
  omega

def positive (n : ℕ) : Prop := n = 2

theorem positive_is_minimal : IsMinimalPositive positive 2 := by
  constructor
  · rfl
  · intro b hb hbpos
    dsimp [positive] at hbpos
    omega

/-- Concrete B-LOCAL-ORDER instantiation. The entire strict lower set of the
selected block is transported, without global injectivity or a monotonicity
assumption outside the lower set. -/
theorem local_transport_under_noninjective_fold :
    IsMinimalPositive positive 2 ↔ IsMinimalPositive positive (folded 2) := by
  apply minimalPositive_iff_of_lowerSet_lifting folded positive positive 2
  · intro b hb
    rw [folded_eq_on_lower b hb]
  · intro b hb
    rw [folded_eq_on_lower b (Nat.le_of_lt hb)]
    simpa [folded] using hb
  · intro c hc
    have hlt : c < 2 := by simpa [folded] using hc
    exact ⟨c, hlt, folded_eq_on_lower c (Nat.le_of_lt hlt)⟩

/-- Nonvacuous positive conclusion of the actual local order theorem. -/
theorem folded_two_minimal : IsMinimalPositive positive (folded 2) :=
  local_transport_under_noninjective_fold.mp positive_is_minimal

/-- Distinguishes the positive local conclusion from the demonstrably false
claim that every order folding must preserve global injectivity. -/
theorem local_minimality_without_global_isomorphism :
    IsMinimalPositive positive (folded 2) ∧ ¬ Function.Injective folded :=
  ⟨folded_two_minimal, folded_not_injective⟩

end PermanssonResearch.GrammarRobust.LocalOrderPositiveFixture
