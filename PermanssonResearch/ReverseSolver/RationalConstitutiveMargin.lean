import PermanssonResearch.ReverseSolver.RationalEventuallyObserved
import Mathlib.Tactic

/-!
# C10 — exact rational maximin arithmetic for one fixed intervention

The original comparison set is supplied as one nonempty finite set. A
candidate must be held fixed across ALL states of that set. This arithmetic
layer does not itself assert equality with the original typed path-law margin.
-/
namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

/-- One baseline certificate and one separately computed certificate for
each candidate. No baseline recurrent decomposition is reused by a member. -/
structure MenuCertificate (n menuSize : ℕ) where
  baseline : DirichletCertificate n
  members : Fin menuSize → DirichletCertificate n

/-- All rational numerical tables are checked against their own matrix. -/
def MenuConditions {n menuSize : ℕ}
    (raw : RawInput n menuSize) (checked : CheckedInput raw)
    (cert : MenuCertificate n menuSize) : Prop :=
  DirichletConditions checked.baseline cert.baseline ∧
    ∀ i : Fin menuSize,
      DirichletConditions (checked.members i) (cert.members i)

def checkMenu {n menuSize : ℕ}
    (raw : RawInput n menuSize) (checked : CheckedInput raw)
    (cert : MenuCertificate n menuSize) : Bool :=
  decide (MenuConditions raw checked cert)

theorem checkMenu_sound {n menuSize : ℕ}
    (raw : RawInput n menuSize) (checked : CheckedInput raw)
    (cert : MenuCertificate n menuSize)
    (hc : checkMenu raw checked cert = true) :
    MenuConditions raw checked cert := by
  simpa [checkMenu] using hc

/-- Pointwise exact rational effect, comparing both genuine candidate
numerical tables against the SAME frozen descriptor. -/
def numericalEffect {n menuSize : ℕ}
    (raw : RawInput n menuSize) (cert : MenuCertificate n menuSize)
    (i : Fin menuSize) (x : Fin n) : ℚ :=
  |eventValue cert.baseline raw.descriptor x -
    eventValue (cert.members i) raw.descriptor x|

/-- A single candidate's worst-case exact rational effect across every
predeclared comparison state, not an after-the-fact favorable singleton. -/
def numericalMargin {n menuSize : ℕ}
    (raw : RawInput n menuSize) (checked : CheckedInput raw)
    (cert : MenuCertificate n menuSize) (i : Fin menuSize) : ℚ :=
  raw.comparison.inf' checked.comparisonNonempty
    (numericalEffect raw cert i)

/-- Numeric effects are nonnegative independently of baseline GR status. -/
theorem numericalEffect_nonneg {n menuSize : ℕ}
    (raw : RawInput n menuSize) (cert : MenuCertificate n menuSize)
    (i : Fin menuSize) (x : Fin n) :
    0 ≤ numericalEffect raw cert i x := by
  exact abs_nonneg _

end C10
end ReverseSolver
end PermanssonResearch