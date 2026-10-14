import PermanssonResearch.ReverseSolver.RationalSupportGraph
import Mathlib.Tactic

/-!
# C10 — computable bottom-communication-class proposal and checking

A BSCC is a maximal strongly connected class with no positive outgoing
edge. The producer below enumerates proposed terminal classes using the
finite computed reach table. The checker validates exact closure and the
reported normalized component set. A generic proof of equality with the
existing abstract recurrent class representation is a separate obligation.
-/
namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

/-- The component of a numerical state under computed mutual reachability. -/
def component {n : ℕ} (K : RationalMarkovMatrix n)
    (x : Fin n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun y => communicatesB K x y = true)

/-- Exact rational closure test, independent of the (potentially periodic)
internal transition probabilities of a component. -/
def closedB {n : ℕ} (K : RationalMarkovMatrix n)
    (C : Finset (Fin n)) : Bool :=
  decide (∀ x ∈ C, ∀ z : Fin n, 0 < K.entry x z → z ∈ C)

/-- Computably deduplicated bottom SCC list as a finite set of finite sets. -/
def bottomClasses {n : ℕ} (K : RationalMarkovMatrix n) :
    Finset (Finset (Fin n)) :=
  (((Finset.univ : Finset (Fin n)).image (component K))).filter
    (fun C => C.Nonempty ∧ closedB K C = true)

/-- A finite, decidable receipt consistency check. No external class list
can silently drop or introduce a bottom component in this representation. -/
def checkBottomClasses {n : ℕ} (K : RationalMarkovMatrix n)
    (claimed : Finset (Finset (Fin n))) : Bool :=
  decide (claimed = bottomClasses K)

theorem checkBottomClasses_sound {n : ℕ} (K : RationalMarkovMatrix n)
    (claimed : Finset (Finset (Fin n)))
    (h : checkBottomClasses K claimed = true) :
    claimed = bottomClasses K := by
  simpa [checkBottomClasses] using h

/-- Every returned set satisfies the *actual exact-entry* no-outgoing-edge
condition; generic completeness of BSCC enumeration is a separate theorem. -/
theorem bottomClasses_closed {n : ℕ} (K : RationalMarkovMatrix n)
    (C : Finset (Fin n)) (h : C ∈ bottomClasses K) :
    ∀ x ∈ C, ∀ z : Fin n, 0 < K.entry x z → z ∈ C := by
  have hc : closedB K C = true := (Finset.mem_filter.mp h).2.2
  simpa [closedB] using hc

end C10
end ReverseSolver
end PermanssonResearch