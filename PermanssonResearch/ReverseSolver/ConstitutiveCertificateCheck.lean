import PermanssonResearch.ReverseSolver.ExecutableConstitutiveSelection
import Mathlib.Tactic

/-!
# C10 — exact-rational receipt checking

This checker operates on already validated, typed Lean input values. JSON
parsing, raw-byte provenance, external-model identification, and the
missing numerical-to-canonical-path equality are distinct boundaries.
-/
namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

/-- One frozen numerical margin receipt with complete candidate margins,
selected optimal index and all exact ties. -/
structure MarginReceipt (n menuSize : ℕ) where
  classTables : MenuCertificate n menuSize
  reportedMargin : Fin menuSize → ℚ
  selectedIndex : Fin menuSize
  reportedOptimum : ℚ
  ties : List (Fin menuSize)

/-- A claimed numerical receipt is accepted only when all its class
absorption tables satisfy exact rational Dirichlet equations and the
maximin results exactly match the computed finite arithmetic. -/
def ReceiptConditions {n menuSize : ℕ}
    (raw : RawInput n menuSize) (checked : CheckedInput raw)
    (receipt : MarginReceipt n menuSize) : Prop :=
  MenuConditions raw checked receipt.classTables ∧
  (∀ i : Fin menuSize,
      receipt.reportedMargin i = numericalMargin raw checked receipt.classTables i) ∧
  receipt.selectedIndex = selectBest raw checked receipt.classTables ∧
  receipt.reportedOptimum = bestMargin raw checked receipt.classTables ∧
  receipt.ties = optimalIndices raw checked receipt.classTables

/-- This checker is decidable using exact ℚ arithmetic and finite inputs. -/
def checkReceipt {n menuSize : ℕ}
    (raw : RawInput n menuSize) (checked : CheckedInput raw)
    (receipt : MarginReceipt n menuSize) : Bool :=
  decide (ReceiptConditions raw checked receipt)

/-- The checker is sound for its explicitly stated numerical equations. -/
theorem checkReceipt_sound {n menuSize : ℕ}
    (raw : RawInput n menuSize) (checked : CheckedInput raw)
    (receipt : MarginReceipt n menuSize)
    (hc : checkReceipt raw checked receipt = true) :
    ReceiptConditions raw checked receipt := by
  simpa [checkReceipt] using hc

/-- A checked receipt cannot announce a non-maximizing chosen candidate. -/
theorem checked_receipt_global_max {n menuSize : ℕ}
    (raw : RawInput n menuSize) (checked : CheckedInput raw)
    (receipt : MarginReceipt n menuSize)
    (hc : checkReceipt raw checked receipt = true)
    (i : Fin menuSize) :
    receipt.reportedMargin i ≤ receipt.reportedOptimum := by
  have h := checkReceipt_sound raw checked receipt hc
  rw [h.2.1 i, h.2.2.2.1]
  exact selected_dominates raw checked receipt.classTables i

end C10
end ReverseSolver
end PermanssonResearch