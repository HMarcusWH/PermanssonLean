import PermanssonResearch.ReverseSolver.C10ReferenceReceipt
import Mathlib.Tactic

/-!
# C10 — full, input-bound exact-rational execution receipts

The minimal checked certificate has class weights, menu margins, selection,
and ties. This richer receipt additionally checks every state event value,
every per-candidate state effect, and an attained lowest-index worst start.
It is still parameterized by the actual `RawInput` and its proof-carrying
`CheckedInput`; JSON deserialization is not a theorem premise.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

/-- All states attaining the exact original comparison minimum. -/
def worstStartSet {n m : ℕ}
    (raw : RawInput n m) (checked : CheckedInput raw)
    (cert : MenuCertificate n m) (i : Fin m) : Finset (Fin n) :=
  raw.comparison.filter (fun x =>
    numericalEffect raw cert i x = numericalMargin raw checked cert i)

/-- The finite nonempty original comparison set always attains its minimum. -/
theorem worstStartSet_nonempty {n m : ℕ}
    (raw : RawInput n m) (checked : CheckedInput raw)
    (cert : MenuCertificate n m) (i : Fin m) :
    (worstStartSet raw checked cert i).Nonempty := by
  obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image
    raw.comparison (numericalEffect raw cert i)
    checked.comparisonNonempty
  have heq : numericalMargin raw checked cert i =
      numericalEffect raw cert i x := by
    apply le_antisymm
    · exact Finset.inf'_le _ hx
    · exact Finset.le_inf' _ _ (fun y hy => hmin y hy)
  exact ⟨x, Finset.mem_filter.mpr ⟨hx, heq.symm⟩⟩

/-- The least numbered minimizing state, with no arbitrary classical
choice or favorable post-hoc comparison-state restriction. -/
def worstStart {n m : ℕ}
    (raw : RawInput n m) (checked : CheckedInput raw)
    (cert : MenuCertificate n m) (i : Fin m) : Fin n :=
  (worstStartSet raw checked cert i).min'
    (worstStartSet_nonempty raw checked cert i)

/-- Returned worst starts belong to the frozen full comparison set and
exactly attain the mathematical minimum. -/
theorem worstStart_attains {n m : ℕ}
    (raw : RawInput n m) (checked : CheckedInput raw)
    (cert : MenuCertificate n m) (i : Fin m) :
    worstStart raw checked cert i ∈ raw.comparison ∧
      numericalEffect raw cert i (worstStart raw checked cert i) =
        numericalMargin raw checked cert i := by
  have hmem : worstStart raw checked cert i ∈
      worstStartSet raw checked cert i :=
    Finset.min'_mem _ _
  exact Finset.mem_filter.mp hmem

/-- The deterministic worst start is the smallest state among ties. -/
theorem worstStart_le_tied {n m : ℕ}
    (raw : RawInput n m) (checked : CheckedInput raw)
    (cert : MenuCertificate n m) (i : Fin m)
    (x : Fin n) (hx : x ∈ raw.comparison)
    (he : numericalEffect raw cert i x =
      numericalMargin raw checked cert i) :
    worstStart raw checked cert i ≤ x := by
  exact Finset.min'_le (worstStartSet raw checked cert i) x
    (Finset.mem_filter.mpr ⟨hx, he⟩)

/-- Complete reified report, including intermediate per-state numbers. -/
structure FullReceipt (n m : ℕ) where
  core : MarginReceipt n m
  baselineEvent : Fin n → ℚ
  memberEvent : Fin m → Fin n → ℚ
  pointwiseEffect : Fin m → Fin n → ℚ
  worstState : Fin m → Fin n

def FullReceiptConditions {n m : ℕ}
    (raw : RawInput n m) (checked : CheckedInput raw)
    (receipt : FullReceipt n m) : Prop :=
  ReceiptConditions raw checked receipt.core ∧
  (∀ x, receipt.baselineEvent x =
    eventValue receipt.core.classTables.baseline raw.descriptor x) ∧
  (∀ i x, receipt.memberEvent i x =
    eventValue (receipt.core.classTables.members i) raw.descriptor x) ∧
  (∀ i x, receipt.pointwiseEffect i x =
    numericalEffect raw receipt.core.classTables i x) ∧
  (∀ i, receipt.worstState i =
    worstStart raw checked receipt.core.classTables i)

/-- The full checker verifies the whole report, not just its printed
maximum. It does not trust the rational matrix inversion producer. -/
def checkFullReceipt {n m : ℕ}
    (raw : RawInput n m) (checked : CheckedInput raw)
    (receipt : FullReceipt n m) : Bool :=
  checkReceipt raw checked receipt.core &&
    decide
      ((∀ x, receipt.baselineEvent x =
          eventValue receipt.core.classTables.baseline raw.descriptor x) ∧
       (∀ i x, receipt.memberEvent i x =
          eventValue (receipt.core.classTables.members i) raw.descriptor x) ∧
       (∀ i x, receipt.pointwiseEffect i x =
          numericalEffect raw receipt.core.classTables i x) ∧
       (∀ i, receipt.worstState i =
          worstStart raw checked receipt.core.classTables i))

theorem checkFullReceipt_sound {n m : ℕ}
    (raw : RawInput n m) (checked : CheckedInput raw)
    (receipt : FullReceipt n m)
    (hc : checkFullReceipt raw checked receipt = true) :
    FullReceiptConditions raw checked receipt := by
  unfold checkFullReceipt at hc
  obtain ⟨hcore, hfields⟩ := (andB_eq_true_iff _ _).mp hc
  exact ⟨checkReceipt_sound raw checked receipt.core hcore,
    of_decide_eq_true hfields⟩

/-- All fields are produced deterministically from rational arithmetic. -/
def referenceFullReceipt {n m : ℕ}
    (raw : RawInput n m) (checked : CheckedInput raw) :
    FullReceipt n m :=
  let base := referenceReceipt raw checked
  { core := base
    baselineEvent := fun x =>
      eventValue base.classTables.baseline raw.descriptor x
    memberEvent := fun i x =>
      eventValue (base.classTables.members i) raw.descriptor x
    pointwiseEffect := fun i x =>
      numericalEffect raw base.classTables i x
    worstState := fun i =>
      worstStart raw checked base.classTables i }

/-- Total exact-rational *full* reference receipts are accepted for
every successfully checked input, with no empirical or oracle premise. -/
theorem referenceFullReceipt_check_true {n m : ℕ}
    (raw : RawInput n m) (checked : CheckedInput raw) :
    checkFullReceipt raw checked (referenceFullReceipt raw checked) = true := by
  unfold checkFullReceipt
  apply (andB_eq_true_iff _ _).mpr
  constructor
  · exact referenceReceipt_check_true raw checked
  · simp [referenceFullReceipt]

/-- For an accepted receipt the returned worst state is an actual member
of original BR and its effect equals the reported margin. -/
theorem checkedFullReceipt_worstStart {n m : ℕ}
    (raw : RawInput n m) (checked : CheckedInput raw)
    (receipt : FullReceipt n m)
    (hc : checkFullReceipt raw checked receipt = true)
    (i : Fin m) :
    receipt.worstState i ∈ raw.comparison ∧
      receipt.pointwiseEffect i (receipt.worstState i) =
        receipt.core.reportedMargin i := by
  have h := checkFullReceipt_sound raw checked receipt hc
  have hstart := worstStart_attains raw checked receipt.core.classTables i
  rw [h.2.2.2.2 i]
  rw [h.2.2.2.1 i (worstStart raw checked receipt.core.classTables i)]
  rw [h.1.2.1 i]
  exact hstart

end C10
end ReverseSolver
end PermanssonResearch
