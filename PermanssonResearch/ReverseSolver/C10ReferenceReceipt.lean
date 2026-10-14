import PermanssonResearch.ReverseSolver.ConstitutiveCertificateCheck
import PermanssonResearch.ReverseSolver.RationalCramerCertification
import Mathlib.Tactic

/-!
# C10 — total proof-carrying rational reference menu and receipt

The reference constructs every rational absorption column from the already
proved nonsingular full-state Dirichlet system. Every accepted nonempty
finite stochastic input receives a full menu and receipt that pass the
independent decidable Lean checker, without an external validity premise.
This is the numerical certificate, not a claim about JSON decoding or
external-model identification.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

/-- The baseline and EVERY listed typed matrix receive separately
computed, exact rational Cramer certificates. -/
def referenceMenuCertificate {n m : ℕ}
    (raw : RawInput n m) (checked : CheckedInput raw) :
    MenuCertificate n m where
  baseline := referenceDirichletCertificate checked.baseline
  members := fun i => referenceDirichletCertificate (checked.members i)

/-- Complete rational reference output with all candidate margins, ties,
and a deterministic first maximizing index. -/
def referenceReceipt {n m : ℕ}
    (raw : RawInput n m) (checked : CheckedInput raw) :
    MarginReceipt n m :=
  let cert := referenceMenuCertificate raw checked
  { classTables := cert
    reportedMargin := numericalMargin raw checked cert
    selectedIndex := selectBest raw checked cert
    reportedOptimum := bestMargin raw checked cert
    ties := optimalIndices raw checked cert }

/-- Every checked nonempty finite rational menu passes the full exact
Dirichlet checker; the input's proof of positive dimension supplies the
nonvacuity hypothesis rather than an unchecked class condition. -/
theorem referenceMenu_check_true {n m : ℕ}
    (raw : RawInput n m) (checked : CheckedInput raw) :
    checkMenu raw checked (referenceMenuCertificate raw checked) = true := by
  have hn : 0 < n := checked.statesPositive
  haveI : NeZero n := ⟨by omega⟩
  change
    checkDirichlet checked.baseline
        (referenceDirichletCertificate checked.baseline) &&
      decide (∀ i : Fin m,
        checkDirichlet (checked.members i)
          (referenceDirichletCertificate (checked.members i)) = true) = true
  apply (andB_eq_true_iff _ _).mpr
  constructor
  · exact referenceDirichlet_check_true checked.baseline
  · have hm : ∀ i : Fin m,
        checkDirichlet (checked.members i)
          (referenceDirichletCertificate (checked.members i)) = true :=
      fun i => referenceDirichlet_check_true (checked.members i)
    simpa only [decide_eq_true_eq] using hm

/-- The complete constructed reference receipt is accepted for EVERY
valid finite input, not merely for the hand-coded six-state witness. -/
theorem referenceReceipt_check_true {n m : ℕ}
    (raw : RawInput n m) (checked : CheckedInput raw) :
    checkReceipt raw checked (referenceReceipt raw checked) = true := by
  unfold checkReceipt
  apply (andB_eq_true_iff _ _).mpr
  constructor
  · exact referenceMenu_check_true raw checked
  · simp [referenceReceipt]

/-- Full numerical soundness is a consequence of generic reference
acceptance, not an assumption about Python outputs or a magic hash. -/
theorem referenceReceipt_sound {n m : ℕ}
    (raw : RawInput n m) (checked : CheckedInput raw) :
    ReceiptConditions raw checked (referenceReceipt raw checked) :=
  checkReceipt_sound raw checked (referenceReceipt raw checked)
    (referenceReceipt_check_true raw checked)

/-- Every numerical candidate's reported margin is bounded by the
reported optimum of the constructed total reference. -/
theorem referenceReceipt_selected_dominates {n m : ℕ}
    (raw : RawInput n m) (checked : CheckedInput raw) (i : Fin m) :
    (referenceReceipt raw checked).reportedMargin i ≤
      (referenceReceipt raw checked).reportedOptimum :=
  checked_receipt_global_max raw checked (referenceReceipt raw checked)
    (referenceReceipt_check_true raw checked) i

end C10
end ReverseSolver
end PermanssonResearch
