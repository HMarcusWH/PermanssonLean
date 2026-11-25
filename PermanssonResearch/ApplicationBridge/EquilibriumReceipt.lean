import PermanssonResearch.Games.BimatrixRegret
import PermanssonResearch.Games.ApproximateDiscounted

/-! A literal rational receipt checks every action before it is interpreted as
a real mixed-deviation bound. No external solver flag is a theorem premise. -/
namespace PermanssonResearch.ApplicationBridge.EquilibriumReceipt

open ApproxEquilibrium
set_option autoImplicit false

theorem checked_profile {m n : ℕ}
    (R : Fin m → Fin n → ℚ) (C : Fin n → Fin m → ℚ)
    (p : Fin m → ℚ) (q : Fin n → ℚ) (ε : ℚ)
    (h : checkNash R C p q ε = true) :
    ∃ hp : Simplex p, ∃ hq : Simplex q,
      ApproxNash (fun i j => (R i j : ℝ)) (fun j i => (C j i : ℝ))
        (realRow p hp) (realRow q hq) (ε : ℝ) := by
  have hc := (checkNash_iff R C p q ε).1 h
  exact ⟨hc.1, hc.2.1, (rationalChecks_iff_real R C p q hc.1 hc.2.1 ε).1 hc⟩

end PermanssonResearch.ApplicationBridge.EquilibriumReceipt
