import PermanssonResearch.ReverseSolver.Bellman

/-!
# Finite monitors with rational terminal objectives

The monitor reads the realized control before the next physical observation.
Its terminal state never changes the physical stochastic row. The chronological
time and remaining horizon are separate indices throughout.
-/

namespace PermanssonResearch.ReverseSolver.FiniteMonitor

open ControlledKernel

universe uC uS

structure Monitor (C : Type uC) (n : ℕ) (S : Type uS) where
  initial : Fin n → S
  update : ℕ → S → Fin n → C → Fin n → S
  reward : Fin n → S → ℚ

variable {C : Type uC} [DecidableEq C] {n : ℕ} {S : Type uS}

/-- The exact one-stage rational continuation score, including action memory. -/
def score (sys : FiniteControlSystem C n) (M : Monitor C n S)
    (v : Fin n → S → ℚ) (t : ℕ) (y : Fin n) (s : S) (c : C) : ℚ :=
  ∑ z : Fin n, (sys.matrix c).entry y z * v z (M.update t s y c z)

noncomputable def maximizingControl (sys : FiniteControlSystem C n)
    (M : Monitor C n S) (v : Fin n → S → ℚ) (t : ℕ) (y : Fin n) (s : S) : C :=
  Classical.choose (Finset.exists_max_image (sys.options y)
    (score sys M v t y s) (sys.options_nonempty y))

theorem maximizingControl_permitted (sys : FiniteControlSystem C n)
    (M : Monitor C n S) (v : Fin n → S → ℚ) (t : ℕ) (y : Fin n) (s : S) :
    maximizingControl sys M v t y s ∈ sys.options y :=
  (Classical.choose_spec (Finset.exists_max_image (sys.options y)
    (score sys M v t y s) (sys.options_nonempty y))).1

theorem maximizingControl_dominates (sys : FiniteControlSystem C n)
    (M : Monitor C n S) (v : Fin n → S → ℚ) (t : ℕ) (y : Fin n) (s : S)
    (c : C) (hc : c ∈ sys.options y) :
    score sys M v t y s c ≤ score sys M v t y s
      (maximizingControl sys M v t y s) :=
  (Classical.choose_spec (Finset.exists_max_image (sys.options y)
    (score sys M v t y s) (sys.options_nonempty y))).2 c hc

/-- Rational Bellman recursion; `r` transitions remain at chronological time `t`. -/
noncomputable def value (sys : FiniteControlSystem C n) (M : Monitor C n S) :
    ℕ → ℕ → Fin n → S → ℚ
  | 0, _, y, s => M.reward y s
  | r+1, t, y, s => score sys M (value sys M r (t+1)) t y s
      (maximizingControl sys M (value sys M r (t+1)) t y s)

/-- A single control chosen from time, physical state and monitor state. -/
structure MonitorPolicy (sys : FiniteControlSystem C n) (S : Type uS) where
  choose : ℕ → Fin n → S → C
  permitted : ∀ t y s, choose t y s ∈ sys.options y

noncomputable def deterministicMaximizer (sys : FiniteControlSystem C n)
    (M : Monitor C n S) (N : ℕ) : MonitorPolicy sys S where
  choose t y s := maximizingControl sys M (value sys M (N-(t+1)) (t+1)) t y s
  permitted t y s := maximizingControl_permitted sys M _ t y s

/-- Independent forward conditional continuation under a deterministic controller. -/
def deterministicValue (sys : FiniteControlSystem C n) (M : Monitor C n S)
    (π : MonitorPolicy sys S) : ℕ → ℕ → Fin n → S → ℚ
  | 0, _, y, s => M.reward y s
  | r+1, t, y, s => ∑ z : Fin n,
      (sys.matrix (π.choose t y s)).entry y z *
        deterministicValue sys M π r (t+1) z (M.update t s y (π.choose t y s) z)

/-- The chosen time/state/monitor controller attains the rational optimum. -/
theorem monitor_deterministic_maximizer_attains (sys : FiniteControlSystem C n)
    (M : Monitor C n S) (N r t : ℕ) (y : Fin n) (s : S) (horizon : t+r=N) :
    deterministicValue sys M (deterministicMaximizer sys M N) r t y s =
      value sys M r t y s := by
  induction r generalizing t y s with
  | zero => rfl
  | succ r ih =>
      have hsub : N-(t+1)=r := by omega
      have hc : (deterministicMaximizer sys M N).choose t y s =
          maximizingControl sys M (value sys M r (t+1)) t y s := by
        simp only [deterministicMaximizer, hsub]
      change (∑ z : Fin n,
        (sys.matrix ((deterministicMaximizer sys M N).choose t y s)).entry y z *
        deterministicValue sys M (deterministicMaximizer sys M N) r (t+1) z
          (M.update t s y ((deterministicMaximizer sys M N).choose t y s) z)) = _
      rw [hc]
      change _ = ∑ z : Fin n, _
      apply Finset.sum_congr rfl
      intro z _
      rw [ih (t+1) z _ (by omega)]

end PermanssonResearch.ReverseSolver.FiniteMonitor
