import PermanssonResearch.ReverseSolver.ControlledKernel
import PermanssonResearch.StrategicWorld.ActionTrace

/-! Finite time-dependent controlled rows and the exact finite flow contract.
Policies see the initial state and every realized control/successor. The
reconstructed policy is legal at every history, including zero-mass states. -/

namespace PermanssonResearch.ReverseSolver.Occupancy
open ControlledKernel ActionTrace

noncomputable section
variable {C : Type*} [Fintype C] [DecidableEq C] {n : ℕ}

structure TimeSystem (C : Type*) [DecidableEq C] (n : ℕ) where
  states_nonempty : 0<n
  options : ℕ → Fin n → Finset C
  options_nonempty : ∀ t y, (options t y).Nonempty
  matrix : ℕ → C → RationalMarkovMatrix n

inductive History (C : Type*) (n : ℕ) : ℕ → Type _ where
  | initial (y : Fin n) : History C n 0
  | snoc {t : ℕ} (past : History C n t) (control : C) (state : Fin n) : History C n (t+1)
  deriving DecidableEq

def History.zeroEquiv : History C n 0 ≃ Fin n where
  toFun h := match h with | .initial y => y
  invFun := .initial
  left_inv h := by cases h; rfl
  right_inv _ := rfl

def History.succEquiv (t : ℕ) : History C n (t+1) ≃ History C n t × (C × Fin n) where
  toFun h := match h with | .snoc past c z => (past,(c,z))
  invFun h := .snoc h.1 h.2.1 h.2.2
  left_inv h := by cases h; rfl
  right_inv h := by cases h; rfl

instance historyFintype : (t : ℕ) → Fintype (History C n t)
  | 0 => Fintype.ofEquiv (Fin n) History.zeroEquiv.symm
  | t+1 => by
      letI := historyFintype t
      exact Fintype.ofEquiv (History C n t × (C × Fin n)) (History.succEquiv t).symm

instance historyMeasurable (t : ℕ) : MeasurableSpace (History C n t) := ⊤
instance historyDiscrete (t : ℕ) : DiscreteMeasurableSpace (History C n t) := ⟨fun _ => trivial⟩

def last (t : ℕ) : History C n t → Fin n
  | .initial y => y
  | .snoc _ _ z => z

def historyPrefix (t : ℕ) : History C n (t+1) → History C n t
  | .snoc h _ _ => h

structure BehavioralPolicy (sys : TimeSystem C n) where
  control : (t : ℕ) → History C n t → Row C
  supported : ∀ t h c, c ∉ sys.options t (last t h) → (control t h).mass c=0

def matrixRow (sys : TimeSystem C n) (t : ℕ) (y : Fin n) (c : C) : Row (Fin n) where
  mass z := ((sys.matrix t c).entry y z : ℝ)
  nonneg z := by exact_mod_cast (sys.matrix t c).entry_nonneg y z
  total := by exact_mod_cast (sys.matrix t c).row_sum_one y

/-- All LP coordinates are finite. Neither normalization nor [0,1] bounds
are assumptions: they follow from these nonnegative flow equations. -/
structure Flow (sys : TimeSystem C n) (μ : Row (Fin n)) (N : ℕ) where
  state : Fin (N+1) → Fin n → ℝ
  action : Fin N → Fin n → C → ℝ
  state_nonneg : ∀ t y, 0≤state t y
  action_nonneg : ∀ t y c, 0≤action t y c
  initial : ∀ y, state 0 y=μ.mass y
  outflow : ∀ t y, (∑ c : C, action t y c)=state t.castSucc y
  inflow : ∀ t z, state t.succ z=
    ∑ y : Fin n, ∑ c : C, action t y c*((sys.matrix t.val c).entry y z : ℝ)
  supported : ∀ t y c, c ∉ sys.options t.val y → action t y c=0

variable {sys : TimeSystem C n} {μ : Row (Fin n)} {N : ℕ}

theorem Flow.state_total (F : Flow sys μ N) : ∀ t, (∑ y : Fin n, F.state t y)=1 := by
  intro t
  refine Fin.induction ?_ ?_ t
  · simpa only [F.initial] using μ.total
  · intro k ih
    calc
      (∑ z : Fin n, F.state k.succ z)=
          ∑ z : Fin n, ∑ y : Fin n, ∑ c : C,
            F.action k y c*((sys.matrix k.val c).entry y z : ℝ) := by simp_rw [F.inflow]
      _ = ∑ y : Fin n, ∑ c : C, ∑ z : Fin n,
          F.action k y c*((sys.matrix k.val c).entry y z : ℝ) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.sum_comm]
      _ = ∑ y : Fin n, ∑ c : C, F.action k y c := by
        apply Finset.sum_congr rfl
        intro y _
        apply Finset.sum_congr rfl
        intro c _
        rw [← Finset.mul_sum]
        have hr : (∑ z : Fin n, ((sys.matrix k.val c).entry y z : ℝ))=1 := by
          exact_mod_cast (sys.matrix k.val c).row_sum_one y
        rw [hr,mul_one]
      _ = ∑ y : Fin n, F.state k.castSucc y := by simp_rw [F.outflow]
      _ = 1 := ih

theorem Flow.state_le_one (F : Flow sys μ N) (t : Fin (N+1)) (y : Fin n) :
    F.state t y≤1 := by
  have hh := Finset.single_le_sum (fun z (_ : z ∈ Finset.univ) => F.state_nonneg t z)
    (Finset.mem_univ y)
  simpa only [F.state_total t] using hh

theorem Flow.action_le_state (F : Flow sys μ N) (t : Fin N) (y : Fin n) (c : C) :
    F.action t y c≤F.state t.castSucc y := by
  have hh := Finset.single_le_sum (fun a (_ : a ∈ Finset.univ) => F.action_nonneg t y a)
    (Finset.mem_univ c)
  simpa only [F.outflow] using hh

theorem Flow.action_le_one (F : Flow sys μ N) (t : Fin N) (y : Fin n) (c : C) :
    F.action t y c≤1 := (F.action_le_state t y c).trans (F.state_le_one t.castSucc y)

theorem Flow.action_zero_of_state_zero (F : Flow sys μ N) (t : Fin N) (y : Fin n)
    (hy : F.state t.castSucc y=0) (c : C) : F.action t y c=0 := by
  exact le_antisymm (by simpa only [hy] using F.action_le_state t y c) (F.action_nonneg t y c)

def fallback (sys : TimeSystem C n) (t : ℕ) (y : Fin n) : C :=
  Classical.choose (sys.options_nonempty t y)

theorem fallback_permitted (sys : TimeSystem C n) (t : ℕ) (y : Fin n) :
    fallback sys t y ∈ sys.options t y := Classical.choose_spec (sys.options_nonempty t y)

/-- Exact x/d reconstruction. Zero state mass and times after the finite
horizon use a fixed allowed action, so every off-support history is legal. -/
def Flow.markovControl (F : Flow sys μ N) (t : ℕ) (y : Fin n) : Row C := by
  classical
  exact if ht : t<N then
    if hy : 0<F.state ⟨t,by omega⟩ y then {
      mass := fun c => F.action ⟨t,ht⟩ y c/F.state ⟨t,by omega⟩ y
      nonneg := fun c => div_nonneg (F.action_nonneg ⟨t,ht⟩ y c) (le_of_lt hy)
      total := by
        rw [← Finset.sum_div,F.outflow]
        exact div_self (ne_of_gt hy) }
    else Row.pure (fallback sys t y)
  else Row.pure (fallback sys t y)

theorem Flow.markovControl_supported (F : Flow sys μ N) (t : ℕ) (y : Fin n) (c : C)
    (hc : c ∉ sys.options t y) : (F.markovControl t y).mass c=0 := by
  classical
  have hn : fallback sys t y≠c := fun he => hc (he ▸ fallback_permitted sys t y)
  unfold Flow.markovControl
  split_ifs with ht hy
  · simp only
    rw [F.supported ⟨t,ht⟩ y c hc,zero_div]
  · simp [Row.pure,hn]
  · simp [Row.pure,hn]

def Flow.policy (F : Flow sys μ N) : BehavioralPolicy sys where
  control t h := F.markovControl t (last t h)
  supported t h c hc := F.markovControl_supported t (last t h) c hc

theorem Flow.state_mul_markovControl (F : Flow sys μ N) (t : Fin N) (y : Fin n) (c : C) :
    F.state t.castSucc y*(F.markovControl t.val y).mass c=F.action t y c := by
  classical
  unfold Flow.markovControl
  split_ifs with ht hy
  · exact mul_div_cancel₀ _ (ne_of_gt hy)
  · have hz : F.state t.castSucc y=0 := le_antisymm (le_of_not_gt hy) (F.state_nonneg _ y)
    rw [hz,zero_mul,F.action_zero_of_state_zero t y hz c]
  · exact (ht t.isLt).elim

end
end PermanssonResearch.ReverseSolver.Occupancy
