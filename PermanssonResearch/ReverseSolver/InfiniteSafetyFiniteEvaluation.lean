import PermanssonResearch.ReverseSolver.InfiniteSafetyBellman
import PermanssonResearch.ReverseSolver.BehavioralInfiniteLaw

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch.ReverseSolver.InfiniteSafety

open ControlledKernel FiniteMonitor

noncomputable section

variable {C : Type*} [DecidableEq C] [Fintype C] {n : ℕ}

def survival (sys : FiniteControlSystem C n) (σ : BehavioralPolicy sys)
    (G : Finset (Fin n)) : ℕ → HistoryState C n → ℝ
  | 0, h => if historySafe G h then 1 else 0
  | k+1, h => ∑ a : C × Fin n,
      outcomeWeight sys σ h a*survival sys σ G k (append h a.1 a.2)

theorem survival_bounds (sys : FiniteControlSystem C n) (σ : BehavioralPolicy sys)
    (G : Finset (Fin n)) (k : ℕ) (h : HistoryState C n) :
    0≤survival sys σ G k h ∧ survival sys σ G k h≤1 := by
  induction k generalizing h with
  | zero => by_cases hh : historySafe G h <;> simp [survival,hh]
  | succ k ih =>
      constructor
      · exact Finset.sum_nonneg (fun a _ => mul_nonneg (outcomeWeight_nonnegative sys σ h a)
          (ih (append h a.1 a.2)).1)
      · calc
          survival sys σ G (k+1) h ≤ ∑ a : C × Fin n, outcomeWeight sys σ h a*1 := by
            apply Finset.sum_le_sum
            intro a _
            exact mul_le_mul_of_nonneg_left (ih _).2 (outcomeWeight_nonnegative sys σ h a)
          _ = 1 := by simpa only [mul_one] using outcomeWeight_total sys σ h

theorem survival_zero_unsafe (sys : FiniteControlSystem C n) (σ : BehavioralPolicy sys)
    (G : Finset (Fin n)) (k : ℕ) (h : HistoryState C n) (hh : ¬ historySafe G h) :
    survival sys σ G k h=0 := by
  induction k generalizing h with
  | zero => simp only [survival,if_neg hh]
  | succ k ih =>
      apply Finset.sum_eq_zero
      intro a _
      have ha : ¬historySafe G (append h a.1 a.2) := fun hs => hh ((historySafe_append G h _ _).mp hs).1
      rw [ih _ ha,mul_zero]

/-- Finite safety under every full real behavioral history is bounded by the
finite Bellman value. The history may already contain arbitrary past controls. -/
theorem survival_le_horizonValue (sys : FiniteControlSystem C n) (σ : BehavioralPolicy sys)
    (G : Finset (Fin n)) (k : ℕ) (h : HistoryState C n) :
    survival sys σ G k h≤horizonValue sys G k (current h) := by
  induction k generalizing h with
  | zero =>
      by_cases hh : historySafe G h
      · simp only [survival,if_pos hh,horizonValue,if_pos (historySafe_current G h hh),le_refl]
      · rw [survival,if_neg hh]
        exact (horizonValue_bounds sys G 0 (current h)).1
  | succ k ih =>
      by_cases hh : historySafe G h
      · rw [horizonValue,step,if_pos (historySafe_current G h hh)]
        calc
          survival sys σ G (k+1) h ≤ ∑ a : C × Fin n,
              outcomeWeight sys σ h a*horizonValue sys G k a.2 := by
            apply Finset.sum_le_sum
            intro a _
            apply mul_le_mul_of_nonneg_left _ (outcomeWeight_nonnegative sys σ h a)
            simpa only [current_append] using ih (append h a.1 a.2)
          _ = ∑ c : C, σ.weight h.word.length (historyEquiv h) (current h) c*
              rowScore sys (horizonValue sys G k) (current h) c := by
            simp only [outcomeWeight,Fintype.sum_prod_type,rowScore,mul_assoc,Finset.mul_sum]
          _ ≤ ∑ c : C, σ.weight h.word.length (historyEquiv h) (current h) c*
              maximum sys (horizonValue sys G k) (current h) := by
            apply Finset.sum_le_sum
            intro c _
            by_cases hc : c ∈ sys.options (current h)
            · exact mul_le_mul_of_nonneg_left (rowScore_le_maximum sys _ _ c hc)
                (σ.nonnegative _ _ _ c)
            · rw [σ.supported _ _ _ c hc,zero_mul,zero_mul]
          _ = maximum sys (horizonValue sys G k) (current h) := by
            rw [← Finset.sum_mul,σ.normalized,one_mul]
      · rw [survival_zero_unsafe sys σ G (k+1) h hh]
        exact (horizonValue_bounds sys G (k+1) (current h)).1

def stationaryBehavioral (sys : FiniteControlSystem C n) (π : StateFeedback sys) :
    BehavioralPolicy sys where
  weight _ _ y c := if c=π.choose y then 1 else 0
  nonnegative _ _ _ _ := by split <;> norm_num
  normalized _ _ _ := by simp
  supported _ _ y c hc := by
    have hn : c≠π.choose y := fun he => hc (he ▸ π.permitted y)
    simp [hn]

theorem survival_stationary_succ (sys : FiniteControlSystem C n) (π : StateFeedback sys)
    (G : Finset (Fin n)) (k : ℕ) (h : HistoryState C n) :
    survival sys (stationaryBehavioral sys π) G (k+1) h =
      ∑ z : Fin n, ((sys.matrix (π.choose (current h))).entry (current h) z : ℝ)*
        survival sys (stationaryBehavioral sys π) G k (append h (π.choose (current h)) z) := by
  simp [survival,outcomeWeight,Fintype.sum_prod_type,stationaryBehavioral,ite_mul]

/-- A stationary selector of the limiting equation protects its value at
every finite horizon. This is the lower bound needed before taking infinity. -/
theorem limitValue_le_stationary_survival (sys : FiniteControlSystem C n)
    (G : Finset (Fin n)) (k : ℕ) (h : HistoryState C n) (hh : historySafe G h) :
    limitValue sys G (current h)≤survival sys (stationaryBehavioral sys (stationaryPolicy sys G)) G k h := by
  induction k generalizing h with
  | zero => simpa only [survival,if_pos hh] using (limitValue_bounds sys G (current h)).2
  | succ k ih =>
      rw [stationaryChoice_fixed_point sys G (current h) (historySafe_current G h hh),
        survival_stationary_succ]
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast
        (sys.matrix ((stationaryPolicy sys G).choose (current h))).entry_nonneg (current h) z)
      by_cases hz : z ∈ G
      · have hs := ih (append h ((stationaryPolicy sys G).choose (current h)) z)
          ((historySafe_append G h _ _).mpr ⟨hh,hz⟩)
        simpa only [current_append] using hs
      · rw [limitValue_eq_zero_outside sys G z hz]
        exact (survival_bounds sys _ G k _).1

theorem limitValue_le_stationary_survival_initial (sys : FiniteControlSystem C n)
    (G : Finset (Fin n)) (k : ℕ) (y : Fin n) :
    limitValue sys G y≤survival sys (stationaryBehavioral sys (stationaryPolicy sys G)) G k (initialHistory y) := by
  by_cases hy : y ∈ G
  · simpa only [current_initial] using limitValue_le_stationary_survival sys G k
      (initialHistory y) ((historySafe_initial G y).mpr hy)
  · rw [limitValue_eq_zero_outside sys G y hy]
    exact (survival_bounds sys _ G k _).1

/-- Exact genuine Markov-kernel-power probability of the literal safe history
predicate. This is not a definition of probability by a Bellman evaluator. -/
theorem kernel_pow_safe_eq_survival (sys : FiniteControlSystem C n) (σ : BehavioralPolicy sys)
    (G : Finset (Fin n)) (k : ℕ) (h : HistoryState C n) :
    ((historyKernel sys σ)^k) h {h' | historySafe G h'}=ENNReal.ofReal (survival sys σ G k h) := by
  have hset : MeasurableSet {h' : HistoryState C n | historySafe G h'} := .of_discrete
  induction k generalizing h with
  | zero =>
      rw [pow_zero]
      change Measure.dirac h {h' | historySafe G h'}=_
      by_cases hh : historySafe G h <;> simp [Measure.dirac_apply' _ hset,survival,hh]
  | succ k ih =>
      have hp : ((historyKernel sys σ)^(k+1)) h {h' | historySafe G h'} =
          ∫⁻ h', ((historyKernel sys σ)^k) h' {h' | historySafe G h'} ∂historyKernel sys σ h := by
        simpa only [Nat.add_comm,pow_one] using
          Kernel.pow_add_apply_eq_lintegral (historyKernel sys σ) 1 k h hset
      rw [hp,historyKernel_lintegral]
      simp_rw [ih]
      rw [survival,ENNReal.ofReal_sum_of_nonneg (fun a _ =>
        mul_nonneg (outcomeWeight_nonnegative sys σ h a) (survival_bounds sys σ G k _).1)]
      apply Finset.sum_congr rfl
      intro a _
      exact (ENNReal.ofReal_mul (outcomeWeight_nonnegative sys σ h a)).symm

end
end PermanssonResearch.ReverseSolver.InfiniteSafety
