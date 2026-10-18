import PermanssonResearch.ReverseSolver.FiniteMonitor

/-!
# Total rational evaluation and fixed-order tie breaking

The value recursion in this module is executable. Given a fixed linear order
on controls, the selected maximizer is the least admissible maximizing control.
No classical choice is used by either definition.
-/

namespace PermanssonResearch.ReverseSolver.FiniteMonitor

open ControlledKernel

universe uC uS

variable {C : Type uC} [DecidableEq C] {n : ℕ} {S : Type uS}

def maximumScore (sys : FiniteControlSystem C n) (M : Monitor C n S)
    (v : Fin n → S → ℚ) (t : ℕ) (y : Fin n) (s : S) : ℚ :=
  ((sys.options y).image (score sys M v t y s)).max'
    ((sys.options_nonempty y).image _)

theorem maximumScore_eq_selected (sys : FiniteControlSystem C n) (M : Monitor C n S)
    (v : Fin n → S → ℚ) (t : ℕ) (y : Fin n) (s : S) :
    maximumScore sys M v t y s = score sys M v t y s (maximizingControl sys M v t y s) := by
  apply le_antisymm
  · apply Finset.max'_le
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨c,hc,rfl⟩
    exact maximizingControl_dominates sys M v t y s c hc
  · exact Finset.le_max' _ _ (Finset.mem_image.mpr
      ⟨_, maximizingControl_permitted sys M v t y s, rfl⟩)

def computedValue (sys : FiniteControlSystem C n) (M : Monitor C n S) :
    ℕ → ℕ → Fin n → S → ℚ
  | 0, _, y, s => M.reward y s
  | r+1, t, y, s => maximumScore sys M (computedValue sys M r (t+1)) t y s

theorem computedValue_eq_value (sys : FiniteControlSystem C n) (M : Monitor C n S)
    (r t : ℕ) (y : Fin n) (s : S) : computedValue sys M r t y s=value sys M r t y s := by
  induction r generalizing t y s with
  | zero => rfl
  | succ r ih =>
      have he : computedValue sys M r (t+1)=value sys M r (t+1) := by
        funext z q
        exact ih _ _ _
      rw [computedValue, he, maximumScore_eq_selected]
      rfl

section FixedOrder

variable [LinearOrder C]

def maximizingOptions (sys : FiniteControlSystem C n) (M : Monitor C n S)
    (v : Fin n → S → ℚ) (t : ℕ) (y : Fin n) (s : S) : Finset C :=
  (sys.options y).filter (fun c => score sys M v t y s c=maximumScore sys M v t y s)

theorem maximizingOptions_nonempty (sys : FiniteControlSystem C n) (M : Monitor C n S)
    (v : Fin n → S → ℚ) (t : ℕ) (y : Fin n) (s : S) :
    (maximizingOptions sys M v t y s).Nonempty := by
  have hm := Finset.max'_mem ((sys.options y).image (score sys M v t y s))
    ((sys.options_nonempty y).image _)
  rcases Finset.mem_image.mp hm with ⟨c,hc,he⟩
  exact ⟨c, Finset.mem_filter.mpr ⟨hc,he⟩⟩

def leastMaximizingControl (sys : FiniteControlSystem C n) (M : Monitor C n S)
    (v : Fin n → S → ℚ) (t : ℕ) (y : Fin n) (s : S) : C :=
  (maximizingOptions sys M v t y s).min' (maximizingOptions_nonempty sys M v t y s)

theorem leastMaximizingControl_spec (sys : FiniteControlSystem C n) (M : Monitor C n S)
    (v : Fin n → S → ℚ) (t : ℕ) (y : Fin n) (s : S) :
    leastMaximizingControl sys M v t y s ∈ sys.options y ∧
      score sys M v t y s (leastMaximizingControl sys M v t y s)=maximumScore sys M v t y s :=
  Finset.mem_filter.mp (Finset.min'_mem _ _)

def computedMaximizer (sys : FiniteControlSystem C n) (M : Monitor C n S) (N : ℕ) :
    MonitorPolicy sys S where
  choose t y s := leastMaximizingControl sys M (computedValue sys M (N-(t+1)) (t+1)) t y s
  permitted t y s := (leastMaximizingControl_spec sys M _ t y s).1

theorem computedMaximizer_attains (sys : FiniteControlSystem C n) (M : Monitor C n S)
    (N r t : ℕ) (y : Fin n) (s : S) (hr : t+r=N) :
    deterministicValue sys M (computedMaximizer sys M N) r t y s=computedValue sys M r t y s := by
  induction r generalizing t y s with
  | zero => rfl
  | succ r ih =>
      have hsub : N-(t+1)=r := by omega
      let c := (computedMaximizer sys M N).choose t y s
      change (∑ z : Fin n,
        (sys.matrix c).entry y z *
        deterministicValue sys M (computedMaximizer sys M N) r (t+1) z
          (M.update t s y c z)) = _
      calc
        _ = score sys M (computedValue sys M r (t+1)) t y s c := by
          unfold score
          apply Finset.sum_congr rfl
          intro z _
          rw [ih (t+1) z _ (by omega)]
        _ = computedValue sys M (r+1) t y s := by
          simpa only [c, computedMaximizer, hsub, computedValue] using
            (leastMaximizingControl_spec sys M (computedValue sys M r (t+1)) t y s).2

end FixedOrder

end PermanssonResearch.ReverseSolver.FiniteMonitor
