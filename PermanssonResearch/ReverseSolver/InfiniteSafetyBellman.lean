import PermanssonResearch.ReverseSolver.ControlledKernel
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic

/-! Decreasing finite-horizon safety values, their actual limit, and an
attaining stationary selector for the limiting Bellman equation. -/

open Filter
open scoped Topology

namespace PermanssonResearch.ReverseSolver.InfiniteSafety

open ControlledKernel

noncomputable section

variable {C : Type*} [DecidableEq C] {n : ℕ}

def rowScore (sys : FiniteControlSystem C n) (v : Fin n → ℝ)
    (y : Fin n) (c : C) : ℝ := ∑ z : Fin n, ((sys.matrix c).entry y z : ℝ)*v z

def maximum (sys : FiniteControlSystem C n) (v : Fin n → ℝ) (y : Fin n) : ℝ :=
  (sys.options y).sup' (sys.options_nonempty y) (rowScore sys v y)

def step (sys : FiniteControlSystem C n) (G : Finset (Fin n))
    (v : Fin n → ℝ) (y : Fin n) : ℝ := if y ∈ G then maximum sys v y else 0

def horizonValue (sys : FiniteControlSystem C n) (G : Finset (Fin n)) :
    ℕ → Fin n → ℝ
  | 0, y => if y ∈ G then 1 else 0
  | k+1, y => step sys G (horizonValue sys G k) y

theorem rowScore_mono (sys : FiniteControlSystem C n) {v w : Fin n → ℝ}
    (h : ∀ z, v z≤w z) (y : Fin n) (c : C) : rowScore sys v y c≤rowScore sys w y c := by
  apply Finset.sum_le_sum
  intro z _
  exact mul_le_mul_of_nonneg_left (h z) (by exact_mod_cast (sys.matrix c).entry_nonneg y z)

theorem rowScore_one (sys : FiniteControlSystem C n) (y : Fin n) (c : C) :
    rowScore sys (fun _ => 1) y c=1 := by
  simp only [rowScore,mul_one]
  exact_mod_cast (sys.matrix c).row_sum_one y

theorem rowScore_nonnegative (sys : FiniteControlSystem C n) {v : Fin n → ℝ}
    (h : ∀ z, 0≤v z) (y : Fin n) (c : C) : 0≤rowScore sys v y c := by
  exact Finset.sum_nonneg (fun z _ => mul_nonneg
    (by exact_mod_cast (sys.matrix c).entry_nonneg y z) (h z))

theorem rowScore_le_maximum (sys : FiniteControlSystem C n) (v : Fin n → ℝ)
    (y : Fin n) (c : C) (hc : c ∈ sys.options y) : rowScore sys v y c≤maximum sys v y :=
  Finset.le_sup' (rowScore sys v y) hc

theorem maximum_mono (sys : FiniteControlSystem C n) {v w : Fin n → ℝ}
    (h : ∀ z, v z≤w z) (y : Fin n) : maximum sys v y≤maximum sys w y := by
  apply Finset.sup'_le
  intro c hc
  exact (rowScore_mono sys h y c).trans (rowScore_le_maximum sys w y c hc)

theorem maximum_bounds (sys : FiniteControlSystem C n) {v : Fin n → ℝ}
    (h : ∀ z, 0≤v z ∧ v z≤1) (y : Fin n) : 0≤maximum sys v y ∧ maximum sys v y≤1 := by
  constructor
  · obtain ⟨c,hc⟩ := sys.options_nonempty y
    exact (rowScore_nonnegative sys (fun z => (h z).1) y c).trans
      (rowScore_le_maximum sys v y c hc)
  · apply Finset.sup'_le
    intro c _
    exact (rowScore_mono sys (fun z => (h z).2) y c).trans_eq (rowScore_one sys y c)

theorem step_mono (sys : FiniteControlSystem C n) (G : Finset (Fin n))
    {v w : Fin n → ℝ} (h : ∀ z, v z≤w z) (y : Fin n) : step sys G v y≤step sys G w y := by
  by_cases hy : y ∈ G
  · simpa only [step,if_pos hy] using maximum_mono sys h y
  · simp only [step,if_neg hy,le_refl]

theorem horizonValue_bounds (sys : FiniteControlSystem C n) (G : Finset (Fin n))
    (k : ℕ) (y : Fin n) : 0≤horizonValue sys G k y ∧ horizonValue sys G k y≤1 := by
  induction k generalizing y with
  | zero => by_cases hy : y ∈ G <;> simp [horizonValue,hy]
  | succ k ih =>
      by_cases hy : y ∈ G
      · simpa only [horizonValue,step,if_pos hy] using maximum_bounds sys ih y
      · simp [horizonValue,step,hy]

theorem horizonValue_succ_le (sys : FiniteControlSystem C n) (G : Finset (Fin n))
    (k : ℕ) (y : Fin n) : horizonValue sys G (k+1) y≤horizonValue sys G k y := by
  induction k generalizing y with
  | zero =>
      by_cases hy : y ∈ G
      · simpa only [horizonValue,if_pos hy] using (horizonValue_bounds sys G 1 y).2
      · simp [horizonValue,step,hy]
  | succ k ih => exact step_mono sys G ih y

theorem horizonValue_antitone (sys : FiniteControlSystem C n) (G : Finset (Fin n))
    (y : Fin n) : Antitone (fun k => horizonValue sys G k y) :=
  antitone_nat_of_succ_le (fun k => horizonValue_succ_le sys G k y)

theorem horizonValue_bddBelow (sys : FiniteControlSystem C n) (G : Finset (Fin n))
    (y : Fin n) : BddBelow (Set.range (fun k => horizonValue sys G k y)) := by
  refine ⟨0,?_⟩
  rintro _ ⟨k,rfl⟩
  exact (horizonValue_bounds sys G k y).1

def limitValue (sys : FiniteControlSystem C n) (G : Finset (Fin n)) (y : Fin n) : ℝ :=
  ⨅ k : ℕ, horizonValue sys G k y

theorem limitValue_nonnegative (sys : FiniteControlSystem C n) (G : Finset (Fin n))
    (y : Fin n) : 0≤limitValue sys G y :=
  le_ciInf (fun k => (horizonValue_bounds sys G k y).1)

theorem limitValue_le_horizon (sys : FiniteControlSystem C n) (G : Finset (Fin n))
    (y : Fin n) (k : ℕ) : limitValue sys G y≤horizonValue sys G k y :=
  ciInf_le (horizonValue_bddBelow sys G y) k

theorem limitValue_bounds (sys : FiniteControlSystem C n) (G : Finset (Fin n))
    (y : Fin n) : 0≤limitValue sys G y ∧ limitValue sys G y≤1 :=
  ⟨limitValue_nonnegative sys G y,
    (limitValue_le_horizon sys G y 0).trans (horizonValue_bounds sys G 0 y).2⟩

theorem limitValue_eq_zero_outside (sys : FiniteControlSystem C n) (G : Finset (Fin n))
    (y : Fin n) (hy : y ∉ G) : limitValue sys G y=0 := by
  apply le_antisymm _ (limitValue_nonnegative sys G y)
  simpa only [horizonValue,if_neg hy] using limitValue_le_horizon sys G y 0

theorem horizonValue_tendsto (sys : FiniteControlSystem C n) (G : Finset (Fin n))
    (y : Fin n) : Tendsto (fun k => horizonValue sys G k y) atTop (𝓝 (limitValue sys G y)) :=
  tendsto_atTop_ciInf (horizonValue_antitone sys G y) (horizonValue_bddBelow sys G y)

theorem step_continuous (sys : FiniteControlSystem C n) (G : Finset (Fin n))
    (y : Fin n) : Continuous (fun v : Fin n → ℝ => step sys G v y) := by
  by_cases hy : y ∈ G
  · simp only [step,if_pos hy,maximum]
    apply Continuous.finset_sup'_apply (sys.options_nonempty y)
    intro c _
    apply continuous_finset_sum
    intro z _
    exact continuous_const.mul (continuous_apply z)
  · simpa only [step,if_neg hy] using (continuous_const : Continuous (fun _ : Fin n → ℝ => (0:ℝ)))

/-- Finiteness of controls/states permits the finite maximum and sums to pass
through the decreasing limit. No exchange of an infinite-policy supremum is used. -/
theorem limitValue_fixed_point (sys : FiniteControlSystem C n) (G : Finset (Fin n))
    (y : Fin n) : limitValue sys G y=step sys G (limitValue sys G) y := by
  have hp : Tendsto (fun k => horizonValue sys G k) atTop (𝓝 (limitValue sys G)) :=
    tendsto_pi_nhds.mpr (fun z => horizonValue_tendsto sys G z)
  have hs := ((step_continuous sys G y).tendsto (limitValue sys G)).comp hp
  have hl := (horizonValue_tendsto sys G y).comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hl hs

def stationaryChoice (sys : FiniteControlSystem C n) (G : Finset (Fin n))
    (y : Fin n) : C :=
  Classical.choose ((sys.options y).exists_mem_eq_sup' (sys.options_nonempty y)
    (rowScore sys (limitValue sys G) y))

theorem stationaryChoice_mem (sys : FiniteControlSystem C n) (G : Finset (Fin n))
    (y : Fin n) : stationaryChoice sys G y ∈ sys.options y :=
  (Classical.choose_spec ((sys.options y).exists_mem_eq_sup' (sys.options_nonempty y)
    (rowScore sys (limitValue sys G) y))).1

def stationaryPolicy (sys : FiniteControlSystem C n) (G : Finset (Fin n)) : StateFeedback sys where
  choose := stationaryChoice sys G
  permitted := stationaryChoice_mem sys G

theorem stationaryChoice_fixed_point (sys : FiniteControlSystem C n) (G : Finset (Fin n))
    (y : Fin n) (hy : y ∈ G) :
    limitValue sys G y=rowScore sys (limitValue sys G) y ((stationaryPolicy sys G).choose y) := by
  rw [limitValue_fixed_point,step,if_pos hy]
  exact (Classical.choose_spec ((sys.options y).exists_mem_eq_sup' (sys.options_nonempty y)
    (rowScore sys (limitValue sys G) y))).2

end
end PermanssonResearch.ReverseSolver.InfiniteSafety
