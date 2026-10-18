import PermanssonResearch.ReverseSolver.FiniteOccupancyModel

/-! Objective-independent actual normalized laws of full realized histories,
their state/action marginals, and the exact occupancy flow equations. -/

namespace PermanssonResearch.ReverseSolver.Occupancy
open ControlledKernel ActionTrace MeasureTheory
noncomputable section
variable {C : Type*} [Fintype C] [DecidableEq C] {n : ℕ}

def stepRow (sys : TimeSystem C n) (σ : BehavioralPolicy sys) (t : ℕ) (h : History C n t) :
    Row (C × Fin n) :=
  (σ.control t h).bind (fun c => (matrixRow sys t (last t h) c).map (fun z => (c,z)))

def nextRow (sys : TimeSystem C n) (σ : BehavioralPolicy sys) (t : ℕ) (h : History C n t) :
    Row (History C n (t+1)) := (stepRow sys σ t h).map (fun a => History.snoc h a.1 a.2)

def historyLaw (sys : TimeSystem C n) (σ : BehavioralPolicy sys) (μ : Row (Fin n)) :
    (t : ℕ) → Row (History C n t)
  | 0 => μ.map History.initial
  | t+1 => (historyLaw sys σ μ t).bind (nextRow sys σ t)

theorem nextRow_expect (sys : TimeSystem C n) (σ : BehavioralPolicy sys) (t : ℕ)
    (h : History C n t) (f : History C n (t+1) → ℝ) :
    (nextRow sys σ t h).expect f=(σ.control t h).expect (fun c =>
      (matrixRow sys t (last t h) c).expect (fun z => f (History.snoc h c z))) := by
  rw [nextRow,Row.expect_map,stepRow,Row.expect_bind]
  congr 1
  funext c
  rw [Row.expect_map]

theorem historyLaw_step_expect (sys : TimeSystem C n) (σ : BehavioralPolicy sys)
    (μ : Row (Fin n)) (t : ℕ) (f : History C n (t+1) → ℝ) :
    (historyLaw sys σ μ (t+1)).expect f=(historyLaw sys σ μ t).expect (fun h =>
      (σ.control t h).expect (fun c => (matrixRow sys t (last t h) c).expect
        (fun z => f (History.snoc h c z)))) := by
  rw [historyLaw,Row.expect_bind]
  congr 1
  funext h
  exact nextRow_expect sys σ t h f

theorem historyLaw_prefix_expect (sys : TimeSystem C n) (σ : BehavioralPolicy sys)
    (μ : Row (Fin n)) (t : ℕ) (f : History C n t → ℝ) :
    (historyLaw sys σ μ (t+1)).expect (fun h => f (historyPrefix t h))=(historyLaw sys σ μ t).expect f := by
  rw [historyLaw_step_expect]
  simp [historyPrefix]

def stateRow (sys : TimeSystem C n) (σ : BehavioralPolicy sys) (μ : Row (Fin n)) (t : ℕ) :
    Row (Fin n) := (historyLaw sys σ μ t).map (last t)

def actionRow (sys : TimeSystem C n) (σ : BehavioralPolicy sys) (μ : Row (Fin n)) (t : ℕ) :
    Row (Fin n × C) :=
  (historyLaw sys σ μ t).bind (fun h => (σ.control t h).map (fun c => (last t h,c)))

def stateMass (sys : TimeSystem C n) (σ : BehavioralPolicy sys) (μ : Row (Fin n))
    (t : ℕ) (y : Fin n) : ℝ := (stateRow sys σ μ t).mass y

def actionMass (sys : TimeSystem C n) (σ : BehavioralPolicy sys) (μ : Row (Fin n))
    (t : ℕ) (y : Fin n) (c : C) : ℝ := (actionRow sys σ μ t).mass (y,c)

theorem expect_indicator {A : Type*} [Fintype A] [DecidableEq A] (p : Row A) (a : A) :
    p.expect (fun b => if b=a then 1 else 0)=p.mass a := by
  simp [Row.expect,mul_ite]

theorem expect_sum {A B : Type*} [Fintype A] [Fintype B] (p : Row A) (f : B → A → ℝ) :
    p.expect (fun a => ∑ b : B, f b a)=∑ b : B, p.expect (f b) := by
  simp only [Row.expect,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem expect_mul_const {A : Type*} [Fintype A] (p : Row A) (f : A → ℝ) (r : ℝ) :
    p.expect (fun a => f a*r)=p.expect f*r := by
  simp only [Row.expect,Finset.sum_mul,mul_assoc]

theorem stateMass_eq_expect (sys : TimeSystem C n) (σ : BehavioralPolicy sys)
    (μ : Row (Fin n)) (t : ℕ) (y : Fin n) :
    stateMass sys σ μ t y=(historyLaw sys σ μ t).expect
      (fun h => if last t h=y then 1 else 0) := by
  rw [stateMass,← expect_indicator (stateRow sys σ μ t) y,stateRow,Row.expect_map]

theorem actionMass_eq_expect (sys : TimeSystem C n) (σ : BehavioralPolicy sys)
    (μ : Row (Fin n)) (t : ℕ) (y : Fin n) (c : C) :
    actionMass sys σ μ t y c=(historyLaw sys σ μ t).expect
      (fun h => if last t h=y then (σ.control t h).mass c else 0) := by
  rw [actionMass,← expect_indicator (actionRow sys σ μ t) (y,c),actionRow,Row.expect_bind]
  congr 1
  funext h
  rw [Row.expect_map]
  by_cases hy : last t h=y
  · simpa only [Prod.mk.injEq,hy,true_and,if_pos True.intro] using expect_indicator (σ.control t h) c
  · simp [Prod.mk.injEq,hy]

theorem actionMass_supported (sys : TimeSystem C n) (σ : BehavioralPolicy sys)
    (μ : Row (Fin n)) (t : ℕ) (y : Fin n) (c : C) (hc : c ∉ sys.options t y) :
    actionMass sys σ μ t y c=0 := by
  rw [actionMass_eq_expect]
  have he : (fun h : History C n t =>
      if last t h=y then (σ.control t h).mass c else 0)=fun _ => 0 := by
    funext h
    by_cases hy : last t h=y
    · rw [if_pos hy,σ.supported t h c (by simpa only [hy] using hc)]
    · rw [if_neg hy]
  rw [he,Row.expect_const]

theorem actionMass_outflow (sys : TimeSystem C n) (σ : BehavioralPolicy sys)
    (μ : Row (Fin n)) (t : ℕ) (y : Fin n) :
    (∑ c : C, actionMass sys σ μ t y c)=stateMass sys σ μ t y := by
  simp_rw [actionMass_eq_expect]
  rw [← expect_sum,stateMass_eq_expect]
  congr 1
  funext h
  by_cases hy : last t h=y
  · simp only [if_pos hy]
    exact (σ.control t h).total
  · simp [hy]

theorem stateMass_initial (sys : TimeSystem C n) (σ : BehavioralPolicy sys)
    (μ : Row (Fin n)) (y : Fin n) : stateMass sys σ μ 0 y=μ.mass y := by
  rw [stateMass_eq_expect]
  rw [historyLaw,Row.expect_map]
  exact expect_indicator μ y

theorem stateMass_step (sys : TimeSystem C n) (σ : BehavioralPolicy sys)
    (μ : Row (Fin n)) (t : ℕ) (z : Fin n) :
    stateMass sys σ μ (t+1) z=
      (historyLaw sys σ μ t).expect (fun h => ∑ c : C,
        (σ.control t h).mass c*((sys.matrix t c).entry (last t h) z : ℝ)) := by
  rw [stateMass_eq_expect,historyLaw_step_expect]
  congr 1
  funext h
  unfold Row.expect
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  change (matrixRow sys t (last t h) c).expect
      (fun y => if y=z then 1 else 0)=_
  rw [expect_indicator]
  rfl

theorem stateMass_inflow (sys : TimeSystem C n) (σ : BehavioralPolicy sys)
    (μ : Row (Fin n)) (t : ℕ) (z : Fin n) :
    stateMass sys σ μ (t+1) z=
      ∑ y : Fin n, ∑ c : C, actionMass sys σ μ t y c*((sys.matrix t c).entry y z : ℝ) := by
  rw [stateMass_step]
  simp_rw [actionMass_eq_expect,← expect_mul_const,← expect_sum]
  congr 1
  funext h
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  simp [ite_mul]

def occupancies (sys : TimeSystem C n) (σ : BehavioralPolicy sys) (μ : Row (Fin n)) (N : ℕ) :
    Flow sys μ N where
  state t y := stateMass sys σ μ t.val y
  action t y c := actionMass sys σ μ t.val y c
  state_nonneg t y := (stateRow sys σ μ t.val).nonneg y
  action_nonneg t y c := (actionRow sys σ μ t.val).nonneg (y,c)
  initial := stateMass_initial sys σ μ
  outflow t y := actionMass_outflow sys σ μ t.val y
  inflow t z := stateMass_inflow sys σ μ t.val z
  supported t y c hc := actionMass_supported sys σ μ t.val y c hc

theorem terminal_expect_eq_occupancy (sys : TimeSystem C n) (σ : BehavioralPolicy sys)
    (μ : Row (Fin n)) (N : ℕ) (R : Fin n → ℝ) :
    (historyLaw sys σ μ N).expect (fun h => R (last N h))=
      ∑ y : Fin n, (occupancies sys σ μ N).state (Fin.last N) y*R y := by
  have he := Row.expect_map (historyLaw sys σ μ N) (last N) R
  exact he.symm

section ActualMeasure

/-- Ordinary measurable probability law of the actual finite full history. -/
def actualHistoryMeasure (sys : TimeSystem C n) (σ : BehavioralPolicy sys)
    (μ : Row (Fin n)) (N : ℕ) : Measure (History C n N) := (historyLaw sys σ μ N).measure

instance actualHistoryMeasure_probability (sys : TimeSystem C n) (σ : BehavioralPolicy sys)
    (μ : Row (Fin n)) (N : ℕ) : IsProbabilityMeasure (actualHistoryMeasure sys σ μ N) := by
  unfold actualHistoryMeasure
  infer_instance

theorem actual_terminal_integral_eq_occupancy (sys : TimeSystem C n) (σ : BehavioralPolicy sys)
    (μ : Row (Fin n)) (N : ℕ) (R : Fin n → ℝ) :
    (∫ h, R (last N h) ∂actualHistoryMeasure sys σ μ N)=
      ∑ y : Fin n, (occupancies sys σ μ N).state (Fin.last N) y*R y := by
  rw [actualHistoryMeasure,← Row.expect_eq_integral]
  exact terminal_expect_eq_occupancy sys σ μ N R

end ActualMeasure
end
end PermanssonResearch.ReverseSolver.Occupancy
