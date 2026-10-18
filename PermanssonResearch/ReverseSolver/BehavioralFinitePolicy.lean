import PermanssonResearch.ReverseSolver.FiniteMonitor

/-!
# Real behavioral kernels on complete chronological action/state histories

A history records the initial physical state and every realized control and
successor state. Behavioral probabilities are real. Inadmissible controls have
zero weight, also on histories with zero probability. No division by a prefix
probability is used anywhere.
-/

namespace PermanssonResearch.ReverseSolver.FiniteMonitor

open ControlledKernel

universe uC uS

abbrev TraceHistory (C : Type uC) (n : ℕ) := Fin n × List (C × Fin n)

def appendTrace {C : Type uC} {n : ℕ} (h : TraceHistory C n)
    (c : C) (z : Fin n) : TraceHistory C n := (h.1, h.2 ++ [(c,z)])

structure BehavioralPolicy {C : Type uC} [DecidableEq C] [Fintype C] {n : ℕ}
    (sys : FiniteControlSystem C n) where
  weight : ℕ → TraceHistory C n → Fin n → C → ℝ
  nonnegative : ∀ t h y c, 0 ≤ weight t h y c
  normalized : ∀ t h y, ∑ c : C, weight t h y c = 1
  supported : ∀ t h y c, c ∉ sys.options y → weight t h y c = 0

variable {C : Type uC} [DecidableEq C] [Fintype C] {n : ℕ} {S : Type uS}

/-- Monitor pushforward of an explicitly supplied realized control/state word. -/
def run (M : Monitor C n S) : ℕ → Fin n → S → List (C × Fin n) → Fin n × S
  | _, y, s, [] => (y,s)
  | t, y, s, (c,z)::xs => run M (t+1) z (M.update t s y c z) xs

theorem run_append (M : Monitor C n S) (t : ℕ) (y : Fin n) (s : S)
    (xs ys : List (C × Fin n)) :
    run M t y s (xs ++ ys) =
      run M (t+xs.length) (run M t y s xs).1 (run M t y s xs).2 ys := by
  induction xs generalizing t y s with
  | nil => simp [run]
  | cons a xs ih =>
      rcases a with ⟨c,z⟩
      simpa [run, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (t+1) z (M.update t s y c z)

/-- The actual chronological product of behavioral probabilities and rows. -/
def traceMass (sys : FiniteControlSystem C n) (σ : BehavioralPolicy sys) :
    ℕ → TraceHistory C n → Fin n → List (C × Fin n) → ℝ
  | _, _, _, [] => 1
  | t, h, y, (c,z)::xs => σ.weight t h y c * ((sys.matrix c).entry y z : ℝ) *
      traceMass sys σ (t+1) (appendTrace h c z) z xs

/-- Enumerate all realized controls and physical successors independently. -/
noncomputable def traceWords (C : Type uC) [Fintype C] (n : ℕ) :
    ℕ → List (List (C × Fin n))
  | 0 => [[]]
  | r+1 => ((Finset.univ : Finset (C × Fin n)).toList).flatMap
      (fun a => (traceWords C n r).map (a :: ·))

noncomputable def traceExpectation (sys : FiniteControlSystem C n)
    (M : Monitor C n S) (σ : BehavioralPolicy sys) (r t : ℕ)
    (h : TraceHistory C n) (y : Fin n) (s : S) : ℝ :=
  ((traceWords C n r).map (fun xs => traceMass sys σ t h y xs *
    (M.reward (run M t y s xs).1 (run M t y s xs).2 : ℝ))).sum

/-- Unconditional continuation; every zero-mass prefix is still well defined. -/
noncomputable def behavioralValue (sys : FiniteControlSystem C n)
    (M : Monitor C n S) (σ : BehavioralPolicy sys) :
    ℕ → ℕ → TraceHistory C n → Fin n → S → ℝ
  | 0, _, _, y, s => (M.reward y s : ℝ)
  | r+1, t, h, y, s => ∑ c : C, σ.weight t h y c *
      ∑ z : Fin n, ((sys.matrix c).entry y z : ℝ) *
        behavioralValue sys M σ r (t+1) (appendTrace h c z) z (M.update t s y c z)

private theorem list_sum_flatMap {α β : Type*} (xs : List α)
    (f : α → List β) (g : β → ℝ) :
    ((xs.flatMap f).map g).sum = (xs.map (fun x => ((f x).map g).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

/-- The actual chronological word law pushes forward to the monitor recursion. -/
theorem traceExpectation_eq_behavioralValue (sys : FiniteControlSystem C n)
    (M : Monitor C n S) (σ : BehavioralPolicy sys) (r t : ℕ)
    (h : TraceHistory C n) (y : Fin n) (s : S) :
    traceExpectation sys M σ r t h y s = behavioralValue sys M σ r t h y s := by
  induction r generalizing t h y s with
  | zero => simp [traceExpectation, traceWords, traceMass, run, behavioralValue]
  | succ r ih =>
      unfold traceExpectation
      simp only [traceWords, list_sum_flatMap, List.map_map, Function.comp_def,
        traceMass, run]
      simp_rw [mul_assoc, List.sum_map_mul_left]
      simp_rw [← mul_assoc]
      change (((Finset.univ : Finset (C × Fin n)).toList).map
        (fun a => σ.weight t h y a.1 * ((sys.matrix a.1).entry y a.2 : ℝ) *
          traceExpectation sys M σ r (t+1) (appendTrace h a.1 a.2) a.2
            (M.update t s y a.1 a.2))).sum = _
      rw [← List.sum_toFinset _ (Finset.nodup_toList _)]
      simp only [Finset.toList_toFinset, Fintype.sum_prod_type]
      simp_rw [ih, mul_assoc, ← Finset.mul_sum]
      rfl

/-- The chronological law has unit mass, independently of monitor choices. -/
theorem behavioralValue_constant_one (sys : FiniteControlSystem C n)
    (M : Monitor C n S) (σ : BehavioralPolicy sys)
    (hr : ∀ y s, M.reward y s = 1) (r t : ℕ)
    (h : TraceHistory C n) (y : Fin n) (s : S) :
    behavioralValue sys M σ r t h y s = 1 := by
  induction r generalizing t h y s with
  | zero => simp [behavioralValue, hr]
  | succ r ih =>
      simp only [behavioralValue, ih, mul_one]
      have rows : ∀ c : C, ∑ z : Fin n, ((sys.matrix c).entry y z : ℝ) = 1 := by
        intro c
        exact_mod_cast (sys.matrix c).row_sum_one y
      simp only [rows, mul_one]
      exact σ.normalized t h y

end PermanssonResearch.ReverseSolver.FiniteMonitor
