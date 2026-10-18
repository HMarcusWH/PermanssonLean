import PermanssonResearch.ReverseSolver.RectangularFiniteGame
import PermanssonResearch.ReverseSolver.ChronologicalMonitorMeasure

/-!
# Actual chronological product laws and saddle values for the rectangular game

The chronological atom multiplies the controller probability, then nature's
probability conditional on the realized control, then the physical row. This
order is part of the theorem and does not describe a hidden private draw or a
single model committed for the whole horizon.
-/

namespace PermanssonResearch.ReverseSolver.RectangularFiniteGame

open FiniteMonitor

universe uC uΘ
variable {C : Type uC} {Θ : Type uΘ} [DecidableEq C] [DecidableEq Θ]
    [Fintype C] [Fintype Θ] {n : ℕ}

def terminalState : Fin n → List ((C × Θ) × Fin n) → Fin n
  | y, [] => y
  | _, (_,z)::xs => terminalState z xs

def gameMass (G : Game C Θ n) (σ : Controller G) (η : Nature G) :
    ℕ → History C Θ n → Fin n → List ((C × Θ) × Fin n) → ℝ
  | _, _, _, [] => 1
  | t, h, y, ((c,θ),z)::xs => σ.weight t h y c*η.weight t h y c θ*
      ((G.matrix t c θ).entry y z : ℝ)*gameMass G σ η (t+1) (appendTrace h (c,θ) z) z xs

noncomputable def gameExpectation (G : Game C Θ n) (reward : Fin n → ℚ)
    (σ : Controller G) (η : Nature G) (r t : ℕ) (h : History C Θ n) (y : Fin n) : ℝ :=
  ((traceWords (C × Θ) n r).map (fun xs =>
    gameMass G σ η t h y xs*(reward (terminalState y xs) : ℝ))).sum

private theorem list_sum_flatMap {A B : Type*} (xs : List A) (f : A → List B) (g : B → ℝ) :
    ((xs.flatMap f).map g).sum=(xs.map (fun a => ((f a).map g).sum)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [List.flatMap_cons,List.map_append,List.sum_append,ih]

/-- Actual independently enumerated chronological game law equals the
unconditional continuation recursion at every supplied prefix. -/
theorem gameExpectation_eq_continuation (G : Game C Θ n) (reward : Fin n → ℚ)
    (σ : Controller G) (η : Nature G) (r t : ℕ) (h : History C Θ n) (y : Fin n) :
    gameExpectation G reward σ η r t h y=continuation G reward σ η r t h y := by
  induction r generalizing t h y with
  | zero => simp [gameExpectation,traceWords,gameMass,terminalState,continuation]
  | succ r ih =>
      unfold gameExpectation
      simp only [traceWords,list_sum_flatMap,List.map_map,Function.comp_def,gameMass,terminalState]
      simp_rw [mul_assoc,List.sum_map_mul_left]
      simp_rw [← mul_assoc]
      change (((Finset.univ : Finset ((C × Θ) × Fin n)).toList).map
        (fun a => σ.weight t h y a.1.1*η.weight t h y a.1.1 a.1.2*
          ((G.matrix t a.1.1 a.1.2).entry y a.2 : ℝ)*
            gameExpectation G reward σ η r (t+1) (appendTrace h a.1 a.2) a.2)).sum = _
      rw [← List.sum_toFinset _ (Finset.nodup_toList _)]
      simp only [Finset.toList_toFinset,Fintype.sum_prod_type]
      simp_rw [ih,mul_assoc,← Finset.mul_sum]
      rfl

theorem gameMass_nonnegative (G : Game C Θ n) (σ : Controller G) (η : Nature G)
    (t : ℕ) (h : History C Θ n) (y : Fin n) (xs : List ((C × Θ) × Fin n)) :
    0≤gameMass G σ η t h y xs := by
  induction xs generalizing t h y with
  | nil => norm_num [gameMass]
  | cons a xs ih =>
      exact mul_nonneg (mul_nonneg (mul_nonneg (σ.nonnegative t h y a.1.1)
        (η.nonnegative t h y a.1.1 a.1.2))
        (by exact_mod_cast (G.matrix t a.1.1 a.1.2).entry_nonneg y a.2)) (ih _ _ _)

theorem continuation_constant_one (G : Game C Θ n) (σ : Controller G) (η : Nature G)
    (r t : ℕ) (h : History C Θ n) (y : Fin n) :
    continuation G (fun _ => 1) σ η r t h y=1 := by
  induction r generalizing t h y with
  | zero => norm_num [continuation]
  | succ r ih =>
      simp only [continuation,ih,mul_one]
      have rows : ∀ c θ, (∑ z : Fin n, ((G.matrix t c θ).entry y z : ℝ))=1 := by
        intro c θ
        exact_mod_cast (G.matrix t c θ).row_sum_one y
      simp only [rows,mul_one,η.normalized,σ.normalized]

theorem gameMass_total_one (G : Game C Θ n) (σ : Controller G) (η : Nature G)
    (r t : ℕ) (h : History C Θ n) (y : Fin n) :
    ((traceWords (C × Θ) n r).map (gameMass G σ η t h y)).sum=1 := by
  have hh := gameExpectation_eq_continuation G (fun _ => 1) σ η r t h y
  rw [continuation_constant_one] at hh
  simpa [gameExpectation] using hh

noncomputable def gameLaw (G : Game C Θ n) (σ : Controller G) (η : Nature G)
    (r t : ℕ) (h : History C Θ n) (y : Fin n) :
    FiniteProbabilityLaw (List ((C × Θ) × Fin n)) where
  support := (traceWords (C × Θ) n r).toFinset
  atom xs := if xs ∈ (traceWords (C × Θ) n r).toFinset then gameMass G σ η t h y xs else 0
  nonnegative xs := by split <;> simp [gameMass_nonnegative]
  supported xs hx := by simp [hx]
  normalized := by
    simp only [Finset.sum_ite_mem,Finset.inter_self]
    rw [List.sum_toFinset _ (traceWords_nodup r)]
    exact gameMass_total_one G σ η r t h y

theorem gameLaw_expectation (G : Game C Θ n) (reward : Fin n → ℚ)
    (σ : Controller G) (η : Nature G) (r t : ℕ) (h : History C Θ n) (y : Fin n) :
    (gameLaw G σ η r t h y).expectation (fun xs => (reward (terminalState y xs) : ℝ))=
      gameExpectation G reward σ η r t h y := by
  unfold FiniteProbabilityLaw.expectation gameExpectation
  change (∑ xs ∈ (traceWords (C × Θ) n r).toFinset,
    (if xs ∈ (traceWords (C × Θ) n r).toFinset then gameMass G σ η t h y xs else 0)*
      (reward (terminalState y xs) : ℝ)) = _
  calc
    _ = ∑ xs ∈ (traceWords (C × Θ) n r).toFinset,
        gameMass G σ η t h y xs*(reward (terminalState y xs) : ℝ) := by
      apply Finset.sum_congr rfl
      intro xs hx
      simp only [if_pos hx]
    _ = _ := List.sum_toFinset _ (traceWords_nodup r)

/-- Exact saddle theorem for the actual finite chronological product law.
One deterministic time/state controller protects the value against every
behavioral nature history, and one deterministic time/state/realized-control
nature strategy bounds every behavioral controller history from above. -/
theorem rectangular_game_actual_saddle (G : Game C Θ n) (reward : Fin n → ℚ)
    (N : ℕ) (y : Fin n) :
    (∀ σ : Controller G, gameExpectation G reward σ (minimizingNature G reward N) N 0 (y,[]) y≤
      (value G reward N 0 y : ℝ)) ∧
    (∀ η : Nature G, (value G reward N 0 y : ℝ)≤
      gameExpectation G reward (maximizingController G reward N) η N 0 (y,[]) y) ∧
    gameExpectation G reward (maximizingController G reward N) (minimizingNature G reward N)
      N 0 (y,[]) y=(value G reward N 0 y : ℝ) := by
  simp only [gameExpectation_eq_continuation]
  exact ⟨fun σ => minimizingNature_upper G reward N σ N 0 _ y (by omega),
    fun η => maximizingController_lower G reward N η N 0 _ y (by omega),
    deterministic_saddle_attains G reward N y⟩

noncomputable def lawPayoff (G : Game C Θ n) (reward : Fin n → ℚ)
    (σ : Controller G) (η : Nature G) (N : ℕ) (y : Fin n) : ℝ :=
  (gameLaw G σ η N 0 (y,[]) y).expectation (fun xs => (reward (terminalState y xs) : ℝ))

theorem rectangular_game_law_saddle (G : Game C Θ n) (reward : Fin n → ℚ)
    (N : ℕ) (y : Fin n) :
    (∀ σ : Controller G, lawPayoff G reward σ (minimizingNature G reward N) N y≤
      (value G reward N 0 y : ℝ)) ∧
    (∀ η : Nature G, (value G reward N 0 y : ℝ)≤
      lawPayoff G reward (maximizingController G reward N) η N y) ∧
    lawPayoff G reward (maximizingController G reward N) (minimizingNature G reward N)
      N y=(value G reward N 0 y : ℝ) := by
  simpa only [lawPayoff,gameLaw_expectation] using rectangular_game_actual_saddle G reward N y

end PermanssonResearch.ReverseSolver.RectangularFiniteGame
