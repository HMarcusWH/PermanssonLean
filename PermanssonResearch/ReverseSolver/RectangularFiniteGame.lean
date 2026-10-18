import PermanssonResearch.ReverseSolver.RationalKernel

/-!
# Finite rectangular games with nature observing the realized control

The finite state already contains all event monitors. Nature observes the
realized control before selecting its row, and can choose independently at
every chronological node. Both players may use real behavioral kernels on
complete realized state/control/nature histories.
-/

namespace PermanssonResearch.ReverseSolver.RectangularFiniteGame

universe uC uΘ

structure Game (C : Type uC) (Θ : Type uΘ) [DecidableEq C] [DecidableEq Θ] (n : ℕ) where
  states_nonempty : 0<n
  options : Fin n → Finset C
  options_nonempty : ∀ y, (options y).Nonempty
  natureOptions : ℕ → Fin n → C → Finset Θ
  nature_nonempty : ∀ t y c, (natureOptions t y c).Nonempty
  matrix : ℕ → C → Θ → RationalMarkovMatrix n

abbrev History (C : Type uC) (Θ : Type uΘ) (n : ℕ) := Fin n × List ((C × Θ) × Fin n)

def appendTrace {C : Type uC} {Θ : Type uΘ} {n : ℕ}
    (h : History C Θ n) (a : C × Θ) (z : Fin n) : History C Θ n :=
  (h.1,h.2++[(a,z)])

variable {C : Type uC} {Θ : Type uΘ} [DecidableEq C] [DecidableEq Θ]
    [Fintype C] [Fintype Θ] {n : ℕ}

structure Controller (G : Game C Θ n) where
  weight : ℕ → History C Θ n → Fin n → C → ℝ
  nonnegative : ∀ t h y c, 0≤weight t h y c
  normalized : ∀ t h y, ∑ c : C, weight t h y c=1
  supported : ∀ t h y c, c ∉ G.options y → weight t h y c=0

structure Nature (G : Game C Θ n) where
  weight : ℕ → History C Θ n → Fin n → C → Θ → ℝ
  nonnegative : ∀ t h y c θ, 0≤weight t h y c θ
  normalized : ∀ t h y c, ∑ θ : Θ, weight t h y c θ=1
  supported : ∀ t h y c θ, θ ∉ G.natureOptions t y c → weight t h y c θ=0

def rowScore (G : Game C Θ n) (v : Fin n → ℚ) (t : ℕ)
    (y : Fin n) (c : C) (θ : Θ) : ℚ := ∑ z : Fin n, (G.matrix t c θ).entry y z*v z

noncomputable def minimizingRow (G : Game C Θ n) (v : Fin n → ℚ)
    (t : ℕ) (y : Fin n) (c : C) : Θ := Classical.choose
  (Finset.exists_min_image (G.natureOptions t y c) (rowScore G v t y c) (G.nature_nonempty t y c))

theorem minimizingRow_mem (G : Game C Θ n) (v : Fin n → ℚ)
    (t : ℕ) (y : Fin n) (c : C) : minimizingRow G v t y c ∈ G.natureOptions t y c :=
  (Classical.choose_spec (Finset.exists_min_image (G.natureOptions t y c)
    (rowScore G v t y c) (G.nature_nonempty t y c))).1

noncomputable def minScore (G : Game C Θ n) (v : Fin n → ℚ) (t : ℕ) (y : Fin n) (c : C) : ℚ :=
  rowScore G v t y c (minimizingRow G v t y c)

theorem minScore_le_row (G : Game C Θ n) (v : Fin n → ℚ)
    (t : ℕ) (y : Fin n) (c : C) (θ : Θ) (hθ : θ ∈ G.natureOptions t y c) :
    minScore G v t y c≤rowScore G v t y c θ :=
  (Classical.choose_spec (Finset.exists_min_image (G.natureOptions t y c)
    (rowScore G v t y c) (G.nature_nonempty t y c))).2 θ hθ

noncomputable def maximizingControl (G : Game C Θ n) (v : Fin n → ℚ)
    (t : ℕ) (y : Fin n) : C := Classical.choose
  (Finset.exists_max_image (G.options y) (minScore G v t y) (G.options_nonempty y))

theorem maximizingControl_mem (G : Game C Θ n) (v : Fin n → ℚ)
    (t : ℕ) (y : Fin n) : maximizingControl G v t y ∈ G.options y :=
  (Classical.choose_spec (Finset.exists_max_image (G.options y)
    (minScore G v t y) (G.options_nonempty y))).1

theorem minScore_le_max (G : Game C Θ n) (v : Fin n → ℚ)
    (t : ℕ) (y : Fin n) (c : C) (hc : c ∈ G.options y) :
    minScore G v t y c≤minScore G v t y (maximizingControl G v t y) :=
  (Classical.choose_spec (Finset.exists_max_image (G.options y)
    (minScore G v t y) (G.options_nonempty y))).2 c hc

noncomputable def value (G : Game C Θ n) (reward : Fin n → ℚ) : ℕ → ℕ → Fin n → ℚ
  | 0, _, y => reward y
  | r+1, t, y => minScore G (value G reward r (t+1)) t y
      (maximizingControl G (value G reward r (t+1)) t y)

noncomputable def continuation (G : Game C Θ n) (reward : Fin n → ℚ)
    (σ : Controller G) (η : Nature G) : ℕ → ℕ → History C Θ n → Fin n → ℝ
  | 0, _, _, y => (reward y : ℝ)
  | r+1, t, h, y => ∑ c : C, σ.weight t h y c *
      ∑ θ : Θ, η.weight t h y c θ * ∑ z : Fin n,
        ((G.matrix t c θ).entry y z : ℝ) *
          continuation G reward σ η r (t+1) (appendTrace h (c,θ) z) z

noncomputable def maximizingController (G : Game C Θ n) (reward : Fin n → ℚ) (N : ℕ) :
    Controller G where
  weight t h y c := if c=maximizingControl G (value G reward (N-(t+1)) (t+1)) t y then 1 else 0
  nonnegative t h y c := by split <;> norm_num
  normalized t h y := by simp
  supported t h y c hc := by
    have hn : c≠maximizingControl G (value G reward (N-(t+1)) (t+1)) t y := by
      intro he
      exact hc (he ▸ maximizingControl_mem G _ t y)
    simp [hn]

noncomputable def minimizingNature (G : Game C Θ n) (reward : Fin n → ℚ) (N : ℕ) :
    Nature G where
  weight t h y c θ := if θ=minimizingRow G (value G reward (N-(t+1)) (t+1)) t y c then 1 else 0
  nonnegative t h y c θ := by split <;> norm_num
  normalized t h y c := by simp
  supported t h y c θ hθ := by
    have hn : θ≠minimizingRow G (value G reward (N-(t+1)) (t+1)) t y c := by
      intro he
      exact hθ (he ▸ minimizingRow_mem G _ t y c)
    simp [hn]

theorem minimizingNature_upper (G : Game C Θ n) (reward : Fin n → ℚ) (N : ℕ)
    (σ : Controller G) (r t : ℕ) (h : History C Θ n) (y : Fin n) (hr : t+r=N) :
    continuation G reward σ (minimizingNature G reward N) r t h y≤(value G reward r t y : ℝ) := by
  induction r generalizing t h y with
  | zero => exact le_rfl
  | succ r ih =>
      have hsub : N-(t+1)=r := by omega
      have hw (c : C) (θ : Θ) : (minimizingNature G reward N).weight t h y c θ =
          (if θ=minimizingRow G (value G reward r (t+1)) t y c then 1 else 0) := by
        simp only [minimizingNature,hsub]
      change (∑ c : C, σ.weight t h y c * ∑ θ : Θ,
        (minimizingNature G reward N).weight t h y c θ * ∑ z : Fin n,
          ((G.matrix t c θ).entry y z : ℝ)*continuation G reward σ (minimizingNature G reward N)
            r (t+1) (appendTrace h (c,θ) z) z)≤_
      simp only [hw,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      calc
        _ ≤ ∑ c : C, σ.weight t h y c*(minScore G (value G reward r (t+1)) t y c : ℝ) := by
          apply Finset.sum_le_sum
          intro c _
          apply mul_le_mul_of_nonneg_left _ (σ.nonnegative t h y c)
          simp only [minScore,rowScore,Rat.cast_sum,Rat.cast_mul]
          apply Finset.sum_le_sum
          intro z _
          apply mul_le_mul_of_nonneg_left (ih (t+1) _ z (by omega))
          exact_mod_cast (G.matrix t c _).entry_nonneg y z
        _ ≤ ∑ c : C, σ.weight t h y c*(value G reward (r+1) t y : ℝ) := by
          apply Finset.sum_le_sum
          intro c _
          by_cases hc : c ∈ G.options y
          · apply mul_le_mul_of_nonneg_left _ (σ.nonnegative t h y c)
            exact_mod_cast minScore_le_max G (value G reward r (t+1)) t y c hc
          · simp [σ.supported t h y c hc]
        _ = _ := by rw [← Finset.sum_mul,σ.normalized,one_mul]

theorem maximizingController_lower (G : Game C Θ n) (reward : Fin n → ℚ) (N : ℕ)
    (η : Nature G) (r t : ℕ) (h : History C Θ n) (y : Fin n) (hr : t+r=N) :
    (value G reward r t y : ℝ)≤continuation G reward (maximizingController G reward N) η r t h y := by
  induction r generalizing t h y with
  | zero => exact le_rfl
  | succ r ih =>
      have hsub : N-(t+1)=r := by omega
      let c := maximizingControl G (value G reward r (t+1)) t y
      have hw (a : C) : (maximizingController G reward N).weight t h y a =
          (if a=c then 1 else 0) := by simp only [maximizingController,hsub,c]
      change _≤∑ a : C, (maximizingController G reward N).weight t h y a * ∑ θ : Θ,
        η.weight t h y a θ * ∑ z : Fin n, ((G.matrix t a θ).entry y z : ℝ)*
          continuation G reward (maximizingController G reward N) η r (t+1) (appendTrace h (a,θ) z) z
      simp only [hw,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      calc
        _ = ∑ θ : Θ, η.weight t h y c θ*(value G reward (r+1) t y : ℝ) := by
          rw [← Finset.sum_mul,η.normalized,one_mul]
        _ ≤ ∑ θ : Θ, η.weight t h y c θ*(rowScore G (value G reward r (t+1)) t y c θ : ℝ) := by
          apply Finset.sum_le_sum
          intro θ _
          by_cases hθ : θ ∈ G.natureOptions t y c
          · apply mul_le_mul_of_nonneg_left _ (η.nonnegative t h y c θ)
            exact_mod_cast minScore_le_row G (value G reward r (t+1)) t y c θ hθ
          · simp [η.supported t h y c θ hθ]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro θ _
          apply mul_le_mul_of_nonneg_left _ (η.nonnegative t h y c θ)
          simp only [rowScore,Rat.cast_sum,Rat.cast_mul]
          apply Finset.sum_le_sum
          intro z _
          apply mul_le_mul_of_nonneg_left (ih (t+1) _ z (by omega))
          exact_mod_cast (G.matrix t c θ).entry_nonneg y z

theorem deterministic_saddle_attains (G : Game C Θ n) (reward : Fin n → ℚ) (N : ℕ)
    (y : Fin n) : continuation G reward (maximizingController G reward N)
      (minimizingNature G reward N) N 0 (y,[]) y=(value G reward N 0 y : ℝ) := by
  exact le_antisymm (minimizingNature_upper G reward N _ N 0 _ y (by omega))
    (maximizingController_lower G reward N _ N 0 _ y (by omega))

end PermanssonResearch.ReverseSolver.RectangularFiniteGame
