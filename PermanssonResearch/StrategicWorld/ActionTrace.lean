import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Finite alternating action traces

A history retains every realized joint action. A behavioral rule is called
before the independent opponent draw and sees only that complete history.
The finite laws below use real, not merely rational, probabilities.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace PermanssonResearch.ActionTrace

set_option autoImplicit false

universe u v

/-- A finite probability row with arbitrary real probabilities. -/
structure Row (α : Type u) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

namespace Row

variable {α : Type u} {β : Type v} [Fintype α] [Fintype β]

noncomputable def expect (p : Row α) (f : α → ℝ) : ℝ := ∑ a, p.mass a * f a

@[simp] theorem expect_const (p : Row α) (c : ℝ) : p.expect (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, p.total]

@[simp] theorem expect_add (p : Row α) (f g : α → ℝ) :
    p.expect (fun a => f a + g a) = p.expect f + p.expect g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

@[simp] theorem expect_sub (p : Row α) (f g : α → ℝ) :
    p.expect (fun a => f a - g a) = p.expect f - p.expect g := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem expect_mul (p : Row α) (c : ℝ) (f : α → ℝ) :
    p.expect (fun a => c * f a) = c * p.expect f := by
  simp [expect, Finset.mul_sum, mul_left_comm]

theorem expect_mono (p : Row α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    p.expect f ≤ p.expect g := by
  exact Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (h a) (p.nonneg a))

theorem abs_expect_le (p : Row α) {f : α → ℝ} {C : ℝ} (h : ∀ a, |f a| ≤ C) :
    |p.expect f| ≤ C := by
  apply abs_le.mpr
  constructor
  · simpa using p.expect_mono (fun a => (abs_le.mp (h a)).1)
  · simpa using p.expect_mono (fun a => (abs_le.mp (h a)).2)

noncomputable def bind (p : Row α) (q : α → Row β) : Row β where
  mass b := ∑ a, p.mass a * (q a).mass b
  nonneg b := Finset.sum_nonneg (fun a _ => mul_nonneg (p.nonneg a) ((q a).nonneg b))
  total := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, Row.total, mul_one]

@[simp] theorem expect_bind (p : Row α) (q : α → Row β) (f : β → ℝ) :
    (p.bind q).expect f = p.expect (fun a => (q a).expect f) := by
  simp only [expect, bind, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

noncomputable def map (p : Row α) (f : α → β) : Row β := by
  classical
  exact {
    mass := fun b => ∑ a, if f a = b then p.mass a else 0
    nonneg := fun b => Finset.sum_nonneg (fun a _ => by
      split_ifs
      · exact p.nonneg a
      · exact le_refl 0)
    total := by
      rw [Finset.sum_comm]
      simp [p.total] }

@[simp] theorem expect_map (p : Row α) (f : α → β) (g : β → ℝ) :
    (p.map f).expect g = p.expect (fun a => g (f a)) := by
  classical
  simp only [expect, map, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

noncomputable def pure [DecidableEq α] (a : α) : Row α where
  mass b := if a = b then 1 else 0
  nonneg _ := by split_ifs <;> norm_num
  total := by simp

@[simp] theorem expect_pure [DecidableEq α] (a : α) (f : α → ℝ) :
    (pure a).expect f = f a := by simp [expect, pure]

/-- The real row gives an actual probability measure, with no approximation. -/
noncomputable def measure [MeasurableSpace α] (p : Row α) : Measure α :=
  ∑ a, ENNReal.ofReal (p.mass a) • Measure.dirac a

instance measure_probability [MeasurableSpace α] (p : Row α) :
    IsProbabilityMeasure p.measure := by
  refine ⟨?_⟩
  simp only [measure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => p.nonneg a), p.total]
  norm_num

@[simp] theorem measure_singleton [MeasurableSpace α] [MeasurableSingletonClass α]
    [DecidableEq α] (p : Row α) (a : α) :
    p.measure {a} = ENNReal.ofReal (p.mass a) := by
  classical
  simp [measure, Measure.dirac_apply', Pi.single_apply]

theorem expect_eq_integral [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : Row α) (f : α → ℝ) : p.expect f = ∫ a, f a ∂p.measure := by
  classical
  rw [integral_fintype (Integrable.of_finite (μ := p.measure) (f := f))]
  simp [expect, measureReal_def, ENNReal.toReal_ofReal (p.nonneg _)]

end Row

/-- The exact alternating word `(Y₀,A₀,...,Aₙ₋₁,Yₙ)`. -/
abbrev History (Y : Type u) (A : Type u) : ℕ → Type u
  | 0 => Y
  | n + 1 => History Y A n × (A × Y)

instance historyFintype (Y : Type u) (A : Type u) [Fintype Y] [Fintype A] :
    (n : ℕ) → Fintype (History Y A n)
  | 0 => inferInstanceAs (Fintype Y)
  | n + 1 => by
      letI := historyFintype Y A n
      exact inferInstanceAs (Fintype (History Y A n × (A × Y)))

instance historyDecidableEq (Y : Type u) (A : Type u) [DecidableEq Y] [DecidableEq A] :
    (n : ℕ) → DecidableEq (History Y A n)
  | 0 => inferInstanceAs (DecidableEq Y)
  | n + 1 => by
      letI := historyDecidableEq Y A n
      exact inferInstanceAs (DecidableEq (History Y A n × (A × Y)))

instance historyMeasurable (Y : Type u) (A : Type u)
    [MeasurableSpace Y] [MeasurableSpace A] :
    (n : ℕ) → MeasurableSpace (History Y A n)
  | 0 => inferInstanceAs (MeasurableSpace Y)
  | n+1 => by
      letI := historyMeasurable Y A n
      exact inferInstanceAs (MeasurableSpace (History Y A n × (A × Y)))

instance historyDiscrete (Y : Type u) (A : Type u)
    [Fintype Y] [Fintype A]
    [MeasurableSpace Y] [MeasurableSpace A]
    [DiscreteMeasurableSpace Y] [DiscreteMeasurableSpace A] :
    (n : ℕ) → DiscreteMeasurableSpace (History Y A n)
  | 0 => inferInstanceAs (DiscreteMeasurableSpace Y)
  | n+1 => by
      haveI := historyDiscrete Y A n
      exact inferInstanceAs (DiscreteMeasurableSpace (History Y A n × (A × Y)))

def last {Y : Type u} {A : Type u} : (n : ℕ) → History Y A n → Y
  | 0, h => h
  | _ + 1, h => h.2.2

/-- The player index is retained explicitly in the game. `physical` is the
actual conditional law after the two actions, including world and update.
The physical law is held fixed under unilateral policy changes. -/
structure Game (Y : Type u) (A : Type u) [Fintype Y] [Fintype A] where
  player : Fin 2
  physical : Y → A → A → Row Y
  opponent : Y → Row A
  reward : Y → A → A → ℝ
  discount : ℝ
  discount_nonneg : 0 ≤ discount
  discount_lt_one : discount < 1

variable {Y : Type u} {A : Type u} [Fintype Y] [Fintype A]

/-- A rule at each complete alternating observed history. Neither the current
opponent action nor the next state is an argument. -/
abbrev BehavioralPolicy (Y : Type u) (A : Type u) [Fintype A] :=
  (n : ℕ) → History Y (A × A) n → Row A

/-- Independent own and opponent draws followed by the fixed physical law. -/
noncomputable def step (G : Game Y A) (σ : BehavioralPolicy Y A)
    (n : ℕ) (h : History Y (A × A) n) : Row ((A × A) × Y) :=
  (σ n h).bind (fun a => (G.opponent (last n h)).bind (fun b =>
    (G.physical (last n h) a b).map (fun z => ((a,b),z))))

noncomputable def next (G : Game Y A) (σ : BehavioralPolicy Y A)
    (n : ℕ) (h : History Y (A × A) n) : Row (History Y (A × A) (n+1)) :=
  (step G σ n h).map (fun z => (h,z))

/-- Consistent finite laws over the actual retained action trace. -/
noncomputable def law (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y) :
    (n : ℕ) → Row (History Y (A × A) n)
  | 0 => μ
  | n + 1 => (law G σ μ n).bind (next G σ n)

@[simp] theorem next_expect (G : Game Y A) (σ : BehavioralPolicy Y A)
    (n : ℕ) (h : History Y (A × A) n) (f : History Y (A × A) (n+1) → ℝ) :
    (next G σ n h).expect f = (σ n h).expect (fun a =>
      (G.opponent (last n h)).expect (fun b =>
        (G.physical (last n h) a b).expect (fun z => f (h,((a,b),z))))) := by
  classical
  unfold next step
  rw [Row.expect_map, Row.expect_bind]
  congr 1
  funext a
  rw [Row.expect_bind]
  congr 1
  funext b
  rw [Row.expect_map]

/-- Exact consistency, for every real test function on the whole prefix. -/
theorem law_prefix_expect (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y)
    (n : ℕ) (f : History Y (A × A) n → ℝ) :
    (law G σ μ (n+1)).expect (fun h => f h.1) = (law G σ μ n).expect f := by
  classical
  simp only [law, Row.expect_bind]
  congr 1
  funext h
  rw [next_expect]
  simp

/-- Exact finite law factorization, including the action subsequently used by
reward. This is the nonanticipating one-step conditional expectation formula. -/
theorem law_step_expect (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y)
    (n : ℕ) (f : History Y (A × A) (n+1) → ℝ) :
    (law G σ μ (n+1)).expect f = (law G σ μ n).expect (fun h =>
      (σ n h).expect (fun a => (G.opponent (last n h)).expect (fun b =>
        (G.physical (last n h) a b).expect (fun z => f (h,((a,b),z)))))) := by
  classical
  rw [law, Row.expect_bind]
  congr 1
  funext h
  exact next_expect G σ n h f

section Canonical

variable [MeasurableSpace Y] [MeasurableSpace A]
  [DiscreteMeasurableSpace Y] [DiscreteMeasurableSpace A]

/-- Each extension row is also an ordinary measurable Markov kernel. -/
noncomputable def nextKernel (G : Game Y A) (σ : BehavioralPolicy Y A) (n : ℕ) :
    Kernel (History Y (A × A) n) (History Y (A × A) (n+1)) where
  toFun h := (next G σ n h).measure
  measurable' := Measurable.of_discrete

instance nextKernel_markov (G : Game Y A) (σ : BehavioralPolicy Y A) (n : ℕ) :
    IsMarkovKernel (nextKernel G σ n) := by
  refine ⟨fun h => ?_⟩
  change IsProbabilityMeasure (next G σ n h).measure
  infer_instance

/-- Ionescu--Tulcea applied to the successive complete histories. The redundant
coordinates retain the actual actions and support the exact canonical extension.
The strategy still sees only the current alternating history, prior to either
current action draw. -/
noncomputable def canonicalLaw (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y) :
    Measure ((n : ℕ) → History Y (A × A) n) := by
  let κ : (n : ℕ) → Kernel ((j : Finset.Iic n) → History Y (A × A) j)
      (History Y (A × A) (n+1)) := fun n =>
    (nextKernel G σ n).comap (fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
      Measurable.of_discrete
  letI (n : ℕ) : IsMarkovKernel (κ n) := by dsimp [κ]; infer_instance
  exact Kernel.trajMeasure (μ.measure : Measure (History Y (A × A) 0)) κ

instance canonicalLaw_probability (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y) :
    IsProbabilityMeasure (canonicalLaw G σ μ) := by
  unfold canonicalLaw
  infer_instance

end Canonical

/-- Baseline policies embed into the unrestricted behavioral class. -/
noncomputable def markovBehavior (π : Y → Row A) : BehavioralPolicy Y A :=
  fun n h => π (last n h)

noncomputable def stateStep (G : Game Y A) (π : Y → Row A) (y : Y) : Row Y :=
  (π y).bind (fun a => (G.opponent y).bind (fun b => G.physical y a b))

noncomputable def stateLaw (G : Game Y A) (π : Y → Row A) (μ : Row Y) : ℕ → Row Y
  | 0 => μ
  | n+1 => (stateLaw G π μ n).bind (stateStep G π)

/-- Exact finite state marginal of the action-retaining law for a Markov
baseline; the equality is for every real state observable. -/
theorem state_marginal (G : Game Y A) (π : Y → Row A) (μ : Row Y) (n : ℕ)
    (f : Y → ℝ) :
    (law G (markovBehavior π) μ n).expect (fun h => f (last n h)) =
      (stateLaw G π μ n).expect f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      rw [law_step_expect]
      simpa only [markovBehavior, last, stateLaw, stateStep, Row.expect_bind]
        using ih (fun y => (stateStep G π y).expect f)

end PermanssonResearch.ActionTrace
