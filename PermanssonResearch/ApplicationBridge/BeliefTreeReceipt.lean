import PermanssonResearch.ApplicationBridge.ControlTableReceipt
import PermanssonResearch.ApplicationBridge.BeliefReceipt
import PermanssonResearch.ReverseSolver.BeliefHistory
import Mathlib.Tactic

/-!
# ApplicationBridge — observe-then-act belief-tree receipts

The application's finite belief-tree profile observes the CURRENT joint state
`(s, x)` through `Q(o | x)`, then selects an action using only the observation
and action history, then applies P followed by U; the reward is paid on the
final joint state. An action must be admitted at every hidden state that still
carries mass.

Research's `ReverseSolver.Belief` chronology instead selects a control, applies
the transition and then observes. `model` embeds the application chronology
with a one-step time shift: at time `0` the transition is the identity and
the control is ignored, so the first observation is of the initial state; at
every later time the transition is the reflected fixed-action α/P/U row
(`controlledAtom`) and the observation is `Q` of the new world component. The
application's `H` transitions are Research's `H + 1` steps.

Everything checked is computed on unnormalized rational forward vectors, so no
Bayes division is trusted. `checked_observation_optimum` bounds the actual
chronological expectation of every real behavioral observation-history policy
whose actions are admitted on the hidden support, and shows that the receipt's
selected tree is such a policy and attains the checked value.
`checked_terminal_law` identifies its terminal-state law and `checked_blind`
the best observation-independent action sequence. Unrestricted POMDP
optimality, hidden-state controllers and empirical observation models are not
claimed.
-/

namespace PermanssonResearch.ApplicationBridge.BeliefTreeReceipt

open PermanssonResearch.ApplicationBridge
open PermanssonResearch.ReverseSolver
open MeasureTheory

set_option autoImplicit false

variable {ns nx na no : ℕ}

/-- Hidden joint (strategic, world) states. -/
abbrev Joint (ns nx : ℕ) := Fin ns × Fin nx

section Rational

variable (m : RationalObservationInput ns nx na no)
  (options : Fin (ns * nx) → Finset (Fin na)) (R : Joint ns nx → ℚ)

/-- Unnormalized forward vector after observing `o` at the current state. -/
def observe (f : Joint ns nx → ℚ) (o : Fin no) : Joint ns nx → ℚ :=
  fun y => f y * m.likelihood y.2 o

/-- Unnormalized forward vector after action `a` (P then U). -/
def advance (f : Joint ns nx → ℚ) (a : Fin na) : Joint ns nx → ℚ :=
  fun z => ∑ y, f y * m.worldInput.controlledAtom a y z

/-- `a` is admitted at every hidden state carrying mass. -/
def Legal (f : Joint ns nx → ℚ) (a : Fin na) : Prop :=
  ∀ y, f y ≠ 0 → a ∈ options (ControlTableReceipt.jointIndex y)

instance (f : Joint ns nx → ℚ) (a : Fin na) : Decidable (Legal options f a) := by
  unfold Legal
  infer_instance

def legalSet (f : Joint ns nx → ℚ) : Finset (Fin na) :=
  Finset.univ.filter (fun a => Legal options f a)

/-- Optimal unnormalized value of an already observed forward vector with `h`
    remaining transitions: choose an admitted action, transition, observe. -/
def value : ℕ → (Joint ns nx → ℚ) → ℚ
  | 0, g => ∑ y, g y * R y
  | h + 1, g =>
    if hne : (legalSet options g).Nonempty then
      (legalSet options g).sup' hne (fun a => ∑ o, value h (observe m (advance m g a) o))
    else 0

/-- Unnormalized value of a deterministic observation tree. -/
def treeValue : (h : ℕ) → (Joint ns nx → ℚ) → Belief.Tree (Fin na) (Fin no) h → ℚ
  | 0, g, _ => ∑ y, g y * R y
  | h + 1, g, p => ∑ o, treeValue h (observe m (advance m g p.1) o) (p.2 o)

/-- Unnormalized terminal vector of a deterministic observation tree. -/
def treeLaw : (h : ℕ) → (Joint ns nx → ℚ) → Belief.Tree (Fin na) (Fin no) h → Joint ns nx → ℚ
  | 0, g, _ => g
  | h + 1, g, p => fun z => ∑ o, treeLaw h (observe m (advance m g p.1) o) (p.2 o) z

/-- Every action of the tree is admitted on the hidden support of its node. -/
def treeLegal : (h : ℕ) → (Joint ns nx → ℚ) → Belief.Tree (Fin na) (Fin no) h → Bool
  | 0, _, _ => true
  | h + 1, g, p => decide (Legal options g p.1) &&
      decide (∀ o, treeLegal h (observe m (advance m g p.1) o) (p.2 o) = true)

/-- Unnormalized value of an observation-independent action sequence. -/
def seqValue : List (Fin na) → (Joint ns nx → ℚ) → ℚ
  | [], f => ∑ y, f y * R y
  | a :: rest, f => seqValue rest (advance m f a)

/-- Every action of the sequence is admitted on the unobserved hidden support. -/
def seqLegal : List (Fin na) → (Joint ns nx → ℚ) → Bool
  | [], _ => true
  | a :: rest, f => decide (Legal options f a) && seqLegal rest (advance m f a)

/-- Best observation-independent value over admitted actions. -/
def blindValue : ℕ → (Joint ns nx → ℚ) → ℚ
  | 0, f => ∑ y, f y * R y
  | h + 1, f =>
    if hne : (legalSet options f).Nonempty then
      (legalSet options f).sup' hne (fun a => blindValue h (advance m f a))
    else 0

/-- Optimum, selected-tree value and admissibility, and terminal law. The
    first observation is of the initial state. -/
def TreeChecks (prior : Joint ns nx → ℚ) (H : ℕ) (roots : Fin no → Belief.Tree (Fin na) (Fin no) H)
    (D : ℚ) (law : Joint ns nx → ℚ) : Prop :=
  (∑ o, value m options R H (observe m prior o)) = D ∧
  (∑ o, treeValue m R H (observe m prior o) (roots o)) = D ∧
  (∀ o, treeLegal m options H (observe m prior o) (roots o) = true) ∧
  ∀ z, (∑ o, treeLaw m H (observe m prior o) (roots o) z) = law z

instance (prior : Joint ns nx → ℚ) (H : ℕ) (roots : Fin no → Belief.Tree (Fin na) (Fin no) H)
    (D : ℚ) (law : Joint ns nx → ℚ) : Decidable (TreeChecks m options R prior H roots D law) := by
  unfold TreeChecks
  infer_instance

def checkBeliefTree (prior : Joint ns nx → ℚ) (H : ℕ)
    (roots : Fin no → Belief.Tree (Fin na) (Fin no) H) (D : ℚ) (law : Joint ns nx → ℚ) : Bool :=
  decide (TreeChecks m options R prior H roots D law)

theorem checkBeliefTree_sound (prior : Joint ns nx → ℚ) (H : ℕ)
    (roots : Fin no → Belief.Tree (Fin na) (Fin no) H) (D : ℚ) (law : Joint ns nx → ℚ)
    (h : checkBeliefTree m options R prior H roots D law = true) :
    TreeChecks m options R prior H roots D law := by
  unfold checkBeliefTree at h
  exact of_decide_eq_true h

/-- The blind sequence has length `H`, is admitted on the unobserved support,
    attains `B`, and `B` is the best observation-independent value. -/
def BlindChecks (prior : Joint ns nx → ℚ) (H : ℕ) (seq : List (Fin na)) (B : ℚ) : Prop :=
  seq.length = H ∧ seqLegal m options seq prior = true ∧
  seqValue m R seq prior = B ∧ blindValue m options R H prior = B

instance (prior : Joint ns nx → ℚ) (H : ℕ) (seq : List (Fin na)) (B : ℚ) :
    Decidable (BlindChecks m options R prior H seq B) := by
  unfold BlindChecks
  infer_instance

def checkBlind (prior : Joint ns nx → ℚ) (H : ℕ) (seq : List (Fin na)) (B : ℚ) : Bool :=
  decide (BlindChecks m options R prior H seq B)

theorem checkBlind_sound (prior : Joint ns nx → ℚ) (H : ℕ) (seq : List (Fin na)) (B : ℚ)
    (h : checkBlind m options R prior H seq B = true) :
    BlindChecks m options R prior H seq B := by
  unfold checkBlind at h
  exact of_decide_eq_true h

theorem treeValue_eq_law (h : ℕ) : ∀ (g : Joint ns nx → ℚ) (p : Belief.Tree (Fin na) (Fin no) h),
    treeValue m R h g p = ∑ z, treeLaw m h g p z * R z := by
  induction h with
  | zero => intro g p; rfl
  | succ h ih =>
    intro g p
    simp only [treeValue, treeLaw, ih, Finset.sum_mul]
    exact Finset.sum_comm

theorem observe_sum (f : Joint ns nx → ℚ) (y : Joint ns nx) :
    (∑ o, observe m f o y) = f y := by
  simp only [observe, ← Finset.mul_sum, m.likelihood_sum_one, mul_one]

theorem advance_sum (F : Fin no → Joint ns nx → ℚ) (a : Fin na) (z : Joint ns nx) :
    advance m (fun y => ∑ o, F o y) a z = ∑ o, advance m (F o) a z := by
  simp only [advance, Finset.sum_mul]
  exact Finset.sum_comm

theorem seqValue_sum (seq : List (Fin na)) :
    ∀ F : Fin no → Joint ns nx → ℚ,
      seqValue m R seq (fun y => ∑ o, F o y) = ∑ o, seqValue m R seq (F o) := by
  induction seq with
  | nil =>
    intro F
    simp only [seqValue, Finset.sum_mul]
    exact Finset.sum_comm
  | cons a rest ih =>
    intro F
    simp only [seqValue]
    rw [← ih (fun o => advance m (F o) a)]
    congr 1
    funext z
    exact advance_sum m F a z

theorem seqValue_le_blind (seq : List (Fin na)) :
    ∀ f, seqLegal m options seq f = true → seqValue m R seq f ≤ blindValue m options R seq.length f := by
  induction seq with
  | nil => intro f _; exact le_rfl
  | cons a rest ih =>
    intro f hl
    simp only [seqLegal, Bool.and_eq_true, decide_eq_true_eq] at hl
    have ha : a ∈ legalSet options f := Finset.mem_filter.mpr ⟨Finset.mem_univ a, hl.1⟩
    have hne : (legalSet options f).Nonempty := ⟨a, ha⟩
    simp only [seqValue, List.length_cons, blindValue, hne, ↓reduceDIte]
    exact (ih (advance m f a) hl.2).trans
      (Finset.le_sup' (fun b => blindValue m options R rest.length (advance m f b)) ha)

/-- Hidden support of `f` is contained in that of `g`. -/
def SupportLe (f g : Joint ns nx → ℚ) : Prop := ∀ y, f y ≠ 0 → g y ≠ 0

theorem observe_nonneg (f : Joint ns nx → ℚ) (hf : ∀ y, 0 ≤ f y) (o : Fin no) (y : Joint ns nx) :
    0 ≤ observe m f o y :=
  mul_nonneg (hf y) (m.likelihood_nonneg y.2 o)

theorem advance_nonneg (f : Joint ns nx → ℚ) (hf : ∀ y, 0 ≤ f y) (a : Fin na) (z : Joint ns nx) :
    0 ≤ advance m f a z :=
  Finset.sum_nonneg (fun y _ => mul_nonneg (hf y) (m.worldInput.controlledAtom_nonneg a y z))

theorem advance_support (f g : Joint ns nx → ℚ) (hg : ∀ y, 0 ≤ g y)
    (hfg : SupportLe f g) (a : Fin na) : SupportLe (advance m f a) (advance m g a) := by
  intro z hz
  obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hfy : f y ≠ 0 := left_ne_zero_of_mul hy
  have hc : m.worldInput.controlledAtom a y z ≠ 0 := right_ne_zero_of_mul hy
  have hpos : 0 < g y * m.worldInput.controlledAtom a y z :=
    mul_pos (lt_of_le_of_ne (hg y) (Ne.symm (hfg y hfy)))
      (lt_of_le_of_ne (m.worldInput.controlledAtom_nonneg a y z) (Ne.symm hc))
  have hle : g y * m.worldInput.controlledAtom a y z ≤ advance m g a z :=
    Finset.single_le_sum (f := fun w => g w * m.worldInput.controlledAtom a w z)
      (fun w _ => mul_nonneg (hg w) (m.worldInput.controlledAtom_nonneg a w z)) (Finset.mem_univ y)
  exact ne_of_gt (lt_of_lt_of_le hpos hle)

theorem observe_support (f : Joint ns nx → ℚ) (o : Fin no) : SupportLe (observe m f o) f :=
  fun _ hy => left_ne_zero_of_mul hy

/-- The tree that plays a fixed action sequence whatever is observed. -/
def constTree [NeZero na] : (h : ℕ) → List (Fin na) → Belief.Tree (Fin na) (Fin no) h
  | 0, _ => PUnit.unit
  | h + 1, [] => ((0 : Fin na), fun _ => constTree h [])
  | h + 1, a :: rest => (a, fun _ => constTree h rest)

theorem constTree_value [NeZero na] (seq : List (Fin na)) :
    ∀ g : Joint ns nx → ℚ,
      (∑ o, treeValue m R seq.length (observe m g o) (constTree seq.length seq)) =
        seqValue m R seq g := by
  induction seq with
  | nil =>
    intro g
    simp only [List.length_nil, treeValue, seqValue]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, observe_sum]
  | cons a rest ih =>
    intro g
    simp only [List.length_cons, treeValue, constTree, seqValue]
    have hstep : ∀ o, (∑ o', treeValue m R rest.length
        (observe m (advance m (observe m g o) a) o') (constTree rest.length rest)) =
          seqValue m R rest (advance m (observe m g o) a) := fun o => ih _
    simp only [hstep]
    rw [← seqValue_sum m R rest (fun o => advance m (observe m g o) a)]
    congr 1
    funext z
    rw [← advance_sum m (fun o => observe m g o) a z]
    simp only [observe_sum]

theorem constTree_legal [NeZero na] (seq : List (Fin na)) :
    ∀ f g : Joint ns nx → ℚ, (∀ y, 0 ≤ f y) → (∀ y, 0 ≤ g y) → SupportLe f g →
      seqLegal m options seq g = true →
      ∀ o, treeLegal m options seq.length (observe m f o) (constTree seq.length seq) = true := by
  induction seq with
  | nil => intro _ _ _ _ _ _ _; rfl
  | cons a rest ih =>
    intro f g hf hg hfg hl o
    simp only [seqLegal, Bool.and_eq_true, decide_eq_true_eq] at hl
    simp only [List.length_cons, treeLegal, constTree, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨fun y hy => hl.1 y (hfg y (observe_support m f o y hy)), fun o' => ?_⟩
    have hof : ∀ y, 0 ≤ observe m f o y := observe_nonneg m f hf o
    exact ih (advance m (observe m f o) a) (advance m g a) (advance_nonneg m _ hof a)
      (advance_nonneg m g hg a)
      (advance_support m _ g hg (fun y hy => hfg y (observe_support m f o y hy)) a) hl.2 o'

end Rational

section Real

variable (m : RationalObservationInput ns nx na no)

/-- Real row of the reflected fixed-action α/P/U kernel. -/
noncomputable def realRow (a : Fin na) (y : Joint ns nx) : Belief.Distribution (Joint ns nx) where
  weight z := (m.worldInput.controlledAtom a y z : ℝ)
  nonneg z := by exact_mod_cast m.worldInput.controlledAtom_nonneg a y z
  sum_one := by
    rw [← Rat.cast_sum, m.worldInput.controlledAtom_sum_one]
    simp

/-- Real observation row `Q(· | x)`. -/
noncomputable def realObservation (x : Fin nx) : Belief.Distribution (Fin no) where
  weight o := (m.likelihood x o : ℝ)
  nonneg o := by exact_mod_cast m.likelihood_nonneg x o
  sum_one := by
    rw [← Rat.cast_sum, m.likelihood_sum_one]
    simp

noncomputable def realPrior (prior : RationalBelief ns nx) : Belief.Distribution (Joint ns nx) where
  weight y := (prior.weight y : ℝ)
  nonneg y := by exact_mod_cast prior.nonneg y
  sum_one := by
    rw [← Rat.cast_sum, prior.sum_one]
    simp

/-- Research chronology for the application profile: identity transition at
    time `0` (the first observation is of the initial state), the reflected
    α/P/U row afterwards, and `Q` of the new world component throughout. -/
noncomputable def model (prior : RationalBelief ns nx) :
    Belief.Model (Joint ns nx) (Fin na) (Fin no) where
  transition t y a := if t = 0 then Belief.Distribution.pure y else realRow m a y
  observation _ z _ := realObservation m z.2
  default := realPrior prior

theorem model_transition_succ (prior : RationalBelief ns nx) (t : ℕ) (a : Fin na)
    (y z : Joint ns nx) :
    ((model m prior).transition (t + 1) y a).weight z = (m.worldInput.controlledAtom a y z : ℝ) := by
  simp [model, realRow]

theorem model_observation (prior : RationalBelief ns nx) (t : ℕ) (z : Joint ns nx) (a : Fin na)
    (o : Fin no) :
    ((model m prior).observation t z a).weight o = (m.likelihood z.2 o : ℝ) := rfl

variable [NeZero na] (prior : RationalBelief ns nx) (options : Fin (ns * nx) → Finset (Fin na))
  (R : Joint ns nx → ℚ)

/-- Admitted behavioral policy below an observed node with forward vector `g`. -/
def LegalB : (h : ℕ) → (Joint ns nx → ℚ) → Belief.Behavioral (Fin na) (Fin no) h → Prop
  | 0, _, _ => True
  | h + 1, g, π => ∀ a, π.1.weight a ≠ 0 →
      Legal options g a ∧ ∀ o, LegalB h (observe m (advance m g a) o) (π.2 a o)

/-- Root of the embedded chronology: the time-`0` control is ignored; every
    later action is admitted on the hidden support. -/
def RootLegal (H : ℕ) (π : Belief.Behavioral (Fin na) (Fin no) (H + 1)) : Prop :=
  ∀ c, π.1.weight c ≠ 0 → ∀ o, LegalB m options H (observe m prior.weight o) (π.2 c o)

/-- Expected terminal reward under Research's actual chronological law. -/
noncomputable def actualValue (H : ℕ) (π : Belief.Behavioral (Fin na) (Fin no) (H + 1)) : ℝ :=
  ∫ q, (R (Belief.Model.terminal (H + 1) q.1 q.2) : ℝ)
    ∂((model m prior).chronologicalLaw (H + 1) 0 (realPrior prior) π).pmf.toMeasure

/-- Unnormalized conditional expectation from a real forward vector. -/
noncomputable def expectFrom (f : Joint ns nx → ℝ) (n t : ℕ)
    (π : Belief.Behavioral (Fin na) (Fin no) n) : ℝ :=
  ∑ z, f z * (model m prior).stateValue (fun y => (R y : ℝ)) n t π z

omit [NeZero na] in
theorem expectFrom_succ (f : Joint ns nx → ℝ) (n t : ℕ)
    (π : Belief.Behavioral (Fin na) (Fin no) (n + 1)) :
    expectFrom m prior R f (n + 1) t π =
      ∑ c, π.1.weight c * ∑ o, expectFrom m prior R
        (fun z' => ((model m prior).observation t z' c).weight o *
          ∑ z, f z * ((model m prior).transition t z c).weight z') n (t + 1) (π.2 c o) := by
  simp only [expectFrom, Belief.Model.stateValue, Belief.Model.step, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Belief.Model.sum_flip_three]
  refine Finset.sum_congr rfl (fun o _ => Finset.sum_congr rfl (fun z' _ =>
    Finset.sum_congr rfl (fun z _ => by ring)))

omit [NeZero na] in
theorem num_succ (g : Joint ns nx → ℚ) (t : ℕ) (c : Fin na) (o : Fin no) :
    (fun z' => ((model m prior).observation (t + 1) z' c).weight o *
      ∑ z, (g z : ℝ) * ((model m prior).transition (t + 1) z c).weight z') =
        fun z' => ((observe m (advance m g c) o z' : ℚ) : ℝ) := by
  funext z'
  simp only [model_observation, model_transition_succ, observe, advance]
  push_cast
  ring

omit [NeZero na] in
theorem num_zero (g : Joint ns nx → ℚ) (c : Fin na) (o : Fin no) :
    (fun z' => ((model m prior).observation 0 z' c).weight o *
      ∑ z, (g z : ℝ) * ((model m prior).transition 0 z c).weight z') =
        fun z' => ((observe m g o z' : ℚ) : ℝ) := by
  classical
  funext z'
  have hrow : ∀ z, ((model m prior).transition 0 z c).weight z' = if z' = z then 1 else 0 := by
    intro z
    split_ifs with hz
    · subst hz
      simp [model, Belief.Distribution.pure]
    · simp [model, Belief.Distribution.pure, hz]
  simp only [model_observation, hrow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, observe]
  push_cast
  ring

omit [NeZero na] in
theorem pure_sum (d : Fin na) (X : Fin na → ℝ) :
    (∑ c, (Belief.Distribution.pure d).weight c * X c) = X d := by
  classical
  rw [Finset.sum_eq_single d]
  · simp [Belief.Distribution.pure]
  · intro c _ hc
    simp [Belief.Distribution.pure, hc]
  · intro h
    exact absurd (Finset.mem_univ d) h

omit [NeZero na] in
/-- Every admitted behavioral policy is bounded by the checked optimum. -/
theorem expect_le_value (h : ℕ) :
    ∀ (t : ℕ) (g : Joint ns nx → ℚ) (π : Belief.Behavioral (Fin na) (Fin no) h),
      LegalB m options h g π →
        expectFrom m prior R (fun z => (g z : ℝ)) h (t + 1) π ≤ (value m options R h g : ℝ) := by
  induction h with
  | zero =>
    intro t g π _
    simp [expectFrom, Belief.Model.stateValue, value]
  | succ h ih =>
    intro t g π hπ
    rw [expectFrom_succ]
    simp only [num_succ]
    have hterm : ∀ c, π.1.weight c * ∑ o, expectFrom m prior R
        (fun z' => ((observe m (advance m g c) o z' : ℚ) : ℝ)) h (t + 1 + 1) (π.2 c o) ≤
          π.1.weight c * (value m options R (h + 1) g : ℝ) := by
      intro c
      by_cases hc : π.1.weight c = 0
      · simp [hc]
      · obtain ⟨hlegal, hnext⟩ := hπ c hc
        apply mul_le_mul_of_nonneg_left _ (π.1.nonneg c)
        have hmem : c ∈ legalSet options g := Finset.mem_filter.mpr ⟨Finset.mem_univ c, hlegal⟩
        calc
          _ ≤ ∑ o, (value m options R h (observe m (advance m g c) o) : ℝ) :=
            Finset.sum_le_sum (fun o _ => ih (t + 1) _ (π.2 c o) (hnext o))
          _ = ((∑ o, value m options R h (observe m (advance m g c) o) : ℚ) : ℝ) := by
            push_cast; rfl
          _ ≤ (value m options R (h + 1) g : ℝ) := by
            have hne : (legalSet options g).Nonempty := ⟨c, hmem⟩
            simp only [value, hne, ↓reduceDIte]
            exact_mod_cast Finset.le_sup'
              (fun a => ∑ o, value m options R h (observe m (advance m g a) o)) hmem
    calc
      _ ≤ ∑ c, π.1.weight c * (value m options R (h + 1) g : ℝ) := Finset.sum_le_sum (fun c _ => hterm c)
      _ = _ := by rw [← Finset.sum_mul, π.1.sum_one, one_mul]

omit [NeZero na] in
/-- A deterministic tree's actual conditional expectation is its checked value. -/
theorem expect_tree (h : ℕ) :
    ∀ (t : ℕ) (g : Joint ns nx → ℚ) (p : Belief.Tree (Fin na) (Fin no) h),
      expectFrom m prior R (fun z => (g z : ℝ)) h (t + 1) (Belief.Tree.behavioral h p) =
        (treeValue m R h g p : ℝ) := by
  induction h with
  | zero =>
    intro t g p
    simp [expectFrom, Belief.Model.stateValue, treeValue]
  | succ h ih =>
    intro t g p
    rw [expectFrom_succ]
    simp only [num_succ]
    change (∑ c, (Belief.Distribution.pure p.1).weight c * ∑ o, expectFrom m prior R
      (fun z' => ((observe m (advance m g c) o z' : ℚ) : ℝ)) h (t + 1 + 1)
        (Belief.Tree.behavioral h (p.2 o))) = _
    rw [pure_sum]
    simp only [ih, treeValue]
    push_cast
    rfl

omit [NeZero na] in
theorem tree_legal (h : ℕ) :
    ∀ (g : Joint ns nx → ℚ) (p : Belief.Tree (Fin na) (Fin no) h),
      treeLegal m options h g p = true → LegalB m options h g (Belief.Tree.behavioral h p) := by
  classical
  induction h with
  | zero => intro _ _ _; trivial
  | succ h ih =>
    intro g p hp
    simp only [treeLegal, Bool.and_eq_true, decide_eq_true_eq] at hp
    intro a ha
    have hap : a = p.1 := by
      by_contra hne
      exact ha (by simp [Belief.Tree.behavioral, Belief.Distribution.pure, hne])
    subst hap
    exact ⟨hp.1, fun o => ih _ (p.2 o) (hp.2 o)⟩

/-- The research root tree: an ignored time-`0` control, then the receipt's
    tree for each first observation. -/
def rootTree (H : ℕ) (roots : Fin no → Belief.Tree (Fin na) (Fin no) H) :
    Belief.Tree (Fin na) (Fin no) (H + 1) :=
  ((0 : Fin na), roots)

/-- The selected observation-history policy as a Research behavioral policy. -/
noncomputable def selectedPolicy (H : ℕ) (roots : Fin no → Belief.Tree (Fin na) (Fin no) H) :
    Belief.Behavioral (Fin na) (Fin no) (H + 1) :=
  Belief.Tree.behavioral (H + 1) (rootTree H roots)

theorem actualValue_eq (H : ℕ) (π : Belief.Behavioral (Fin na) (Fin no) (H + 1)) :
    actualValue m prior R H π =
      ∑ c, π.1.weight c * ∑ o, expectFrom m prior R
        (fun z => ((observe m prior.weight o z : ℚ) : ℝ)) H 1 (π.2 c o) := by
  have hexp : actualValue m prior R H π =
      expectFrom m prior R (fun z => (prior.weight z : ℝ)) (H + 1) 0 π :=
    Belief.Model.chronologicalIntegral_eq_expected (model m prior) (fun y => (R y : ℝ))
      (H + 1) 0 (realPrior prior) π
  rw [hexp, expectFrom_succ]
  simp only [num_zero]

theorem actualValue_tree (H : ℕ) (roots : Fin no → Belief.Tree (Fin na) (Fin no) H) :
    actualValue m prior R H (selectedPolicy H roots) =
      ((∑ o, treeValue m R H (observe m prior.weight o) (roots o) : ℚ) : ℝ) := by
  rw [actualValue_eq]
  change (∑ c, (Belief.Distribution.pure (0 : Fin na)).weight c * ∑ o, expectFrom m prior R
    (fun z => ((observe m prior.weight o z : ℚ) : ℝ)) H (0 + 1)
      (Belief.Tree.behavioral H (roots o))) = _
  rw [pure_sum]
  simp only [expect_tree]
  push_cast
  rfl

theorem selected_root_legal (H : ℕ) (roots : Fin no → Belief.Tree (Fin na) (Fin no) H)
    (h : ∀ o, treeLegal m options H (observe m prior.weight o) (roots o) = true) :
    RootLegal m prior options H (selectedPolicy H roots) := by
  classical
  intro c hc o
  have hc0 : c = 0 := by
    by_contra hne
    exact hc (by simp [selectedPolicy, rootTree, Belief.Tree.behavioral,
      Belief.Distribution.pure, hne])
  subst hc0
  exact tree_legal m options H _ (roots o) (h o)

/-- **Observation optimum.** Every real behavioral observation-history policy
    admitted on the hidden support has actual expected terminal reward at most
    the checked value; the receipt's tree is admitted and attains it. -/
theorem checked_observation_optimum (H : ℕ) (roots : Fin no → Belief.Tree (Fin na) (Fin no) H)
    (D : ℚ) (law : Joint ns nx → ℚ)
    (h : checkBeliefTree m options R prior.weight H roots D law = true) :
    (∀ π : Belief.Behavioral (Fin na) (Fin no) (H + 1), RootLegal m prior options H π →
      actualValue m prior R H π ≤ (D : ℝ)) ∧
    RootLegal m prior options H (selectedPolicy H roots) ∧
    actualValue m prior R H (selectedPolicy H roots) = (D : ℝ) := by
  obtain ⟨hD, htree, hlegal, -⟩ := checkBeliefTree_sound m options R prior.weight H roots D law h
  refine ⟨fun π hπ => ?_, selected_root_legal m prior options H roots hlegal, ?_⟩
  · rw [actualValue_eq]
    calc
      _ ≤ ∑ c, π.1.weight c * (D : ℝ) := by
        apply Finset.sum_le_sum
        intro c _
        by_cases hc : π.1.weight c = 0
        · simp [hc]
        · apply mul_le_mul_of_nonneg_left _ (π.1.nonneg c)
          rw [← hD]
          push_cast
          exact Finset.sum_le_sum (fun o _ =>
            expect_le_value m prior options R H 0 _ (π.2 c o) (hπ c hc o))
      _ = _ := by rw [← Finset.sum_mul, π.1.sum_one, one_mul]
  · rw [actualValue_tree, htree]

/-- **Terminal law.** Under the selected policy the actual probability that the
    final joint state is `z` is the checked law entry. -/
theorem checked_terminal_law (H : ℕ) (roots : Fin no → Belief.Tree (Fin na) (Fin no) H)
    (D : ℚ) (law : Joint ns nx → ℚ)
    (h : checkBeliefTree m options R prior.weight H roots D law = true) (z : Joint ns nx) :
    (∫ q, (if Belief.Model.terminal (H + 1) q.1 q.2 = z then (1 : ℝ) else 0)
      ∂((model m prior).chronologicalLaw (H + 1) 0 (realPrior prior)
        (selectedPolicy H roots)).pmf.toMeasure) = (law z : ℝ) := by
  classical
  obtain ⟨-, -, -, hlaw⟩ := checkBeliefTree_sound m options R prior.weight H roots D law h
  have hv := actualValue_tree m prior (fun w => if w = z then 1 else 0) H roots
  simp only [treeValue_eq_law, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at hv
  rw [← hlaw z]
  convert hv using 1
  simp only [actualValue]
  congr 1
  funext q
  split_ifs <;> simp

/-- The policy that plays a fixed action sequence whatever is observed. -/
noncomputable def blindPolicy (H : ℕ) (seq : List (Fin na)) :
    Belief.Behavioral (Fin na) (Fin no) (H + 1) :=
  selectedPolicy H (fun _ => constTree H seq)

/-- **Blind baseline.** The checked blind sequence is an admitted
    observation-independent policy whose actual value is `B`; no admitted
    observation-independent sequence does better. -/
theorem checked_blind (H : ℕ) (seq : List (Fin na)) (B : ℚ)
    (h : checkBlind m options R prior.weight H seq B = true) :
    RootLegal m prior options H (blindPolicy H seq) ∧
    actualValue m prior R H (blindPolicy H seq) = (B : ℝ) ∧
    ∀ seq' : List (Fin na), seq'.length = H → seqLegal m options seq' prior.weight = true →
      actualValue m prior R H (blindPolicy H seq') ≤ (B : ℝ) := by
  obtain ⟨hlen, hlegal, hval, hbest⟩ := checkBlind_sound m options R prior.weight H seq B h
  have hvalue : ∀ seq' : List (Fin na), seq'.length = H →
      actualValue m prior R H (blindPolicy H seq') = (seqValue m R seq' prior.weight : ℝ) := by
    intro seq' hl
    subst hl
    rw [blindPolicy, actualValue_tree, constTree_value]
  refine ⟨selected_root_legal m prior options H _ ?_, by rw [hvalue seq hlen, hval], ?_⟩
  · subst hlen
    exact constTree_legal m options seq prior.weight prior.weight prior.nonneg prior.nonneg
      (fun _ hy => hy) hlegal
  · intro seq' hl hl'
    rw [hvalue seq' hl, ← hbest]
    have := seqValue_le_blind m options R seq' prior.weight hl'
    rw [hl] at this
    exact_mod_cast this

/-- Observation can only help: the checked optimum dominates the blind value. -/
theorem checked_value_of_observation (H : ℕ) (roots : Fin no → Belief.Tree (Fin na) (Fin no) H)
    (D : ℚ) (law : Joint ns nx → ℚ) (seq : List (Fin na)) (B : ℚ)
    (h : checkBeliefTree m options R prior.weight H roots D law = true)
    (hb : checkBlind m options R prior.weight H seq B = true) : B ≤ D := by
  obtain ⟨hlegal, hval, -⟩ := checked_blind m prior options R H seq B hb
  have := (checked_observation_optimum m prior options R H roots D law h).1 _ hlegal
  rw [hval] at this
  exact_mod_cast this

end Real

end PermanssonResearch.ApplicationBridge.BeliefTreeReceipt
