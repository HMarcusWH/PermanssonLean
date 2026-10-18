import PermanssonResearch.ReverseSolver.BehavioralFinitePolicy
import PermanssonResearch.MultipleLimit.CanonicalKernelMarginals
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Tactic

/-! The genuine infinite canonical law of a real behavioral controller.
The countable Markov state stores exactly the realized physical/control past.
Every transition appends one realized control and its physical successor.
No finite-horizon objective is used to construct this probability law. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch.ReverseSolver.InfiniteSafety

open ControlledKernel FiniteMonitor
open PermanssonResearch.MultipleLimit.FiniteCanonicalPath

structure HistoryState (C : Type*) (n : ℕ) where
  initial : Fin n
  word : List (C × Fin n)
  deriving DecidableEq

def historyEquiv {C : Type*} {n : ℕ} : HistoryState C n ≃ TraceHistory C n where
  toFun h := (h.initial,h.word)
  invFun h := ⟨h.1,h.2⟩
  left_inv h := by cases h; rfl
  right_inv h := by cases h; rfl

instance {C : Type*} [Countable C] {n : ℕ} : Countable (HistoryState C n) :=
  historyEquiv.injective.countable

instance {C : Type*} {n : ℕ} : MeasurableSpace (HistoryState C n) := ⊤

instance {C : Type*} {n : ℕ} : DiscreteMeasurableSpace (HistoryState C n) := ⟨fun _ => trivial⟩

variable {C : Type*} [DecidableEq C] [Fintype C] {n : ℕ}

def initialHistory (y : Fin n) : HistoryState C n := ⟨y,[]⟩

def current (h : HistoryState C n) : Fin n := h.word.foldl (fun _ a => a.2) h.initial

def append (h : HistoryState C n) (c : C) (z : Fin n) : HistoryState C n :=
  ⟨h.initial,h.word++[(c,z)]⟩

@[simp] theorem current_initial (y : Fin n) : current (initialHistory (C := C) y)=y := rfl

@[simp] theorem current_append (h : HistoryState C n) (c : C) (z : Fin n) :
    current (append h c z)=z := by simp [current,append,List.foldl_append]

@[simp] theorem length_append (h : HistoryState C n) (c : C) (z : Fin n) :
    (append h c z).word.length=h.word.length+1 := by simp [append]

def historySafe (G : Finset (Fin n)) (h : HistoryState C n) : Prop :=
  h.initial ∈ G ∧ ∀ a ∈ h.word, a.2 ∈ G

instance (G : Finset (Fin n)) (h : HistoryState C n) : Decidable (historySafe G h) := by
  unfold historySafe
  infer_instance

@[simp] theorem historySafe_initial (G : Finset (Fin n)) (y : Fin n) :
    historySafe G (initialHistory (C := C) y) ↔ y ∈ G := by simp [historySafe,initialHistory]

@[simp] theorem historySafe_append (G : Finset (Fin n)) (h : HistoryState C n)
    (c : C) (z : Fin n) : historySafe G (append h c z) ↔ historySafe G h ∧ z ∈ G := by
  constructor
  · intro hh
    refine ⟨⟨hh.1,fun a ha => hh.2 a (List.mem_append.mpr (Or.inl ha))⟩,?_⟩
    exact hh.2 (c,z) (by simp [append])
  · rintro ⟨hh,hz⟩
    refine ⟨hh.1,?_⟩
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hh.2 a ha
    · have ha' : a=(c,z) := by simpa using ha
      simpa [ha'] using hz

private theorem fold_current_mem (G : Finset (Fin n)) (xs : List (C × Fin n))
    (y : Fin n) (hy : y ∈ G) (hx : ∀ a ∈ xs, a.2 ∈ G) :
    xs.foldl (fun _ a => a.2) y ∈ G := by
  induction xs generalizing y with
  | nil => exact hy
  | cons a xs ih => exact ih a.2 (hx a (by simp)) (fun b hb => hx b (by simp [hb]))

theorem historySafe_current (G : Finset (Fin n)) (h : HistoryState C n)
    (hh : historySafe G h) : current h ∈ G :=
  fold_current_mem G h.word h.initial hh.1 hh.2

noncomputable section

def outcomeWeight (sys : FiniteControlSystem C n) (σ : BehavioralPolicy sys)
    (h : HistoryState C n) (a : C × Fin n) : ℝ :=
  σ.weight h.word.length (historyEquiv h) (current h) a.1*
    ((sys.matrix a.1).entry (current h) a.2 : ℝ)

theorem outcomeWeight_nonnegative (sys : FiniteControlSystem C n) (σ : BehavioralPolicy sys)
    (h : HistoryState C n) (a : C × Fin n) : 0≤outcomeWeight sys σ h a :=
  mul_nonneg (σ.nonnegative _ _ _ _) (by exact_mod_cast (sys.matrix a.1).entry_nonneg (current h) a.2)

theorem outcomeWeight_total (sys : FiniteControlSystem C n) (σ : BehavioralPolicy sys)
    (h : HistoryState C n) : (∑ a : C × Fin n, outcomeWeight sys σ h a)=1 := by
  have hrow (c : C) : (∑ z : Fin n, ((sys.matrix c).entry (current h) z : ℝ))=1 := by
    exact_mod_cast (sys.matrix c).row_sum_one (current h)
  simp only [outcomeWeight,Fintype.sum_prod_type,← Finset.mul_sum,hrow,mul_one]
  exact σ.normalized _ _ _

def transitionMeasure (sys : FiniteControlSystem C n) (σ : BehavioralPolicy sys)
    (h : HistoryState C n) : Measure (HistoryState C n) :=
  ∑ a : C × Fin n, ENNReal.ofReal (outcomeWeight sys σ h a) • Measure.dirac (append h a.1 a.2)

theorem transitionMeasure_probability (sys : FiniteControlSystem C n)
    (σ : BehavioralPolicy sys) (h : HistoryState C n) :
    IsProbabilityMeasure (transitionMeasure sys σ h) := by
  refine ⟨?_⟩
  simp only [transitionMeasure,Measure.finsetSum_apply,Measure.smul_apply]
  simp only [Measure.dirac_apply' _ MeasurableSet.univ,
    Set.indicator_of_mem (Set.mem_univ _),Pi.one_apply,smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => outcomeWeight_nonnegative sys σ h a),
    outcomeWeight_total]
  simp

def historyKernel (sys : FiniteControlSystem C n) (σ : BehavioralPolicy sys) :
    Kernel (HistoryState C n) (HistoryState C n) :=
  Kernel.ofFunOfCountable (transitionMeasure sys σ)

instance historyKernel_markov (sys : FiniteControlSystem C n) (σ : BehavioralPolicy sys) :
    IsMarkovKernel (historyKernel sys σ) where
  isProbabilityMeasure h := transitionMeasure_probability sys σ h

theorem historyKernel_lintegral (sys : FiniteControlSystem C n) (σ : BehavioralPolicy sys)
    (h : HistoryState C n) (f : HistoryState C n → ℝ≥0∞) :
    (∫⁻ h', f h' ∂historyKernel sys σ h)=
      ∑ a : C × Fin n, ENNReal.ofReal (outcomeWeight sys σ h a)*f (append h a.1 a.2) := by
  change (∫⁻ h', f h' ∂transitionMeasure sys σ h)=_
  rw [transitionMeasure,lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro a _
  rw [lintegral_smul_measure,lintegral_dirac' _ (measurable_of_countable f)]
  rfl

def pathLaw (sys : FiniteControlSystem C n) (σ : BehavioralPolicy sys) (y : Fin n) :
    Measure (ℕ → HistoryState C n) :=
  canonicalPathLaw (historyKernel sys σ) (Measure.dirac (initialHistory y))

instance pathLaw_probability (sys : FiniteControlSystem C n) (σ : BehavioralPolicy sys)
    (y : Fin n) : IsProbabilityMeasure (pathLaw sys σ y) := by
  unfold pathLaw
  infer_instance

end
end PermanssonResearch.ReverseSolver.InfiniteSafety
