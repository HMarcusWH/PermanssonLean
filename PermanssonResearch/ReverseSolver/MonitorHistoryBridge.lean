import PermanssonResearch.ReverseSolver.FiniteMonitor
import PermanssonResearch.ReverseSolver.ResidenceValue

/-!
# Actual deterministic state-history laws and observation monitors

The event is a Boolean predicate of the independently reconstructed monitor on
the actual physical state prefix. The proof reuses the established D2 identity
for the genuine `partialTraj` law, with the original deadline held fixed.
-/

namespace PermanssonResearch.ReverseSolver.FiniteMonitor

open ControlledKernel HistoryDependent
open PermanssonLean.ProbabilitySupport

universe uC uS

structure ObservationMonitor (n : ℕ) (S : Type uS) where
  initial : Fin n → S
  update : ℕ → S → Fin n → S
  accept : S → Bool

variable {C : Type uC} [DecidableEq C] {n : ℕ} {S : Type uS}

def ObservationMonitor.toMonitor (M : ObservationMonitor n S) : Monitor C n S where
  initial := M.initial
  update t s _ _ z := M.update t s z
  reward _ s := if M.accept s then 1 else 0

/-- Reconstruct the summary solely from the actual observed state prefix. -/
def summary (M : ObservationMonitor n S) : (i : ℕ) → History n i → S
  | 0, h => M.initial (last h)
  | i+1, h => M.update i (summary M i (observedPrefix h i i.le_succ)) (last h)

private theorem prefix_append {i : ℕ} (h : History n i) (z : Fin n) :
    observedPrefix (appendHistory h z) i i.le_succ = h := by
  funext j
  simp [observedPrefix, appendHistory, Finset.mem_Iic.mp j.property]

@[simp] theorem summary_append (M : ObservationMonitor n S) {i : ℕ}
    (h : History n i) (z : Fin n) :
    summary M (i+1) (appendHistory h z) = M.update i (summary M i h) z := by
  simp only [summary, prefix_append, appendHistory_last]

@[simp] theorem summary_singleton (M : ObservationMonitor n S) (x : Fin n) :
    summary M 0 (singletonPrefix x) = M.initial x := rfl

def monitorAccept (M : ObservationMonitor n S) (h : PackedHistory n) : Bool :=
  M.accept (summary M h.1 h.2)

/-- The actual monitor event in the original state-history sample space. -/
def monitorEvent (M : ObservationMonitor n S) (N : ℕ) : Set (History n N) :=
  {h | M.accept (summary M N h) = true}

def historyContinuation (sys : FiniteControlSystem C n) (M : ObservationMonitor n S)
    (σ : HistoryPolicy sys) (D : ℕ) :
    (r i : ℕ) → History n i → S → ℚ
  | 0, _, _, s => if M.accept s then 1 else 0
  | r+1, i, h, s => ∑ z : Fin n, selectedEntry sys σ D i h z *
      historyContinuation sys M σ D r (i+1) (appendHistory h z) (M.update i s z)

theorem historyContinuation_eq_objectiveValue
    (sys : FiniteControlSystem C n) (M : ObservationMonitor n S)
    (σ : HistoryPolicy sys) (D r i : ℕ) (h : History n i) :
    historyContinuation sys M σ D r i h (summary M i h) =
      Residence.objectiveValue sys σ (monitorAccept M) D r i h := by
  induction r generalizing i with
  | zero => rfl
  | succ r ih =>
      simp only [historyContinuation, Residence.objectiveValue]
      apply Finset.sum_congr rfl
      intro z _
      rw [← summary_append, ih]

/-- The genuine state-prefix probability equals the independent monitor
continuation, including physical movement after monitor success or failure. -/
theorem monitor_probability_eq_history_probability
    (sys : FiniteControlSystem C n) (M : ObservationMonitor n S)
    (σ : HistoryPolicy sys) (N : ℕ) (x : Fin n) :
    prefixLaw sys σ N x N (monitorEvent M N) = ENNReal.ofReal
      ((historyContinuation sys M σ N N 0 (singletonPrefix x) (M.initial x) : ℚ) : ℝ) := by
  have he := historyContinuation_eq_objectiveValue sys M σ N N 0 (singletonPrefix x)
  rw [summary_singleton] at he
  rw [he]
  exact Residence.objectiveProbability_eq_value sys σ (monitorAccept M) N x

/-- All deterministic state-history policies obey the compact monitor bound. -/
theorem historyContinuation_le_monitor_value
    (sys : FiniteControlSystem C n) (M : ObservationMonitor n S)
    (σ : HistoryPolicy sys) (D r i : ℕ) (h : History n i) (s : S) :
    historyContinuation sys M σ D r i h s ≤ value sys M.toMonitor r i (last h) s := by
  induction r generalizing i s with
  | zero => exact le_rfl
  | succ r ih =>
      change (∑ z : Fin n, selectedEntry sys σ D i h z *
        historyContinuation sys M σ D r (i+1) (appendHistory h z) (M.update i s z)) ≤ _
      calc
        _ ≤ ∑ z : Fin n, selectedEntry sys σ D i h z *
            value sys M.toMonitor r (i+1) z (M.update i s z) := by
          apply Finset.sum_le_sum
          intro z _
          apply mul_le_mul_of_nonneg_left _ (selectedEntry_nonneg sys σ D i h z)
          simpa only [appendHistory_last] using ih (i+1) (appendHistory h z) (M.update i s z)
        _ ≤ value sys M.toMonitor (r+1) i (last h) s :=
          maximizingControl_dominates sys M.toMonitor _ i (last h) s
            (σ.choose D i h) (σ.permitted D i h)

/-- The compact controller is implemented by reconstructing its summary from
the available state prefix. It receives no additional observation. -/
noncomputable def monitorHistoryMaximizer (sys : FiniteControlSystem C n)
    (M : ObservationMonitor n S) : HistoryPolicy sys where
  choose D i h := (deterministicMaximizer sys M.toMonitor D).choose i (last h) (summary M i h)
  permitted D i h := (deterministicMaximizer sys M.toMonitor D).permitted i (last h) _

theorem historyMaximizer_attains (sys : FiniteControlSystem C n)
    (M : ObservationMonitor n S) (D r i : ℕ) (h : History n i) (hr : i+r=D) :
    historyContinuation sys M (monitorHistoryMaximizer sys M) D r i h (summary M i h) =
      value sys M.toMonitor r i (last h) (summary M i h) := by
  induction r generalizing i with
  | zero => rfl
  | succ r ih =>
      have hs : D-(i+1)=r := by omega
      have hc : (monitorHistoryMaximizer sys M).choose D i h =
          maximizingControl sys M.toMonitor (value sys M.toMonitor r (i+1))
            i (last h) (summary M i h) := by
        simp only [monitorHistoryMaximizer, deterministicMaximizer, hs]
      change (∑ z : Fin n,
        selectedEntry sys (monitorHistoryMaximizer sys M) D i h z *
          historyContinuation sys M (monitorHistoryMaximizer sys M) D r (i+1)
            (appendHistory h z) (M.update i (summary M i h) z)) = _
      change _ = ∑ z : Fin n, _
      apply Finset.sum_congr rfl
      intro z _
      rw [← summary_append, ih (i+1) (appendHistory h z) (by omega)]
      simp only [selectedEntry, hc, summary_append, ObservationMonitor.toMonitor, appendHistory_last]

/-- Actual `partialTraj` monitor-event optimality and attainment for the original
deterministic state-history interface, proved with the compact value. -/
theorem monitor_history_probability_optimal_and_attained
    (sys : FiniteControlSystem C n) (M : ObservationMonitor n S) (N : ℕ) (x : Fin n) :
    (∀ σ : HistoryPolicy sys, prefixLaw sys σ N x N (monitorEvent M N) ≤
      ENNReal.ofReal ((value sys M.toMonitor N 0 x (M.initial x) : ℚ) : ℝ)) ∧
    prefixLaw sys (monitorHistoryMaximizer sys M) N x N (monitorEvent M N) =
      ENNReal.ofReal ((value sys M.toMonitor N 0 x (M.initial x) : ℚ) : ℝ) := by
  constructor
  · intro σ
    rw [monitor_probability_eq_history_probability]
    apply ENNReal.ofReal_le_ofReal
    exact_mod_cast historyContinuation_le_monitor_value sys M σ N N 0
      (singletonPrefix x) (M.initial x)
  · rw [monitor_probability_eq_history_probability]
    have hv := historyMaximizer_attains sys M N N 0 (singletonPrefix x) (by omega)
    simp only [summary_singleton] at hv
    rw [hv]
    rfl

end PermanssonResearch.ReverseSolver.FiniteMonitor
