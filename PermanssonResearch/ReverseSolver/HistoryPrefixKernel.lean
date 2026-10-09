import PermanssonResearch.ReverseSolver.HistoryPolicy
import PermanssonResearch.ReverseSolver.CanonicalFiniteKernel
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Tactic

/-!
# D1-D1: actual finite-prefix law under history-dependent controls

At step i, the selected rational stochastic row depends on the FULL observed
prefix and is chosen before drawing state i+1. The law is genuine Mathlib
Kernel.partialTraj, not synthetic path weights or a restarted shorter-deadline
process. G and F are NOT made absorbing in the physical transitions.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace HistoryDependent

open ControlledKernel
open Bellman
open PermanssonLean.ProbabilitySupport

universe uC

/-- The rational transition entry selected by the entire prefix. -/
def selectedEntry {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D i : ℕ) (h : History n i) (z : Fin n) : ℚ :=
  (sys.matrix (σ.choose D i h)).entry (last h) z

theorem selectedEntry_nonneg {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D i : ℕ) (h : History n i) (z : Fin n) :
    0 ≤ selectedEntry sys σ D i h z :=
  (sys.matrix (σ.choose D i h)).entry_nonneg (last h) z

theorem selectedEntry_row_sum_one {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D i : ℕ) (h : History n i) :
    (∑ z : Fin n, selectedEntry sys σ D i h z) = 1 :=
  (sys.matrix (σ.choose D i h)).row_sum_one (last h)

/-- A measurable history-to-next-state kernel: each history determines a
genuine certified rational matrix row, without deleting any past state. -/
noncomputable def historyStep {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D i : ℕ) : Kernel (History n i) (Fin n) where
  toFun := fun h => rationalFiniteKernel (sys.matrix (σ.choose D i h)) (last h)
  measurable' := Measurable.of_discrete

instance historyStep_isMarkov {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D i : ℕ) : IsMarkovKernel (historyStep sys σ D i) := by
  refine ⟨fun h => ?_⟩
  change IsProbabilityMeasure
    (rationalFiniteKernel (sys.matrix (σ.choose D i h)) (last h))
  infer_instance

theorem historyStep_singleton {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D i : ℕ) (h : History n i) (z : Fin n) :
    historyStep sys σ D i h {z} =
      ENNReal.ofReal (selectedEntry sys σ D i h z : ℝ) := by
  exact rationalFiniteKernel_singleton _ _ _

/-- Normalized law of y₀,...,y_t for the same ORIGINAL deadline D. -/
noncomputable def prefixLaw {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D : ℕ) (x : Fin n) (t : ℕ) : Measure (History n t) :=
  Kernel.partialTraj (X := fun _ : ℕ => Fin n)
    (fun i => historyStep sys σ D i) 0 t (singletonPrefix x)

instance prefixLaw_isProbability {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D : ℕ) (x : Fin n) (t : ℕ) :
    IsProbabilityMeasure (prefixLaw sys σ D x t) := by
  unfold prefixLaw
  infer_instance

@[simp] theorem prefixLaw_zero {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D : ℕ) (x : Fin n) :
    prefixLaw sys σ D x 0 = Measure.dirac (singletonPrefix x) := by
  unfold prefixLaw
  rw [Kernel.partialTraj_self, Kernel.id_apply]

/-- Prefix consistency for a FIXED initial deadline, not cross-deadline. -/
theorem prefixLaw_projective {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D : ℕ) (x : Fin n) {s t : ℕ} (hst : s ≤ t) :
    (prefixLaw sys σ D x t).map
      (Preorder.frestrictLe₂ (π := fun _ : ℕ => Fin n) hst) =
    prefixLaw sys σ D x s := by
  unfold prefixLaw
  exact Kernel.partialTraj_map_frestrictLe₂_apply
    (X := fun _ : ℕ => Fin n)
    (κ := fun i => historyStep sys σ D i)
    (x₀ := singletonPrefix x) hst

/-- Under an embedded Markov schedule, the genuine conditional kernel is
definitionally the existing D1-C1 last-state-only kernel. -/
theorem historyStep_embedMarkov {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (D i : ℕ) :
    historyStep sys (embedMarkov sys π) D i =
      Nonstationary.historyStep sys π D i := by
  rfl

/-- Equality of complete prefix probability measures under embedding. -/
theorem prefixLaw_embedMarkov {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (D : ℕ) (x : Fin n) (t : ℕ) :
    prefixLaw sys (embedMarkov sys π) D x t =
      Nonstationary.prefixLaw sys π D x t := by
  unfold prefixLaw Nonstationary.prefixLaw
  congr 1
  funext i
  exact historyStep_embedMarkov sys π D i

end HistoryDependent
end ReverseSolver
end PermanssonResearch
