import PermanssonResearch.ReverseSolver.BellmanOptimality
import PermanssonResearch.ReverseSolver.GenericFinitePrefixAtoms
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Tactic

/-!
# D1-C1: genuine fixed-deadline rational nonstationary path law

The original deadline T is immutable throughout a run. At elapsed step
i < T, the actual selected transition is the rational stochastic kernel
of the D1-B feedback rule with T-i transitions REMAINING. No clock update
is smuggled into the strategic-world primitive. We use Mathlib's authentic
Ionescu--Tulcea Kernel.partialTraj, not a synthetic path score.

The family of t-prefixes, for t <= T, is projective WITHIN THE SAME T.
There is deliberately no claim that the t-prefix of a T-run equals a new
run whose initial deadline was t.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace Nonstationary

open Bellman
open ControlledKernel
open PermanssonLean.ProbabilitySupport

universe uC

/-- Certified selected rational matrix at elapsed step i, from an ORIGINAL
deadline T. Only indices i < T occur on the path through time T. -/
def selectedMatrix {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (T i : ℕ) : RationalMarkovMatrix n :=
  feedbackMatrix sys (π (T-i))

/-- Genuine Markov transition on world states for each elapsed time. -/
noncomputable def selectedKernel {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (T i : ℕ) : Kernel (Fin n) (Fin n) :=
  rationalFiniteKernel (selectedMatrix sys π T i)

instance selectedKernel_isMarkov {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (T i : ℕ) : IsMarkovKernel (selectedKernel sys π T i) := by
  unfold selectedKernel
  infer_instance

/-- A history-dependent kernel which reads only the LAST observed state,
then applies the selected time-specific stochastic row. -/
noncomputable def historyStep {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (T i : ℕ) :
    Kernel ((j : Finset.Iic i) → Fin n) (Fin n) :=
  (selectedKernel sys π T i).comap
    (fun w => w ⟨i, Finset.mem_Iic.mpr le_rfl⟩) (by fun_prop)

instance historyStep_isMarkov {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (T i : ℕ) : IsMarkovKernel (historyStep sys π T i) := by
  unfold historyStep
  infer_instance

/-- The ACTUAL time-inhomogeneous finite-prefix distribution through t
transitions, with the ORIGINAL initial deadline T fixed. -/
noncomputable def prefixLaw {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (T : ℕ) (x : Fin n) (t : ℕ) :
    Measure ((j : Finset.Iic t) → Fin n) :=
  Kernel.partialTraj
    (X := fun _ : ℕ => Fin n)
    (fun i => historyStep sys π T i) 0 t (singletonPrefix x)

instance prefixLaw_isProbability {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (T : ℕ) (x : Fin n) (t : ℕ) :
    IsProbabilityMeasure (prefixLaw sys π T x t) := by
  unfold prefixLaw
  infer_instance

/-- Exactly the Dirac initial law, with time zero counted. -/
theorem prefixLaw_zero {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (T : ℕ) (x : Fin n) :
    prefixLaw sys π T x 0 = Measure.dirac (singletonPrefix x) := by
  unfold prefixLaw
  rw [Kernel.partialTraj_self, Kernel.id_apply]

/-- Projectivity only within a *fixed original deadline*, with no accidental
substitution of a shorter deadline or a restarted controller. -/
theorem prefixLaw_projective {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (T : ℕ) (x : Fin n) {s t : ℕ} (hst : s ≤ t) :
    (prefixLaw sys π T x t).map
      (Preorder.frestrictLe₂ (π := fun _ : ℕ => Fin n) hst) =
    prefixLaw sys π T x s := by
  unfold prefixLaw
  exact Kernel.partialTraj_map_frestrictLe₂_apply
    (X := fun _ : ℕ => Fin n)
    (κ := fun i => historyStep sys π T i)
    (x₀ := singletonPrefix x) hst

/-- At the first transition the rule uses T, not T-1, remaining steps. -/
theorem selectedMatrix_first {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (T : ℕ) :
    selectedMatrix sys π T 0 = feedbackMatrix sys (π T) := by
  simp [selectedMatrix]

/-- At elapsed step i, the next step's rule uses one fewer transition. -/
theorem selectedMatrix_next {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (T i : ℕ) (hi : i < T) :
    selectedMatrix sys π T (i+1) =
      feedbackMatrix sys (π (T-i-1)) := by
  have heq : T - (i+1) = T-i-1 := by omega
  simp only [selectedMatrix, heq]

end Nonstationary
end ReverseSolver
end PermanssonResearch
