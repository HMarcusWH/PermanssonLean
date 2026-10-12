import PermanssonResearch.MultipleLimit.CanonicalClassContinuation
import Mathlib.Tactic

/-!
# Lane C2 — almost-sure eventual residence in one recurrent class

Builds on genuine unconditional a.s. entry into the recurrent union,
and on independently derived a.s. continuation inside ANY closed class.

Since a FINITE state space has only finitely many candidate subsets,
the countable/finitely indexed a.s. intersection permits a
simultaneous closed-class continuation statement.

Every genuine canonical trajectory eventually resides in some
closed communicating class a.s. Distinct recurrent classes cannot both
be eventual residence classes for the same path; uniqueness is pathwise
and does not depend on probabilistic assumptions.

This is still NOT a proof that the empirical occupation within the
class converges to its invariant law.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit
namespace CanonicalRecurrentResidence

open KernelCommunication
open RecurrentClassDecomposition
open CanonicalClassEntry
open CanonicalClassContinuation
open FiniteCanonicalPath

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [Nonempty Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

def EventuallyInClass (w : ℕ → Y) (C : Set Y) : Prop :=
  ∃ t : ℕ, ∀ n : ℕ, t ≤ n → w n ∈ C

/-- A single a.s. event simultaneously enforces all closed finite-class
continuation implications at every time; no independence assertion is made. -/
theorem all_closed_classes_stay_ae (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      ∀ C : Set Y, ClosedSubset K C →
        ∀ t : ℕ, w t ∈ C →
          ∀ n : ℕ, t ≤ n → w n ∈ C := by
  classical
  haveI : Countable (Set Y) := inferInstance
  apply ae_all_iff.mpr
  intro C
  by_cases hc : ClosedSubset K C
  · filter_upwards [closed_stay_after_entry_ae K μ C hc] with w hw
    intro _
    exact hw
  · exact Filter.Eventually.of_forall (fun w h => (hc h).elim)

/-- Main unconditional canonical entrance-and-residence theorem.
Every arbitrary finite homogeneous Markov chain is eventually
contained in exactly one closed recurrent communication class a.s. -/
theorem canonical_ae_eventual_recurrent_class
    (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      ∃ C ∈ RecurrentClasses K, EventuallyInClass w C := by
  filter_upwards [canonical_ae_enters_recurrent K μ,
    all_closed_classes_stay_ae K μ] with w hhit hstay
  obtain ⟨t, ht⟩ := hhit
  let C : Set Y := CommunicatingClass K (w t)
  have hC : IsRecurrentState K (w t) := ht
  refine ⟨C, (recurrentClasses_mem_iff K C).mpr
    ⟨w t, hC, rfl⟩, t, ?_⟩
  intro n hn
  exact hstay C hC t (mem_communicatingClass K (w t)) n hn

/-- Any two distinct closed recurrent classes are disjoint, so two
potential eventual terminal classes for one path must be identical. -/
theorem eventual_class_unique
    (w : ℕ → Y) {C D : Set Y}
    (hC : C ∈ RecurrentClasses K)
    (hD : D ∈ RecurrentClasses K)
    (hwC : EventuallyInClass w C)
    (hwD : EventuallyInClass w D) :
    C = D := by
  by_contra hne
  have hdisj := recurrentClasses_disjoint_of_ne K hC hD hne
  obtain ⟨t, ht⟩ := hwC
  obtain ⟨u, hu⟩ := hwD
  have hmemberC : w (max t u) ∈ C := ht _ (le_max_left _ _)
  have hmemberD : w (max t u) ∈ D := hu _ (le_max_right _ _)
  exact (Set.disjoint_left.mp hdisj) hmemberC hmemberD


/-- The final recurrent communicating class is pathwise UNIQUE on
the probability-one event of eventual class residence. The statement
is for the authentic canonical infinite path law and for every
initial probability measure. This does not identify an invariant
occupation measure or certify a regime. -/
theorem canonical_ae_unique_eventual_class
    (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      ∃! C : Set Y,
        C ∈ RecurrentClasses K ∧ EventuallyInClass w C := by
  filter_upwards [canonical_ae_eventual_recurrent_class K μ] with w hw
  obtain ⟨C, hC, hE⟩ := hw
  refine ⟨C, ⟨hC, hE⟩, ?_⟩
  intro D hD
  exact (eventual_class_unique K w hC hD.1 hE hD.2).symm

end CanonicalRecurrentResidence
end MultipleLimit
end PermanssonResearch
