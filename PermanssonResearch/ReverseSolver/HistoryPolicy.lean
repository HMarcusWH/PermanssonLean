import PermanssonResearch.ReverseSolver.NonstationaryPrefixKernel
import Mathlib.Tactic

/-!
# D1-D1: admissible deterministic policies on complete observed histories

The controller is handed exactly the observed states y₀,...,yᵢ, together with
the original deadline D and elapsed step i. It never observes the future.
Only the currently occupied state's admissible menu is used. This is a
rational finite-state research policy, not a single frozen intervention.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace HistoryDependent

open ControlledKernel
open Bellman

universe uC

/-- A state history with exactly i elapsed transitions (including time zero). -/
abbrev History (n i : ℕ) := (j : Finset.Iic i) → Fin n

/-- The last observed state at elapsed step i. -/
def last {n i : ℕ} (h : History n i) : Fin n :=
  h ⟨i, Finset.mem_Iic.mpr le_rfl⟩

/-- A deterministic controller seeing only the observed prefix; admissibility
is certified at its last observed state, for every deadline and prefix. -/
structure HistoryPolicy {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) where
  choose : (D i : ℕ) → History n i → C
  permitted : ∀ (D i : ℕ) (h : History n i),
    choose D i h ∈ sys.options (last h)

/-- Every remaining-horizon Markov schedule is a history controller which
ignores all the earlier states. Retain the ORIGINAL deadline throughout. -/
def embedMarkov {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys) :
    HistoryPolicy sys where
  choose := fun D i h => (π (D-i)).choose (last h)
  permitted := fun D i h => (π (D-i)).permitted (last h)

@[simp] theorem embedMarkov_choose
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (D i : ℕ) (h : History n i) :
    (embedMarkov sys π).choose D i h = (π (D-i)).choose (last h) := rfl

/-- An admissible action is available at every supplied history, including
zero-probability prefixes; no conditional-probability division is required. -/
theorem chosen_mem
    {C : Type uC} [DecidableEq C] {n : ℕ}
    {sys : FiniteControlSystem C n} (σ : HistoryPolicy sys)
    (D i : ℕ) (h : History n i) :
    σ.choose D i h ∈ sys.options (last h) :=
  σ.permitted D i h

end HistoryDependent
end ReverseSolver
end PermanssonResearch
