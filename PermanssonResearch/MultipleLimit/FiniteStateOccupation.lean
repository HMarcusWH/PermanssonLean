import PermanssonLean.Regime.Occupation
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic

/-!
# Lane C2 — universal finite-state empirical occupation probability

The frozen Permansson paper uses the occupation of times 0,...,T-1
for strictly positive T. Rather than silently changing normalization
or skipping time zero, use the original proved uniform finite-horizon
probability and its pushforward by the state-at-time map.

This gives a true ProbabilityMeasure Y for every path and every
strictly positive horizon; no stochastic assumptions or matrix
approximations are needed.

The almost-sure LIMIT of this process is NOT proved by its definition.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteStateOccupation

variable {Y : Type*} [MeasurableSpace Y]

/-- The original strictly positive horizon convention, pushed to the
actual finite state coordinate rather than a chosen descriptor. -/
noncomputable def empiricalOccupation
    (w : ℕ → Y) (T : ℕ) (hT : 0 < T) : ProbabilityMeasure Y :=
  (PermanssonLean.RegimeSpecification.uniformFinProbability T hT).map
    (fun i : Fin T => w (i : ℕ))

/-- The n-th positive empirical measure sees exactly the initial
n+1 physical observations. This is an equality of definitions, not a
convergence statement. -/
theorem empiricalOccupation_succ (w : ℕ → Y) (n : ℕ) :
    empiricalOccupation w (n+1) (Nat.succ_pos n) =
      (PermanssonLean.RegimeSpecification.uniformFinProbability
        (n+1) (Nat.succ_pos n)).map
          (fun i : Fin (n+1) => w (i : ℕ)) := rfl

/-- A normalized probability measure at every individual positive
horizon, including periodic alternating paths. -/
theorem empiricalOccupation_mass_one
    (w : ℕ → Y) (T : ℕ) (hT : 0 < T) :
    (empiricalOccupation w T hT).toMeasure Set.univ = 1 := by
  exact measure_univ

end FiniteStateOccupation
end MultipleLimit
end PermanssonResearch
