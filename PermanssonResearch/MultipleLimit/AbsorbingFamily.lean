import PermanssonLean.Regime.GeneratedRegime
import Mathlib.Tactic

/-!
# Lane C1 — finite absorbing-family semantic boundary

This new research-only object holds a genuine finite Markov kernel and a
nonempty set of pointwise absorbing states. It does not mutate the frozen
single-target RegimeSpecification or claim that absorption follows
from the mere existence of an absorbing set.
-/

open MeasureTheory ProbabilityTheory Filter

namespace PermanssonResearch
namespace MultipleLimit

/-- A finite-state stochastic kernel with nonempty pointwise absorbing
states; intermediate states may be transient. -/
structure AbsorbingFamily (Y : Type*) [MeasurableSpace Y] [Fintype Y] where
  kernel : Kernel Y Y
  isMarkov : IsMarkovKernel kernel
  absorbing : Finset Y
  absorbing_nonempty : absorbing.Nonempty
  absorbing_fixed :
    ∀ a : Y, a ∈ absorbing → kernel a = Measure.dirac a

/-- A path eventually stays at one fixed state, with no constraint on
its finite prefix. -/
def EventuallyAt {Y : Type*} (w : ℕ → Y) (a : Y) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → w n = a

/-- The absorbing-state outcome is unique on every eventually constant
trajectory. It is therefore meaningful to speak of the random destination
rather than an arbitrary selected witness. -/
theorem eventuallyAt_unique {Y : Type*}
    {w : ℕ → Y} {a b : Y}
    (ha : EventuallyAt w a) (hb : EventuallyAt w b) : a = b := by
  rcases ha with ⟨Na, ha⟩
  rcases hb with ⟨Nb, hb⟩
  exact (ha (max Na Nb) (le_max_left _ _)).symm.trans
    (hb (max Na Nb) (le_max_right _ _))

/-- Literal good-path event: the trajectory eventually remains at exactly
one of the predeclared absorbing destinations. -/
def AbsorptionPaths {Y : Type*} [MeasurableSpace Y] [Fintype Y]
    (F : AbsorbingFamily Y) : Set (ℕ → Y) :=
  {w | ∃ a ∈ F.absorbing, EventuallyAt w a}

/-- What a separate stochastic-hitting theorem must establish for an
initial path law; not automatically inferred from an absorbing set. -/
def HasAlmostSureAbsorption {Y : Type*} [MeasurableSpace Y] [Fintype Y]
    (F : AbsorbingFamily Y) (μ : Measure (ℕ → Y)) : Prop :=
  ∀ᵐ w ∂μ, w ∈ AbsorptionPaths F

end MultipleLimit
end PermanssonResearch
