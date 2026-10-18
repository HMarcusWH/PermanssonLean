import PermanssonResearch.Probability.FirstMomentKantorovichDuality
import PermanssonResearch.Probability.KRDualSeparation
import Mathlib.Topology.MetricSpace.Cauchy

/-! The genuine transport metric on first-moment probability measures.
Its distance is the infimum of costs of actual integrable couplings. -/

open MeasureTheory TopologicalSpace
namespace PermanssonResearch.Probability
set_option autoImplicit false

variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

structure FirstMomentProbability (y₀ : Y) where
  probability : ProbabilityMeasure Y
  firstMoment : Integrable (fun y => dist y y₀) probability.toMeasure

namespace FirstMomentProbability
variable {y₀ : Y}

def measure (μ : FirstMomentProbability y₀) : Measure Y := μ.probability.toMeasure

instance measure_probability (μ : FirstMomentProbability y₀) :
    IsProbabilityMeasure μ.measure := μ.probability.prop

@[ext] theorem ext {μ ν : FirstMomentProbability y₀} (h : μ.measure = ν.measure) : μ = ν := by
  cases μ with
  | mk p hp =>
    cases ν with
    | mk q hq =>
      have he : p = q := ProbabilityMeasure.toMeasure_injective h
      cases he
      rfl

variable [SeparableSpace Y]

noncomputable def distance (μ ν : FirstMomentProbability y₀) : ℝ :=
  couplingW1 μ.measure ν.measure

theorem dual_distance (μ ν : FirstMomentProbability y₀) :
    W1DualLE μ.measure ν.measure (distance μ ν) :=
  firstMoment_w1DualLE_couplingW1 μ.measure ν.measure y₀ μ.firstMoment ν.firstMoment

theorem distance_le {μ ν : FirstMomentProbability y₀} {b : ℝ}
    (h : W1DualLE μ.measure ν.measure b) : distance μ ν ≤ b :=
  firstMoment_couplingW1_le_of_w1DualLE μ.measure ν.measure y₀ μ.firstMoment ν.firstMoment h

theorem distance_nonneg (μ ν : FirstMomentProbability y₀) : 0 ≤ distance μ ν :=
  (dual_distance μ ν).nonneg

theorem distance_self (μ : FirstMomentProbability y₀) : distance μ μ = 0 :=
  le_antisymm (distance_le (W1DualLE.refl _)) (distance_nonneg _ _)

theorem distance_comm (μ ν : FirstMomentProbability y₀) : distance μ ν = distance ν μ :=
  le_antisymm (distance_le (dual_distance ν μ).symm)
    (distance_le (dual_distance μ ν).symm)

theorem distance_triangle (μ ν ρ : FirstMomentProbability y₀) :
    distance μ ρ ≤ distance μ ν + distance ν ρ :=
  distance_le ((dual_distance μ ν).trans (dual_distance ν ρ))

theorem eq_of_distance_eq_zero {μ ν : FirstMomentProbability y₀}
    (h : distance μ ν = 0) : μ = ν := by
  apply ext
  apply measure_eq_of_w1DualLE_zero
  simpa [h] using dual_distance μ ν

noncomputable instance metricSpace : MetricSpace (FirstMomentProbability y₀) where
  dist := distance
  dist_self := distance_self
  dist_comm := distance_comm
  dist_triangle := distance_triangle
  eq_of_dist_eq_zero := eq_of_distance_eq_zero

theorem dist_eq_couplingW1 (μ ν : FirstMomentProbability y₀) :
    dist μ ν = couplingW1 μ.measure ν.measure := rfl

theorem w1DualLE_iff_dist_le (μ ν : FirstMomentProbability y₀) (b : ℝ) :
    W1DualLE μ.measure ν.measure b ↔ dist μ ν ≤ b :=
  ⟨distance_le,fun h => (dual_distance μ ν).mono h⟩

end FirstMomentProbability
end PermanssonResearch.Probability
