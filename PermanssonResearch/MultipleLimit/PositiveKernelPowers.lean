import PermanssonResearch.MultipleLimit.KernelCommunication
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Lane C2 — real positive graph paths imply positive kernel powers

The generic finite graph uses positive ONE-STEP transition masses.
This bridge proves that an actual finite positive path contributes
positive mass to a real Chapman–Kolmogorov kernel power. The result
is about an arbitrary measurable Markov kernel, not a rational
surrogate. The proof uses positivity of a genuine Lebesgue integral
on a set carrying positive kernel-power mass.

No a.s. eventual hitting, stationary distribution or ergodic result
is assumed or claimed here.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace PositiveKernelPowers

open KernelCommunication

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y]
variable (K : Kernel Y Y)

/-- Every *genuine* positive-edge reachability witness yields a positive
n-step transition atom of the actual homogeneous kernel K. This holds
without any rational-matrix representation or aperiodicity assumption. -/
theorem positive_kernel_power_of_reachable {a b : Y}
    (hab : Reachable K a b) :
    ∃ n : ℕ, 0 < (K ^ n) a ({b} : Set Y) := by
  induction hab with
  | refl =>
      refine ⟨0, ?_⟩
      change 0 < (Kernel.id : Kernel Y Y) a ({a} : Set Y)
      simp [Kernel.id_apply]
  | @tail z w hprev hedge ih =>
      obtain ⟨n, hpos⟩ := ih
      refine ⟨n+1, ?_⟩
      rw [Kernel.pow_succ_apply_eq_lintegral K n a
        (measurableSet_singleton w)]
      have hmeas : Measurable (fun u : Y => K u ({w} : Set Y)) :=
        Kernel.measurable_coe K (measurableSet_singleton w)
      have hsubset : ({z} : Set Y) ⊆
          Function.support (fun u : Y => K u ({w} : Set Y)) := by
        intro u hu
        have heq : u = z := by simpa using hu
        subst u
        change K z ({w} : Set Y) ≠ 0
        exact ne_of_gt hedge
      have hpositive :
          0 < (K ^ n) a
            (Function.support (fun u : Y => K u ({w} : Set Y))) :=
        lt_of_lt_of_le hpos (measure_mono hsubset)
      exact (lintegral_pos_iff_support hmeas).mpr hpositive

/-- Combining finite maximal communication-class existence and the
real kernel-power bridge: every state has a genuine positive n-step
transition probability into some closed communicating class. -/
theorem positive_power_to_closed_class (a : Y) :
    ∃ c : Y, ClosedSubset K (CommunicatingClass K c) ∧
      ∃ n : ℕ, 0 < (K ^ n) a ({c} : Set Y) := by
  obtain ⟨c, hac, hc⟩ := exists_reachable_closed_class K a
  exact ⟨c, hc, positive_kernel_power_of_reachable K hac⟩

end PositiveKernelPowers
end MultipleLimit
end PermanssonResearch
