import PermanssonResearch.MultipleLimit.FiniteOccupationVector
import PermanssonResearch.MultipleLimit.CanonicalRecurrentResidence
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Tactic

/-!
# Lane C2 — eventual recurrent residence forces empirical mass outside to vanish

This is the deterministic support half of the all-chain occupation proof.
It does not assume ergodicity, a limiting empirical distribution, stationarity
of the initial law, or independence of transition blocks.

The actual finite-horizon empirical occupation uses times 0 through T-1,
as required by the frozen Permansson regime specification.
-/

open Filter
open scoped Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteOccupationOutside

open FiniteOccupationVector
open FiniteOccupationTelescoping
open CanonicalRecurrentResidence

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- If a path eventually stays in C, its observed fraction at every state
outside C converges to zero. This is a Cesàro consequence of eventual
absence, not an assumption of a stationary distribution. -/
theorem empiricalVector_tendsto_zero_of_eventuallyInClass
    (w : ℕ → Y) (C : Set Y)
    (hC : EventuallyInClass w C)
    (z : Y) (hz : z ∉ C) :
    Tendsto (fun n => empiricalVector w n z) atTop (𝓝 0) := by
  obtain ⟨t, ht⟩ := hC
  have hzero : (fun n : ℕ => indicatorAt w z n) =ᶠ[atTop]
      (fun _ : ℕ => (0 : ℝ)) := by
    filter_upwards [Ici_mem_atTop t] with n hn
    have hnz : w n ≠ z := by
      intro heq
      apply hz
      simpa only [heq] using ht n hn
    simp [indicatorAt, hnz]
  have htends : Tendsto (fun n : ℕ => indicatorAt w z n)
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.congr' hzero.symm
  have hcesaro := htends.cesaro
  have hshift := hcesaro.comp (tendsto_add_atTop_nat 1)
  simpa only [empiricalVector] using hshift

end FiniteOccupationOutside
end MultipleLimit
end PermanssonResearch
