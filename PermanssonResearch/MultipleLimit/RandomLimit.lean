import PermanssonResearch.MultipleLimit.AbsorbingFamily
import PermanssonLean.Examples.PeriodicExactGR
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Tactic

/-!
# Lane C1 — canonical occupation convergence on eventually fixed paths

No new convergence mode is introduced: empiricalOccupation is literally
the frozen positive-horizon probability-measure-valued occupation process.
This module proves the pathwise weak limit whenever a path is eventually
constant, including an arbitrary finite transient prefix. It works for the
Boolean strategic-world state space used by the nontrivial test witness.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PermanssonResearch
namespace MultipleLimit

open PermanssonLean PermanssonLean.RegimeSpecification
open PermanssonLean.PeriodicExactGR

/-- A Dirac probability measure at the chosen terminal state of the
canonical finite Boolean joint-state space. -/
noncomputable def terminalLaw (a : Y) : ProbabilityMeasure Y :=
  ⟨Measure.dirac a, inferInstance⟩

/-- The frozen empirical occupation of the identity-descriptor specification
has the exact finite arithmetic average expected in the paper. -/
theorem empirical_integral_eq_average
    (w : ℕ → Y) (f : Y → ℝ) (n : ℕ) :
    (∫ z, f z ∂empiricalOccupation spec w (n+1) (Nat.succ_pos n)) =
      ((((n+1 : ℕ) : ℝ))⁻¹) *
        ∑ i ∈ Finset.range (n+1), f (w i) := by
  exact integral_empiricalOccupation_eq_average w (n+1) (Nat.succ_pos n) f

/-- Every eventually constant trajectory has the correct Cesàro integral
limit, despite arbitrarily many earlier transient visits. -/
theorem empirical_integral_eventually_at
    (w : ℕ → Y) (a : Y) (ha : EventuallyAt w a)
    (f : Y → ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ z, f z ∂empiricalOccupation spec w (n+1) (Nat.succ_pos n))
      atTop (𝓝 (f a)) := by
  rcases ha with ⟨N,hN⟩
  have heq : (fun n : ℕ => f (w n)) =ᶠ[atTop] (fun _ : ℕ => f a) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [hN n hn]
  have hpoint : Tendsto (fun n : ℕ => f (w n)) atTop (𝓝 (f a)) :=
    tendsto_const_nhds.congr' heq.symm
  have hc := hpoint.cesaro
  have hidx : Tendsto (fun n : ℕ => n+1) atTop atTop := by
    apply tendsto_atTop.2
    intro t
    filter_upwards [eventually_ge_atTop t] with n hn
    omega
  have havg := hc.comp hidx
  simpa only [empirical_integral_eq_average, Function.comp_def] using havg

/-- C1 pathwise theorem: canonical empirical occupation converges weakly to
the random destination's Dirac law on every eventually fixed path. -/
theorem occupation_eventually_at
    (w : ℕ → Y) (a : Y) (ha : EventuallyAt w a) :
    Tendsto
      (fun n : ℕ => empiricalOccupation spec w (n+1) (Nat.succ_pos n))
      atTop (𝓝 (terminalLaw a)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  change Tendsto
    (fun n : ℕ =>
      ∫ z, f z ∂empiricalOccupation spec w (n+1) (Nat.succ_pos n))
    atTop (𝓝 (∫ z, f z ∂(Measure.dirac a)))
  simp only [integral_dirac]
  exact empirical_integral_eventually_at w a ha (fun z => f z)

end MultipleLimit
end PermanssonResearch
