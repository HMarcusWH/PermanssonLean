import PermanssonResearch.RegimeExit.ExitLawLimits
import PermanssonLean.Examples.QSDCounterexample
import PermanssonLean.Regime.QuasiStationary
import Mathlib.Tactic

/-!
# C-Exit — certified positive forever-survival on a genuine typed model

The *existing frozen-core* three-state QSD counterexample supplies genuine
alpha -> P -> U kernels with an absorbing state 0 inside B, and a different
state 1 in B that exits immediately. We REUSE that original witness rather
than pretend a separately postulated rational matrix is a path law.

Via the new research-only arbitrary-law survival limit theorem we derive a
real infinite-horizon path-law identity: starting at 0, never exiting B
has probability one, despite the presence of a leaking state 1 in B.
No false statewise persistence consequence is drawn from a QSD.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory Topology

namespace PermanssonResearch.RegimeExit.ExitLongHorizonWitness

open PermanssonLean PermanssonLean.RegimeSpecification
open PermanssonLean.QSDCounterexample
open PermanssonResearch.RegimeExit

theorem actual_typed_thetaOne_QSD_and_leaking_other_state :
    IsQuasiStationaryDistribution model spec qsdLaw 1 ∧
      ¬ IsFinitePersistent model spec 1 0 :=
  qsd_does_not_imply_uniform_finitePersistence

/-- All finite law-initialized survival masses equal one, by the actual
killed-kernel eigenmeasure theorem with theta=1. -/
theorem actual_typed_qsd_finite_survival_one (n : ℕ) :
    survivalProbabilityFromLaw model spec qsdLaw n = 1 := by
  simpa using
    (qsd_survivalProbability model spec qsdLaw 1 qsd_exists n)

/-- New long-run theorem: the actual infinite path law, not a numeric table. -/
theorem actual_typed_never_exit_from_qsd_law :
    survivalForeverProbabilityFromLaw model spec qsdLaw = 1 := by
  rw [survivalForeverProbabilityFromLaw_eq_iInf_survival]
  simp [actual_typed_qsd_finite_survival_one]

/-- Point-started form of the same actual canonical infinite-horizon law. -/
theorem actual_typed_never_exit_from_absorbing_point :
    survivalForeverProbability model spec ((), (0 : X)) = 1 := by
  have h := actual_typed_never_exit_from_qsd_law
  simpa [survivalForeverProbabilityFromLaw,
    survivalForeverProbability, qsdLaw_toMeasure] using h

end PermanssonResearch.RegimeExit.ExitLongHorizonWitness
