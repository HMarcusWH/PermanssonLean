import PermanssonResearch.Perturbation.FiniteOccupationFactorization
import PermanssonResearch.ReverseSolver.InfiniteSafetyLeakage
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# A-05: invariant occupation weights are not a general full-path property

A finite *constant-row* rational Markov model has stationary weight 99/100
on the safe physical state, yet the probability of never leaving that state
is zero. Both computations concern the same explicitly declared transition
law. Thus the original whole-path survival property cannot silently be
replaced by an arbitrary functional reading the stationary marginal.

This is a model-relative counterexample to unlicensed property factorization,
not a four-model perturbation theorem or general long-run certification.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace PermanssonResearch.ReverseSolver.InfiniteSafety.A05OccupationBoundary
open ControlledKernel FiniteMonitor

def constantMatrix : RationalMarkovMatrix 2 where
  entry _ z := if z = 0 then 99/100 else 1/100
  entry_nonneg _ z := by split_ifs <;> norm_num
  row_sum_one y := by fin_cases y <;> norm_num [Fin.sum_univ_two]

def constantSystem : FiniteControlSystem Unit 2 where
  states_nonempty := by decide
  baseline := constantMatrix
  options _ := {()}
  options_nonempty _ := Finset.singleton_nonempty ()
  matrix _ := constantMatrix

def safe : Finset (Fin 2) := {0}

def stationaryWeight (z : Fin 2) : ℚ :=
  if z = 0 then 99/100 else 1/100

theorem actual_rational_stationary_weights :
    (∑ z : Fin 2, stationaryWeight z) = 1 ∧
    ∀ z : Fin 2, (∑ y : Fin 2,
      stationaryWeight y * constantMatrix.entry y z) =
        stationaryWeight z := by
  constructor
  · norm_num [stationaryWeight, Fin.sum_univ_two]
  · intro z
    fin_cases z <;>
      norm_num [stationaryWeight, constantMatrix, Fin.sum_univ_two]

noncomputable section

theorem outside_horizon (n : ℕ) :
    horizonValue constantSystem safe n 1 = 0 := by
  cases n <;> simp [horizonValue, step, safe]

theorem inside_horizon (n : ℕ) :
    horizonValue constantSystem safe n 0 = ((99 : ℝ)/100)^n := by
  induction n with
  | zero => simp [horizonValue, safe]
  | succ n ih =>
      have hm (v : Fin 2 → ℝ) :
          maximum constantSystem v 0 = rowScore constantSystem v 0 () := by
        simp [maximum, constantSystem]
      rw [horizonValue, step,
        if_pos (show (0 : Fin 2) ∈ safe by decide),
        hm, rowScore, Fin.sum_univ_two, ih, outside_horizon]
      norm_num [constantSystem, constantMatrix, pow_succ] <;> ring

theorem actual_full_path_survival_zero :
    limitValue constantSystem safe 0 = 0 := by
  have hv := horizonValue_tendsto constantSystem safe 0
  simp_rw [inside_horizon] at hv
  have hz : Tendsto (fun k : ℕ => ((99 : ℝ)/100)^k)
      atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  exact tendsto_nhds_unique hv hz

/-- A true invariant-state mass does not equal the infinite survival event
of this very same fixed finite rational chain. -/
theorem cannot_replace_full_path_survival_by_stationary_mass :
    limitValue constantSystem safe 0 ≠
      ((stationaryWeight (0 : Fin 2) : ℚ) : ℝ) := by
  rw [actual_full_path_survival_zero]
  norm_num [stationaryWeight]

end
end PermanssonResearch.ReverseSolver.InfiniteSafety.A05OccupationBoundary
