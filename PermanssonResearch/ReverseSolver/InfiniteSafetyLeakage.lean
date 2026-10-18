import PermanssonResearch.ReverseSolver.InfiniteSafetyOptimality
import Mathlib.Analysis.SpecificLimits.Basic

/-! A literal infinite-law counterexample to inference from high finite
survival. The safe state leaks with probability 1/100 on every step. -/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace PermanssonResearch.ReverseSolver.InfiniteSafety
open ControlledKernel FiniteMonitor

def leakageMatrix : RationalMarkovMatrix 2 where
  entry y z := if y=0 then (if z=0 then 99/100 else 1/100) else (if z=1 then 1 else 0)
  entry_nonneg y z := by split <;> split <;> norm_num
  row_sum_one y := by fin_cases y <;> norm_num [Fin.sum_univ_two]

def leakageSystem : FiniteControlSystem Unit 2 where
  states_nonempty := by decide
  baseline := leakageMatrix
  options _ := {()}
  options_nonempty _ := Finset.singleton_nonempty ()
  matrix _ := leakageMatrix

def leakageTarget : Finset (Fin 2) := {0}

noncomputable section

theorem leakage_horizonValue_outside (k : ℕ) : horizonValue leakageSystem leakageTarget k 1=0 := by
  cases k <;> simp [horizonValue,step,leakageTarget]

theorem leakage_horizonValue (k : ℕ) :
    horizonValue leakageSystem leakageTarget k 0=((99:ℝ)/100)^k := by
  induction k with
  | zero => simp [horizonValue,leakageTarget]
  | succ k ih =>
      have hm (v : Fin 2 → ℝ) : maximum leakageSystem v 0=rowScore leakageSystem v 0 () := by
        simp [maximum,leakageSystem]
      rw [horizonValue,step,if_pos (show (0 : Fin 2) ∈ leakageTarget by decide),hm,
        rowScore,Fin.sum_univ_two,ih,leakage_horizonValue_outside]
      norm_num [leakageSystem,leakageMatrix,pow_succ] <;> ring

/-- Every positive fixed leakage below one has geometric survival tending to
zero. This scalar fact is used here for the actual leaking system. -/
theorem fixed_leakage_tends_to_zero (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    Tendsto (fun k : ℕ => (1-ε)^k) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)

theorem leakage_limitValue : limitValue leakageSystem leakageTarget 0=0 := by
  have hv := horizonValue_tendsto leakageSystem leakageTarget 0
  simp_rw [leakage_horizonValue] at hv
  have hz : Tendsto (fun k : ℕ => ((99:ℝ)/100)^k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  exact tendsto_nhds_unique hv hz

/-- At one step survival is 99/100, while every behavioral controller has
actual infinite physical safety probability zero. -/
theorem high_finite_survival_zero_infinite :
    horizonValue leakageSystem leakageTarget 1 0=(99:ℝ)/100 ∧
    ∀ σ : BehavioralPolicy leakageSystem,
      safetyProbability leakageSystem σ leakageTarget 0=0 := by
  constructor
  · simpa using leakage_horizonValue 1
  · intro σ
    apply le_antisymm
    · simpa [leakage_limitValue] using infiniteSafety_upper leakageSystem σ leakageTarget 0
    · exact ENNReal.toReal_nonneg

theorem leakage_actual_one_step (σ : BehavioralPolicy leakageSystem) :
    pathLaw leakageSystem σ 0 (safeThrough leakageTarget 1)=
      ENNReal.ofReal ((99:ℝ)/100) := by
  rw [pathLaw_safeThrough]
  have hw (t : ℕ) (h : TraceHistory Unit 2) (y : Fin 2) : σ.weight t h y ()=1 := by
    simpa using σ.normalized t h y
  congr 1
  simp [survival,outcomeWeight,Fintype.sum_prod_type,Fin.sum_univ_two,hw,
    initialHistory,current,historySafe,append,leakageSystem,leakageMatrix,leakageTarget]

theorem high_actual_finite_survival_zero_infinite (σ : BehavioralPolicy leakageSystem) :
    pathLaw leakageSystem σ 0 (safeThrough leakageTarget 1)=ENNReal.ofReal ((99:ℝ)/100) ∧
    safetyProbability leakageSystem σ leakageTarget 0=0 :=
  ⟨leakage_actual_one_step σ,high_finite_survival_zero_infinite.2 σ⟩

end
end PermanssonResearch.ReverseSolver.InfiniteSafety
