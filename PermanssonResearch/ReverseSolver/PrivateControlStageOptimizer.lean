import PermanssonResearch.ReverseSolver.PrivateControlStageModel

/-! Exact rational private-control stage optimization, with actual real
mixed strategies. No minimax interchange or LP duality hypothesis is used. -/

namespace PermanssonResearch.ReverseSolver.PrivateControlStage
open ExactPolytope ActionTrace Matrix
variable {C Θ : Type*} [Fintype C] [LinearOrder C] [Nonempty C]
  [Fintype Θ] [LinearOrder Θ] [Nonempty Θ]

noncomputable def lowerVector (Q : Θ → C → ℚ) : Option C → ℝ
  | none => (lowerPayoff Q : ℝ)
  | some _ => 0

noncomputable def upperVector (Q : Θ → C → ℚ) : Option C → ℝ
  | none => (upperPayoff Q : ℝ)
  | some _ => 1

def feasibleRow (Q : Θ → C → ℚ) (x : Option C → ℝ)
    (hx : x∈listFeasible (stageConstraints Q)) : Row C where
  mass c := x (some c)
  nonneg := (stageConstraints_iff Q x).mp hx |>.1
  total := (stageConstraints_iff Q x).mp hx |>.2.1

theorem feasibleRow_value_le (Q : Θ → C → ℚ) (x : Option C → ℝ)
    (hx : x∈listFeasible (stageConstraints Q)) (θ : Θ) :
    x none≤stagePayoff Q (feasibleRow Q x hx) θ :=
  (stageConstraints_iff Q x).mp hx |>.2.2.2 θ

theorem stage_box_bounds (Q : Θ → C → ℚ) :
    ∀ x∈listFeasible (stageConstraints Q), lowerVector Q≤x ∧ x≤upperVector Q := by
  intro x hx
  have hc := (stageConstraints_iff Q x).mp hx
  constructor
  · intro j
    cases j with
    | none => exact hc.2.2.1
    | some c => exact hc.1 c
  · intro j
    cases j with
    | none =>
        exact (feasibleRow_value_le Q x hx (Classical.choice inferInstance)).trans
          (stagePayoff_bounds Q (feasibleRow Q x hx) _).2
    | some c =>
        have hh := Finset.single_le_sum (fun a (_ : a∈Finset.univ) => hc.1 a)
          (Finset.mem_univ c)
        simpa only [upperVector,hc.2.1] using hh

noncomputable def strategyVector (Q : Θ → C → ℚ) (p : Row C) : Option C → ℝ
  | none => privateValue Q p
  | some c => p.mass c

theorem strategyVector_feasible (Q : Θ → C → ℚ) (p : Row C) :
    strategyVector Q p∈listFeasible (stageConstraints Q) := by
  apply (stageConstraints_iff Q _).mpr
  exact ⟨p.nonneg,p.total,(privateValue_bounds Q p).1,privateValue_le Q p⟩

def stageObjective : Option C → ℚ
  | none => 1
  | some _ => 0

/-- Executable exhaustive rational vertex constructor. The added lower
bound is a valid minimum payoff, so it does not change the strategic value. -/
def solvePrivateStage (Q : Θ → C → ℚ) : Option (Option C → ℚ) :=
  optimizeList (stageConstraints Q) stageObjective

theorem solvePrivateStage_ne_none (Q : Θ → C → ℚ) : solvePrivateStage Q≠none := by
  intro hn
  have he := (optimizeList_none_iff (stageConstraints Q) stageObjective
    (lowerVector Q) (upperVector Q) (stage_box_bounds Q)).mp hn
  have hf := strategyVector_feasible Q (Row.pure (Classical.choice inferInstance))
  rw [he] at hf
  exact hf

theorem solvePrivateStage_returns (Q : Θ → C → ℚ) :
    ∃ q,solvePrivateStage Q=some q := by
  cases h : solvePrivateStage Q with
  | none => exact (solvePrivateStage_ne_none Q h).elim
  | some q => exact ⟨q,rfl⟩

theorem returned_feasible (Q : Θ → C → ℚ) (q : Option C → ℚ)
    (hq : solvePrivateStage Q=some q) :
    (fun j => (q j : ℝ))∈listFeasible (stageConstraints Q) :=
  optimizeList_some_feasible _ _ q hq

noncomputable def solutionRow (Q : Θ → C → ℚ) (q : Option C → ℚ)
    (hq : solvePrivateStage Q=some q) : Row C :=
  feasibleRow Q (fun j => (q j : ℝ)) (returned_feasible Q q hq)

theorem returned_rational_simplex (Q : Θ → C → ℚ) (q : Option C → ℚ)
    (hq : solvePrivateStage Q=some q) :
    (∀ c,0≤q (some c)) ∧ (∑ c : C,q (some c))=1 := by
  have hh := (stageConstraints_iff Q _).mp (returned_feasible Q q hq)
  constructor
  · intro c
    exact_mod_cast hh.1 c
  · exact_mod_cast hh.2.1

theorem returned_dominates_all_real_mixtures (Q : Θ → C → ℚ) (q : Option C → ℚ)
    (hq : solvePrivateStage Q=some q) (p : Row C) : privateValue Q p≤(q none : ℝ) := by
  have ho := optimizeList_some_optimal (stageConstraints Q) stageObjective q hq
    (lowerVector Q) (upperVector Q) (stage_box_bounds Q) (strategyVector Q p)
    (strategyVector_feasible Q p)
  simpa [stageObjective,strategyVector,dotProduct,Fintype.sum_option] using ho

theorem returned_value_attained (Q : Θ → C → ℚ) (q : Option C → ℚ)
    (hq : solvePrivateStage Q=some q) : privateValue Q (solutionRow Q q hq)=(q none : ℝ) := by
  apply le_antisymm
  · exact returned_dominates_all_real_mixtures Q q hq _
  · exact feasibleRow_value_le Q _ (returned_feasible Q q hq)
      (minimizingNature Q (solutionRow Q q hq))

theorem returned_isGreatest (Q : Θ → C → ℚ) (q : Option C → ℚ)
    (hq : solvePrivateStage Q=some q) :
    IsGreatest (Set.range (privateValue Q)) (q none : ℝ) := by
  refine ⟨⟨solutionRow Q q hq,returned_value_attained Q q hq⟩,?_⟩
  rintro _ ⟨p,rfl⟩
  exact returned_dominates_all_real_mixtures Q q hq p

/-- The rational returned controller guarantees its value against every
real mixed nature law, and an actual pure nature law attains that value. -/
theorem returned_actual_strategic_value (Q : Θ → C → ℚ) (q : Option C → ℚ)
    (hq : solvePrivateStage Q=some q) :
    (∀ η : Row Θ, (q none : ℝ)≤
      (stageLaw (solutionRow Q q hq) η).expect (fun a => (Q a.1 a.2 : ℝ))) ∧
    (∃ η : Row Θ, (stageLaw (solutionRow Q q hq) η).expect
      (fun a => (Q a.1 a.2 : ℝ))=(q none : ℝ)) := by
  constructor
  · intro η
    rw [← returned_value_attained Q q hq]
    exact actual_nature_lower_bound Q _ η
  · refine ⟨Row.pure (minimizingNature Q (solutionRow Q q hq)),?_⟩
    rw [actual_minimizing_nature,returned_value_attained]

end PermanssonResearch.ReverseSolver.PrivateControlStage
