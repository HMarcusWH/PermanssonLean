import PermanssonResearch.ReverseSolver.ChronologicalMonitorMeasure
import PermanssonResearch.ReverseSolver.SolverBoundaryWitnesses
import Mathlib.Tactic

/-!
# D-05 — fixed-model versus independently reselected-row two-stage laws

A model `θ` chosen once supplies both chronological Bernoulli success rows.
Under a rectangular adversary the model may be reselected after stage zero.
We construct the actual normalized *two-observation probability law*, instead
of treating the scalar 9/100 versus 1/100 as a path-law identity by fiat.

The recorded `Bool × Bool` path contains success at the first and second
stages. Both draws are conditionally product-distributed for their specified
rows; the claimed separation is for this explicit finite construction only.
-/

namespace PermanssonResearch.ReverseSolver.CommittedVsRectangular

open PermanssonResearch.ReverseSolver.FiniteMonitor

/-- If `θ` matches the time flag, survival is 1/10; otherwise 9/10. -/
def stageSuccess (θ second : Bool) : ℚ :=
  if θ = second then 1 / 10 else 9 / 10

/-- The literal chronological two-stage joint atom, with a model selection
at each time. A committed model corresponds to `θ₀ = θ₁`. -/
def pathAtom (θ₀ θ₁ : Bool) (path : Bool × Bool) : ℚ :=
  (if path.1 then stageSuccess θ₀ false else 1 - stageSuccess θ₀ false) *
  (if path.2 then stageSuccess θ₁ true else 1 - stageSuccess θ₁ true)

/-- A finite probability measure on *entire two-stage paths*, not solely on
the terminal output. The support is complete and every atom is checked. -/
noncomputable def pathLaw (θ₀ θ₁ : Bool) : FiniteProbabilityLaw (Bool × Bool) where
  support := Finset.univ
  atom path := (pathAtom θ₀ θ₁ path : ℝ)
  nonnegative path := by
    rcases path with ⟨a, b⟩
    cases θ₀ <;> cases θ₁ <;> cases a <;> cases b <;>
      norm_num [pathAtom, stageSuccess]
  supported path h := False.elim (h (Finset.mem_univ path))
  normalized := by
    cases θ₀ <;> cases θ₁ <;>
      norm_num [pathAtom, stageSuccess, Fintype.sum_prod_type, Fintype.sum_bool]

/-- Observed survival of BOTH chronological stages. -/
def survivesBoth (path : Bool × Bool) : ℝ :=
  if path.1 && path.2 then 1 else 0

/-- Both possible models, if committed for the whole horizon, give 9/100
under the actual complete joint path law. -/
theorem committed_false_actual_success :
    (pathLaw false false).expectation survivesBoth = 9 / 100 := by
  norm_num [FiniteProbabilityLaw.expectation, pathLaw, pathAtom,
    stageSuccess, survivesBoth, Fintype.sum_prod_type, Fintype.sum_bool]

theorem committed_true_actual_success :
    (pathLaw true true).expectation survivesBoth = 9 / 100 := by
  norm_num [FiniteProbabilityLaw.expectation, pathLaw, pathAtom,
    stageSuccess, survivesBoth, Fintype.sum_prod_type, Fintype.sum_bool]

/-- A nature able to reselect after the first recorded stage chooses the
1/10 row on BOTH stages, yielding 1/100 on actual two-stage paths. -/
theorem rectangular_actual_success :
    (pathLaw false true).expectation survivesBoth = 1 / 100 := by
  norm_num [FiniteProbabilityLaw.expectation, pathLaw, pathAtom,
    stageSuccess, survivesBoth, Fintype.sum_prod_type, Fintype.sum_bool]

/-- Two separate temporal information structures, one actual event. -/
theorem committed_vs_rectangular_separate_on_path_laws :
    min ((pathLaw false false).expectation survivesBoth)
        ((pathLaw true true).expectation survivesBoth) = 9 / 100 ∧
    (pathLaw false true).expectation survivesBoth = 1 / 100 ∧
    (pathLaw false true).expectation survivesBoth <
      min ((pathLaw false false).expectation survivesBoth)
          ((pathLaw true true).expectation survivesBoth) := by
  rw [committed_false_actual_success, committed_true_actual_success,
    rectangular_actual_success]
  norm_num

end PermanssonResearch.ReverseSolver.CommittedVsRectangular
