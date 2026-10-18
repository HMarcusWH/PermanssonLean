import PermanssonResearch.Games.DiscountedTraceExpectation
import PermanssonLean.StrategicWorld.WellPosedness
import PermanssonLean.Regime.Specification
import Mathlib.Tactic

/-!
# A new three-world economic witness

This is the separately selected XPLUS construction of the 2026-10-18 build
specification. It does not edit or reinterpret the historical X1 model.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch.EconomicWitness

open PermanssonLean ActionTrace
set_option autoImplicit false

abbrev World := Fin 3
abbrev Action := Bool × Bool
abbrev Player := Fin 2
abbrev Y := JointState Unit World

noncomputable def fairRow : Row World where
  mass z := if z = 2 then 0 else 1/2
  nonneg z := by split_ifs <;> norm_num
  total := by norm_num [Fin.sum_univ_three]

/-- A functioning world is followed by a fair resource condition exactly when
both players restrain; collapse is absorbing under every action. -/
noncomputable def worldRow (x : World) (a : Action) : Row World :=
  if x = 2 ∨ a ≠ (false,false) then Row.pure 2 else fairRow

noncomputable def world : Kernel (WorldInput Unit World Action) World where
  toFun z := (worldRow z.1.2 z.2).measure
  measurable' := Measurable.of_discrete

instance world_markov : IsMarkovKernel world := by
  refine ⟨fun z => ?_⟩
  change IsProbabilityMeasure (worldRow z.1.2 z.2).measure
  infer_instance

noncomputable def baselineAction : Kernel Y Action :=
  Kernel.deterministic (fun _ => (false,false)) Measurable.of_discrete

noncomputable def unitUpdate : Kernel (UpdateInput Unit World Action) Unit :=
  Kernel.deterministic (fun _ => ()) Measurable.of_discrete

noncomputable def model : StrategicWorldModel Unit World Action where
  generator := {
    action := baselineAction
    update := unitUpdate
    action_isMarkov := by unfold baselineAction; infer_instance
    update_isMarkov := by unfold unitUpdate; infer_instance }
  world := world
  world_isMarkov := inferInstance

def assemble (i : Player) (own other : Bool) : Action :=
  if i = 0 then (own,other) else (other,own)

def ownAction (i : Player) (a : Action) : Bool := if i = 0 then a.1 else a.2

def reward (i : Player) (x : World) (a : Action) : ℝ :=
  if x = 2 then 0 else 1 + if ownAction i a then 1 else 0

def value (_i : Player) (y : Y) : ℝ := if y.2 = 2 then 0 else 4

noncomputable def strategyGame (i : Player) : Game Y Bool where
  player := i
  physical y a b := (worldRow y.2 (assemble i a b)).map (fun x => ((),x))
  opponent _ := Row.pure false
  reward y a b := reward i y.2 (assemble i a b)
  discount := 3/4
  discount_nonneg := by norm_num
  discount_lt_one := by norm_num

noncomputable def baselineBehavior : BehavioralPolicy Y Bool := fun _ _ => Row.pure false

def region : Set Y := {y | y.2 ≠ 2}

noncomputable def target : ProbabilityMeasure World := ⟨fairRow.measure, inferInstance⟩

noncomputable def specification : RegimeSpecification Y World where
  region := region
  region_measurable := MeasurableSet.of_discrete
  basin := region
  basin_measurable := MeasurableSet.of_discrete
  basin_subset_region := Set.Subset.rfl
  descriptor := Prod.snd
  descriptor_measurable := measurable_snd
  target := target
  convergenceMode := ConvergenceMode.almostSureWeak Y World

/-- Exact intended physical law, tested at all three world states. -/
theorem world_restraint (x : World) (hx : x ≠ 2) :
    world (((),x),(false,false)) = fairRow.measure := by
  simp [world, worldRow, hx]

theorem world_collapse (a : Action) : world (((),2),a) = Measure.dirac 2 := by
  norm_num [world, worldRow, Row.measure, Row.pure, Fin.sum_univ_three]

theorem actual_physical_expect (i : Player) (y : Y) (a b : Bool) (f : Y → ℝ) :
    ((strategyGame i).physical y a b).expect f =
      ∫ x, ∫ q, f (q,x) ∂unitUpdate ((y,assemble i a b),x)
        ∂world (y,assemble i a b) := by
  simp only [strategyGame, Row.expect_map]
  rw [Row.expect_eq_integral]
  change (∫ x, f ((),x) ∂(worldRow y.2 (assemble i a b)).measure) = _
  apply integral_congr_ae
  apply ae_of_all
  intro x
  simp [unitUpdate, Kernel.deterministic_apply]

end PermanssonResearch.EconomicWitness
