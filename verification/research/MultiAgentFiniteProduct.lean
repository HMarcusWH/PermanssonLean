import PermanssonResearch.MultiAgent.FiniteProductTwo

open MeasureTheory ProbabilityTheory Set PermanssonLean
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultiAgent.FiniteProductTests
open FiniteProduct

abbrev Private : Fin 3 → Type := fun _ => Unit
abbrev Action : Fin 3 → Type := fun _ => Bool
abbrev Y := JointState (StrategicState Unit Private) Bool

noncomputable def component (i : Fin 3) (b : Bool) : Mechanism Unit Private Bool Action i where
  action := Kernel.const _ (Measure.dirac b)
  update := Kernel.const _ (Measure.dirac ())
  action_isMarkov := inferInstance
  update_isMarkov := inferInstance

noncomputable def baseline : Generator Unit Private Bool Action where
  component := fun i => component i false
  common := Kernel.const _ (Measure.dirac ())
  common_isMarkov := inferInstance

noncomputable def opponents : ∀ i, Mechanism Unit Private Bool Action i :=
  fun i => component i (decide (i = 0))

def clActions : Fin 3 → Bool := fun i => decide (i = 1)
def olActions : Fin 3 → Bool := fun i => decide (i = 0 ∨ i = 1)
def start : Y := (((),fun _ => ()),false)

/-- Asymmetric three-player physics: players zero and one must both act,
while player two's action vetoes the outcome. -/
noncomputable def physical : Kernel (WorldInput (StrategicState Unit Private) Bool (Fin 3 → Bool)) Bool :=
  Kernel.deterministic (fun v => v.2 0 && v.2 1 && !(v.2 2)) (by fun_prop)

/-- Selected-player CL installs only coordinate one; OL additionally installs
the asymmetric opponent profile. These are actual product-kernel atom checks. -/
example :
    (baseline.closedLoop 1 (component 1 true)).toGenerator.action start {clActions} = 1 ∧
    (baseline.openLoop 1 (component 1 true) opponents).toGenerator.action start {olActions} = 1 := by
  constructor
  · rw [Generator.action_atom]
    simp [Fin.prod_univ_three,baseline,Generator.closedLoop,component,
      Kernel.const_apply,Measure.dirac_apply,clActions]
  · rw [Generator.action_atom]
    simp [Fin.prod_univ_three,baseline,Generator.openLoop,opponents,component,
      Kernel.const_apply,Measure.dirac_apply,olActions]

/-- The same literal world object distinguishes the declared protocol actions;
it is neither symmetrized nor replaced inside this comparison. -/
example : physical (start,clActions) {true} = 0 ∧ physical (start,olActions) {true} = 1 := by
  simp [physical,Kernel.deterministic_apply,Measure.dirac_apply,clActions,olActions]

example : ¬ Nonempty (Fin 0) := FiniteProduct.no_treated_empty

end PermanssonResearch.MultiAgent.FiniteProductTests
