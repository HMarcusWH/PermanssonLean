import PermanssonResearch.X1.Parameters
import PermanssonLean.StrategicWorld.InducedKernel
import PermanssonLean.Regime.Property
import PermanssonLean.Intervention.Apply

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace PermanssonResearch.X1

set_option autoImplicit false
open PermanssonLean

abbrev WI := WorldInput Memory Bool Action
abbrev UI := UpdateInput Memory Bool Action

/-- Exact rational Boolean law, with no floating-point conversion. -/
noncomputable def coin (p : ℚ) : Measure Bool :=
  ENNReal.ofReal (p : ℝ) • Measure.dirac true +
    ENNReal.ofReal ((1 - p : ℚ) : ℝ) • Measure.dirac false

theorem coin_probability (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) : IsProbabilityMeasure (coin p) := by
  refine ⟨?_⟩
  have hp0 : 0 ≤ (p : ℝ) := by exact_mod_cast hp.1
  have hp1 : 0 ≤ ((1 - p : ℚ) : ℝ) := by exact_mod_cast sub_nonneg.mpr hp.2
  have hsum : (p : ℝ) + ((1-p : ℚ) : ℝ) = 1 := by push_cast; ring
  simp only [coin, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_of_mem (Set.mem_univ _),
    Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp0 hp1]
  rw [hsum]; norm_num

theorem coin_true (p : ℚ) : coin p {true} = ENNReal.ofReal (p : ℝ) := by
  simp [coin, Measure.dirac_apply']

theorem coin_false (p : ℚ) : coin p {false} = ENNReal.ofReal ((1-p : ℚ) : ℝ) := by
  simp [coin, Measure.dirac_apply']

theorem coin_lintegral (p : ℚ) (f : Bool → ℝ≥0∞) :
    (∫⁻ b, f b ∂coin p) = ENNReal.ofReal (p : ℝ) * f true +
      ENNReal.ofReal ((1-p : ℚ) : ℝ) * f false := by
  simp [coin, lintegral_add_measure, lintegral_smul_measure]

noncomputable def world : Kernel WI Bool where
  toFun i := coin (pRep i.1.2 i.2)
  measurable' := Measurable.of_discrete

instance world_isMarkov : IsMarkovKernel world :=
  ⟨fun i => coin_probability _ (pRep_bounds _ _)⟩

/-- The actual common P has the same probability appearing in the Bellman certificate. -/
theorem world_replete (y : Y) (a : Action) :
    world (y, a) {true} = ENNReal.ofReal (pRep y.2 a : ℝ) := coin_true _

inductive Mode | equilibrium | learner
  deriving DecidableEq

def extractionRate (m : Mode) (y : Y) : ℚ × ℚ :=
  match m with
  | .equilibrium => (piExtract y.2, piExtract y.2)
  | .learner => (learnerExtract y.1.1, learnerExtract y.1.2)

theorem extractionRate_bounds (m : Mode) (y : Y) :
    (0 ≤ (extractionRate m y).1 ∧ (extractionRate m y).1 ≤ 1) ∧
      (0 ≤ (extractionRate m y).2 ∧ (extractionRate m y).2 ≤ 1) := by
  cases m with
  | equilibrium => exact ⟨piExtract_bounds _, piExtract_bounds _⟩
  | learner => exact ⟨learnerExtract_bounds _, learnerExtract_bounds _⟩

/-- Independent per-player draws, on the same Fin3×Fin3 memory for both modes. -/
noncomputable def action (m : Mode) : Kernel Y Action where
  toFun y := (coin (extractionRate m y).1).prod (coin (extractionRate m y).2)
  measurable' := Measurable.of_discrete

instance action_isMarkov (m : Mode) : IsMarkovKernel (action m) := by
  refine ⟨fun y => ?_⟩
  haveI := coin_probability _ (extractionRate_bounds m y).1
  haveI := coin_probability _ (extractionRate_bounds m y).2
  change IsProbabilityMeasure ((coin (extractionRate m y).1).prod _)
  infer_instance

def nextMemory (m : Mode) (y : Y) (a : Action) : Memory :=
  match m with
  | .equilibrium => y.1
  | .learner => updateL y a

noncomputable def update (m : Mode) : Kernel UI Memory :=
  Kernel.deterministic (fun u => nextMemory m u.1.1 u.1.2) Measurable.of_discrete

instance update_isMarkov (m : Mode) : IsMarkovKernel (update m) := by
  unfold update; infer_instance

noncomputable def generator (m : Mode) : StrategicGenerator Memory Bool Action :=
  ⟨action m, update m, inferInstance, inferInstance⟩

noncomputable def model (m : Mode) : StrategicWorldModel Memory Bool Action :=
  ⟨generator m, world, inferInstance⟩

/-- Literal kernel identity, not equality of selected observed probabilities. -/
theorem identical_world : (model .equilibrium).world = (model .learner).world := rfl

theorem action_product (m : Mode) (y : Y) :
    (model m).generator.action y =
      (coin (extractionRate m y).1).prod (coin (extractionRate m y).2) := rfl

theorem update_dirac (m : Mode) (u : UI) :
    (model m).generator.update u = Measure.dirac (nextMemory m u.1.1 u.1.2) :=
  Kernel.deterministic_apply _ _

/-- The update is performed after P, but the specified reinforcement reads the
OLD world and recorded action. It does not accidentally substitute x'. -/
theorem update_ignores_new_world (m : Mode) (y : Y) (a : Action) (x x' : Bool) :
    update m ((y, a), x) = update m ((y, a), x') := rfl

/-- Frozen full-path property: replete at the declared horizon 3. -/
noncomputable def property : RegimePropertyMap Y ℝ :=
  fun law => (law.toMeasure {w : ℕ → Y | descriptor (w propertyHorizon) = true}).toReal

/-- Exact finite alpha→P→U matrix expression. All masses are lifted exact
rationals; this definition is not a separately postulated matrix. -/
noncomputable def transitionEntry (m : Mode) (y z : Y) : ℝ≥0∞ :=
  ∑ a : Action, ENNReal.ofReal (boolMass (extractionRate m y).1 a.1 : ℝ) *
    ENNReal.ofReal (boolMass (extractionRate m y).2 a.2 : ℝ) *
    (∑ x : Bool, ENNReal.ofReal (boolMass (pRep y.2 a) x : ℝ) *
      if (nextMemory m y a, x) = z then 1 else 0)

/-- Nonnegative product integration is performed against the actual action law. -/
theorem action_lintegral (m : Mode) (y : Y) (f : Action → ℝ≥0∞) :
    (∫⁻ a, f a ∂action m y) =
      ∑ a : Action, ENNReal.ofReal (boolMass (extractionRate m y).1 a.1 : ℝ) *
        ENNReal.ofReal (boolMass (extractionRate m y).2 a.2 : ℝ) * f a := by
  haveI := coin_probability _ (extractionRate_bounds m y).1
  haveI := coin_probability _ (extractionRate_bounds m y).2
  change (∫⁻ a, f a ∂(coin _).prod (coin _)) = _
  rw [MeasureTheory.lintegral_prod _ (Measurable.of_discrete.aemeasurable)]
  simp only [coin_lintegral]
  simp [Fintype.sum_prod_type, sum_bool, boolMass, mul_add, mul_assoc, add_comm, add_left_comm]

/-- Every atom of the ACTUAL typed induced kernel equals the explicit matrix
entry obtained in the frozen alpha→P→U order. No matrix-correspondence premise. -/
theorem inducedKernel_atom_entry (m : Mode) (y z : Y) :
    (model m).inducedKernel y {z} = transitionEntry m y z := by
  classical
  rw [StrategicWorldModel.inducedKernel_apply _ _ (measurableSet_singleton z)]
  change (∫⁻ a, ∫⁻ x, (update m ((y, a), x)) {q | (q, x) ∈ ({z} : Set Y)}
    ∂coin (pRep y.2 a) ∂action m y) = _
  rw [action_lintegral]
  unfold transitionEntry
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  rw [coin_lintegral]
  simp [update, Kernel.deterministic_apply, Measure.dirac_apply,
    sum_bool, boolMass, add_comm]

end PermanssonResearch.X1
