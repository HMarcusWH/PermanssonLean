import PermanssonResearch.GrammarRobust.BooleanDynamics
import PermanssonLean.Examples.PeriodicExactGR
import Mathlib.Tactic

/-!
# Lane B: full canonical path law for a deterministic constant-target kernel

This reusable bridge is specialized to the finite Boolean strategic-world
state space, but polymorphic in the actual typed model and its target state.
When every induced transition is Dirac(q), the *whole infinite path law* is
the push-forward of the initial law under the trajectory y,q,q,q,... .
No path property is postulated.
-/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch
namespace GrammarRobust
namespace ConstantDynamics

open PermanssonLean BooleanModel

noncomputable section

def orbit (q y : Y) : ℕ → Y
  | 0 => y
  | _ + 1 => q

@[simp] theorem orbit_zero (q y : Y) : orbit q y 0 = y := rfl
@[simp] theorem orbit_succ (q y : Y) (n : ℕ) :
    orbit q y (n + 1) = q := rfl

theorem measurable_orbit (q : Y) : Measurable (orbit q) := by
  rw [measurable_pi_iff]
  intro n
  exact Measurable.of_discrete

theorem stationaryKernel_eq_deterministic
    (M : StrategicWorldModel Bool Bool Bool) (q : Y)
    (hK : ∀ y : Y, M.inducedKernel y = Measure.dirac q)
    (n : ℕ) :
    StrategicWorldModel.stationaryHistoryKernel M.inducedKernel n =
      Kernel.deterministic (fun _ : (i : Finset.Iic n) → Y => q)
        (by fun_prop) := by
  ext h E hE
  rw [StrategicWorldModel.stationaryHistoryKernel, Kernel.comap_apply]
  rw [hK]
  rw [Kernel.deterministic_apply]

noncomputable def orbitLaw (q : Y) (μ : ProbabilityMeasure Y) :
    Measure (ℕ → Y) :=
  μ.toMeasure.map (orbit q)

instance orbitLaw_probability (q : Y) (μ : ProbabilityMeasure Y) :
    IsProbabilityMeasure (orbitLaw q μ) := by
  unfold orbitLaw
  infer_instance

theorem orbitLaw_initialPrefix (q : Y) (μ : ProbabilityMeasure Y) :
    (orbitLaw q μ).map (Preorder.frestrictLe 0) =
      μ.toMeasure.map
        (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Y)).symm := by
  unfold orbitLaw
  rw [Measure.map_map (by fun_prop) (measurable_orbit q)]
  apply Measure.map_congr
  filter_upwards [] with y
  funext i
  have hi : (i : ℕ) = 0 :=
    Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.2)
  change orbit q y (i : ℕ) = y
  rw [hi, orbit_zero]

theorem orbitLaw_transitionPairs
    (M : StrategicWorldModel Bool Bool Bool) (q : Y)
    (hK : ∀ y : Y, M.inducedKernel y = Measure.dirac q)
    (μ : ProbabilityMeasure Y) :
    StrategicWorldModel.HasTransitionPair
      (orbitLaw q μ) M.inducedKernel := by
  intro n
  rw [stationaryKernel_eq_deterministic M q hK n]
  rw [Measure.compProd_deterministic]
  unfold orbitLaw
  rw [Measure.map_map (by fun_prop) (measurable_orbit q)]
  rw [Measure.map_map (by fun_prop) (measurable_orbit q)]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  apply Measure.map_congr
  filter_upwards [] with y
  simp [Function.comp_apply, orbit_succ]

theorem pathLaw_eq_orbitLaw
    (M : StrategicWorldModel Bool Bool Bool) (q : Y)
    (hK : ∀ y : Y, M.inducedKernel y = Measure.dirac q)
    (μ : ProbabilityMeasure Y) :
    M.pathLaw μ.toMeasure = orbitLaw q μ := by
  exact (StrategicWorldModel.pathLaw_existsUnique M μ.toMeasure).unique
    (StrategicWorldModel.pathLaw_spec M μ.toMeasure)
    ⟨inferInstance, orbitLaw_initialPrefix q μ,
      orbitLaw_transitionPairs M q hK μ⟩

theorem pathLaw_point_eq_dirac
    (M : StrategicWorldModel Bool Bool Bool) (q : Y)
    (hK : ∀ y : Y, M.inducedKernel y = Measure.dirac q)
    (y : Y) :
    M.pathLaw (Measure.dirac y) = Measure.dirac (orbit q y) := by
  have h := pathLaw_eq_orbitLaw M q hK (diracProba y)
  simpa [orbitLaw, Measure.map_dirac] using h

end

end ConstantDynamics
end GrammarRobust
end PermanssonResearch
