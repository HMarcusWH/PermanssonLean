import PermanssonResearch.MultiAgent.MeasurableProductProtocols

namespace PermanssonResearch.MultiAgent.MeasurableProduct.Regression

open MeasureTheory ProbabilityTheory Set PermanssonLean
open scoped ENNReal ProbabilityTheory

noncomputable section

abbrev S := Fin 3 → ℝ
abbrev Y := JointState (Unit × S) Unit
abbrev A := Fin 3 → ℝ

def component (i : Fin 3) (a u : ℝ) :
    FiniteProduct.Mechanism Unit (fun _ : Fin 3 => ℝ) Unit (fun _ : Fin 3 => ℝ) i where
  action := Kernel.const Y (Measure.dirac a)
  update := Kernel.const (UpdateInput (Unit × S) Unit A) (Measure.dirac u)
  action_isMarkov := inferInstance
  update_isMarkov := inferInstance

def baseline : FiniteProduct.Generator Unit (fun _ : Fin 3 => ℝ) Unit (fun _ : Fin 3 => ℝ) where
  component i := component i (i : ℝ) 0
  common := Kernel.const _ (Measure.dirac ())
  common_isMarkov := inferInstance

def anchors (i : Fin 3) :
    FiniteProduct.Mechanism Unit (fun _ : Fin 3 => ℝ) Unit (fun _ : Fin 3 => ℝ) i :=
  component i (100+(i : ℝ)) (200+(i : ℝ))

def replacement := component 1 10 20

def cl := closedLoop baseline 1 replacement
def ol := openLoop baseline 1 replacement anchors

def physical : Kernel (WorldInput (Unit × S) Unit A) Unit :=
  Kernel.const _ (Measure.dirac ())

instance physical_isMarkov : IsMarkovKernel physical := by unfold physical; infer_instance

def actionZeroCylinder : Set A := pi univ (fun i => if i=0 then ({0} : Set ℝ) else univ)

theorem cl_action_zero_cylinder (y : Y) : (assemble cl).action y actionZeroCylinder = 1 := by
  letI : ∀ i, IsMarkovKernel (cl.component i).action := fun i => (cl.component i).action_isMarkov
  rw [action_apply]
  unfold actionZeroCylinder
  rw [Measure.pi_pi]
  apply Finset.prod_eq_one
  intro i hi
  by_cases h0 : i=0
  · subst i
    norm_num [cl,closedLoop,baseline,replacement,component,Kernel.const_apply]
  · simp only [h0,ite_eq_right]
    exact measure_univ

theorem ol_action_zero_cylinder (y : Y) : (assemble ol).action y actionZeroCylinder = 0 := by
  letI : ∀ i, IsMarkovKernel (ol.component i).action := fun i => (ol.component i).action_isMarkov
  rw [action_apply]
  unfold actionZeroCylinder
  rw [Measure.pi_pi]
  apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 3))
  norm_num [ol,openLoop,anchors,replacement,component,Kernel.const_apply]

theorem actual_action_laws_distinct (y : Y) : (assemble cl).action y ≠ (assemble ol).action y := by
  intro h
  have hv := congrArg (fun μ : Measure A => μ actionZeroCylinder) h
  rw [cl_action_zero_cylinder,ol_action_zero_cylinder] at hv
  exact one_ne_zero hv

def treatedCylinder : Set A := pi univ (fun i => if i=1 then ({10} : Set ℝ) else univ)

theorem cl_treated_action (y : Y) : (assemble cl).action y treatedCylinder = 1 := by
  letI : ∀ i, IsMarkovKernel (cl.component i).action := fun i => (cl.component i).action_isMarkov
  rw [action_apply]
  unfold treatedCylinder
  rw [Measure.pi_pi]
  apply Finset.prod_eq_one
  intro i hi
  by_cases h1 : i=1
  · subst i
    norm_num [cl,closedLoop,baseline,replacement,component,Kernel.const_apply]
  · simp only [h1,ite_eq_right]
    exact measure_univ

theorem ol_treated_action (y : Y) : (assemble ol).action y treatedCylinder = 1 := by
  letI : ∀ i, IsMarkovKernel (ol.component i).action := fun i => (ol.component i).action_isMarkov
  rw [action_apply]
  unfold treatedCylinder
  rw [Measure.pi_pi]
  apply Finset.prod_eq_one
  intro i hi
  by_cases h1 : i=1
  · subst i
    norm_num [ol,openLoop,anchors,replacement,component,Kernel.const_apply]
  · simp only [h1,ite_eq_right]
    exact measure_univ

theorem replacement_update (v : UpdateInput (Unit × S) Unit A) :
    ((cl.component 1).update v) {20} = 1 ∧ ((ol.component 1).update v) {20} = 1 := by
  norm_num [cl,ol,closedLoop,openLoop,replacement,component,Kernel.const_apply]

theorem common_and_world_preserved : cl.common = baseline.common ∧ ol.common = baseline.common ∧
    (model cl physical).world = physical ∧ (model ol physical).world = physical := by
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- With no player indices the actual product law is the unique empty tuple. -/
theorem empty_product {D : Type*} [MeasurableSpace D]
    {Z : Fin 0 → Type*} [∀ i, MeasurableSpace (Z i)]
    (κ : ∀ i, Kernel D (Z i)) [∀ i, IsMarkovKernel (κ i)] (d : D) :
    productKernel κ d = Measure.dirac (fun i => Fin.elim0 i) :=
  Measure.pi_of_empty _ _

end
end PermanssonResearch.MultiAgent.MeasurableProduct.Regression
