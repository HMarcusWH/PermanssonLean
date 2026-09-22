import PermanssonLean.Intervention.Apply
import Mathlib.Probability.Kernel.Deterministic

open MeasureTheory ProbabilityTheory

namespace PermanssonLean

/-!
# Section 7 factorization counterexample

This file formalizes the finite typed counterexample behind Theorem 7.2 of
Permansson v0.1.7.  Two distinct strategic/world factorizations induce the
same baseline joint kernel, while both the strategic generator and the world
kernel differ.
-/

namespace Section7Counterexample

noncomputable section

/-- Baseline action kernel for factorization A: always select action `false`. -/
def actionA : Kernel (JointState Unit Bool) Bool :=
  Kernel.deterministic (fun _ => false) (by exact Measurable.of_discrete)

/-- Baseline action kernel for factorization B: always select action `true`. -/
def actionB : Kernel (JointState Unit Bool) Bool :=
  Kernel.deterministic (fun _ => true) (by exact Measurable.of_discrete)

/-- The strategic memory is semantically inert in the finite witness. -/
def updateUnit : Kernel (UpdateInput Unit Bool Bool) Unit :=
  Kernel.deterministic (fun _ => ()) (by exact Measurable.of_discrete)

/-- Factorization A: the world ignores the action and preserves the world bit. -/
def worldA : Kernel (WorldInput Unit Bool Bool) Bool :=
  Kernel.deterministic (fun z => z.1.2) (by exact Measurable.of_discrete)

/-- Factorization B: the baseline action `true` preserves the world bit, while
`false` flips it.  Hence the baseline process agrees with factorization A,
but the typed counterfactual response can differ. -/
def worldB : Kernel (WorldInput Unit Bool Bool) Bool :=
  Kernel.deterministic
    (fun z => if z.2 then z.1.2 else Bool.not z.1.2)
    (by exact Measurable.of_discrete)

def generatorA : StrategicGenerator Unit Bool Bool where
  action := actionA
  update := updateUnit
  action_isMarkov := by
    unfold actionA
    infer_instance
  update_isMarkov := by
    unfold updateUnit
    infer_instance

def generatorB : StrategicGenerator Unit Bool Bool where
  action := actionB
  update := updateUnit
  action_isMarkov := by
    unfold actionB
    infer_instance
  update_isMarkov := by
    unfold updateUnit
    infer_instance

def factorizationA : StrategicWorldModel Unit Bool Bool where
  generator := generatorA
  world := worldA
  world_isMarkov := by
    unfold worldA
    infer_instance

def factorizationB : StrategicWorldModel Unit Bool Bool where
  generator := generatorB
  world := worldB
  world_isMarkov := by
    unfold worldB
    infer_instance

/-- The two finite factorizations induce exactly the same baseline joint kernel. -/
theorem inducedKernel_eq :
    factorizationA.inducedKernel = factorizationB.inducedKernel := by
  ext y E hE
  rw [StrategicWorldModel.inducedKernel_apply factorizationA y hE,
      StrategicWorldModel.inducedKernel_apply factorizationB y hE]
  rcases y with ⟨s, x⟩
  rcases s with ⟨⟩
  cases x <;>
    simp [factorizationA, factorizationB, generatorA, generatorB,
      actionA, actionB, updateUnit, worldA, worldB,
      Kernel.deterministic_apply]

/-- The strategic generators themselves are not equal. -/
theorem generator_ne :
    factorizationA.generator ≠ factorizationB.generator := by
  intro h
  have ha :
      factorizationA.generator.action = factorizationB.generator.action :=
    congrArg StrategicGenerator.action h
  have happ :=
    congrArg
      (fun k : Kernel (JointState Unit Bool) Bool =>
        k ((), false) ({false} : Set Bool))
      ha
  simpa [factorizationA, factorizationB, generatorA, generatorB,
    actionA, actionB, Kernel.deterministic_apply] using happ

/-- The world-transition kernels are not equal either. -/
theorem world_ne :
    factorizationA.world ≠ factorizationB.world := by
  intro h
  have happ :=
    congrArg
      (fun k : Kernel (WorldInput Unit Bool Bool) Bool =>
        k (((), false), false) ({false} : Set Bool))
      h
  simpa [factorizationA, factorizationB, worldA, worldB,
    Kernel.deterministic_apply] using happ

/-- Theorem 7.2, finite witness form: equality of the induced joint process
does not identify either the strategic generator or the world kernel. -/
theorem factorization_nonidentification :
    ∃ M₁ M₂ : StrategicWorldModel Unit Bool Bool,
      M₁.inducedKernel = M₂.inducedKernel ∧
      M₁.generator ≠ M₂.generator ∧
      M₁.world ≠ M₂.world := by
  exact ⟨factorizationA, factorizationB, inducedKernel_eq, generator_ne, world_ne⟩

end

end Section7Counterexample

end PermanssonLean
