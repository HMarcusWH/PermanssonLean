import PermanssonResearch.MultiAgent.FiniteProductProtocols
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! Finite player index sets with arbitrary measurable coordinate spaces.
Actual finite product probabilities are measurable kernels by a generating
rectangle argument. No finiteness of states, actions or kernel inputs is used.
-/

namespace PermanssonResearch.MultiAgent.MeasurableProduct

open MeasureTheory ProbabilityTheory Set PermanssonLean
open scoped ENNReal ProbabilityTheory

noncomputable section

universe uI u0 uS uX uA

variable {I : Type uI} [Fintype I]

theorem measurable_product {Y : Type*} [MeasurableSpace Y]
    {Z : I → Type*} [∀ i, MeasurableSpace (Z i)]
    (κ : ∀ i, Kernel Y (Z i)) [∀ i, IsMarkovKernel (κ i)] :
    Measurable (fun y => Measure.pi (fun i => κ i y)) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_pi.symm isPiSystem_pi
  rintro E ⟨s,hs,rfl⟩
  simp only [Measure.pi_pi]
  exact Finset.measurable_prod _ fun i _ => (κ i).measurable_coe (hs i (mem_univ i))

def productKernel {Y : Type*} [MeasurableSpace Y]
    {Z : I → Type*} [∀ i, MeasurableSpace (Z i)]
    (κ : ∀ i, Kernel Y (Z i)) [∀ i, IsMarkovKernel (κ i)] : Kernel Y (∀ i, Z i) where
  toFun y := Measure.pi (fun i => κ i y)
  measurable' := measurable_product κ

instance productKernel_isMarkov {Y : Type*} [MeasurableSpace Y]
    {Z : I → Type*} [∀ i, MeasurableSpace (Z i)]
    (κ : ∀ i, Kernel Y (Z i)) [∀ i, IsMarkovKernel (κ i)] :
    IsMarkovKernel (productKernel κ) := ⟨fun y => by
  change IsProbabilityMeasure (Measure.pi (fun i => κ i y))
  infer_instance⟩

theorem productKernel_cylinder {Y : Type*} [MeasurableSpace Y]
    {Z : I → Type*} [∀ i, MeasurableSpace (Z i)]
    (κ : ∀ i, Kernel Y (Z i)) [∀ i, IsMarkovKernel (κ i)] (y : Y)
    (E : ∀ i, Set (Z i)) : productKernel κ y (pi univ E) = ∏ i, κ i y (E i) :=
  Measure.pi_pi _ _

variable {S0 : Type u0} {S : I → Type uS} {X : Type uX} {A : I → Type uA}
variable [MeasurableSpace S0] [∀ i, MeasurableSpace (S i)]
variable [MeasurableSpace X] [∀ i, MeasurableSpace (A i)]

def actionKernel (G : FiniteProduct.Generator S0 S X A) :
    Kernel (JointState (FiniteProduct.StrategicState S0 S) X) (∀ i, A i) := by
  letI : ∀ i, IsMarkovKernel (G.component i).action := fun i => (G.component i).action_isMarkov
  exact productKernel (fun i => (G.component i).action)

instance actionKernel_isMarkov (G : FiniteProduct.Generator S0 S X A) :
    IsMarkovKernel (actionKernel G) := by
  unfold actionKernel
  infer_instance

def privateUpdateKernel (G : FiniteProduct.Generator S0 S X A) :
    Kernel (UpdateInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) (∀ i, S i) := by
  letI : ∀ i, IsMarkovKernel (G.component i).update := fun i => (G.component i).update_isMarkov
  exact productKernel (fun i => (G.component i).update)

instance privateUpdateKernel_isMarkov (G : FiniteProduct.Generator S0 S X A) :
    IsMarkovKernel (privateUpdateKernel G) := by
  unfold privateUpdateKernel
  infer_instance

def assemble (G : FiniteProduct.Generator S0 S X A) :
    StrategicGenerator (FiniteProduct.StrategicState S0 S) X (∀ i, A i) where
  action := actionKernel G
  update := G.common ×ₖ privateUpdateKernel G
  action_isMarkov := inferInstance
  update_isMarkov := by
    letI := G.common_isMarkov
    infer_instance

def model (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [hP : IsMarkovKernel P] : StrategicWorldModel (FiniteProduct.StrategicState S0 S) X (∀ i, A i) :=
  ⟨assemble G,P,hP⟩

theorem action_apply (G : FiniteProduct.Generator S0 S X A)
    (y : JointState (FiniteProduct.StrategicState S0 S) X) :
    (assemble G).action y = Measure.pi (fun i => (G.component i).action y) := rfl

theorem update_apply (G : FiniteProduct.Generator S0 S X A)
    (v : UpdateInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) :
    (assemble G).update v = (G.common v).prod (Measure.pi (fun i => (G.component i).update v)) := by
  letI := G.common_isMarkov
  rw [assemble, Kernel.prod_apply]
  rfl

/-- Actual typed alpha/P/U transition with arbitrary measurable coordinates. -/
theorem actual_transition (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] (y : JointState (FiniteProduct.StrategicState S0 S) X)
    {E : Set (JointState (FiniteProduct.StrategicState S0 S) X)} (hE : MeasurableSet E) :
    (model G P).inducedKernel y E =
      ∫⁻ a, ∫⁻ x, ((G.common ((y,a),x)).prod
        (Measure.pi (fun i => (G.component i).update ((y,a),x)))) {s | (s,x) ∈ E}
        ∂P (y,a) ∂Measure.pi (fun i => (G.component i).action y) := by
  rw [StrategicWorldModel.inducedKernel_apply _ _ hE]
  simp only [model,action_apply,update_apply]

section FiniteCompatibility

variable [DecidableEq I]
variable [Fintype S0] [∀ i, Fintype (S i)] [Fintype X] [∀ i, Fintype (A i)]
variable [MeasurableSingletonClass S0] [∀ i, MeasurableSingletonClass (S i)]
variable [MeasurableSingletonClass X] [∀ i, MeasurableSingletonClass (A i)]

theorem assemble_eq_finite (G : FiniteProduct.Generator S0 S X A) :
    assemble G = G.toGenerator := rfl

theorem model_eq_finite (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P] : model G P = G.toModel P := rfl

end FiniteCompatibility
end
end PermanssonResearch.MultiAgent.MeasurableProduct
