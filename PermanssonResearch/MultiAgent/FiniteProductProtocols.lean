import PermanssonResearch.MultiAgent.AutonomousKey
import PermanssonResearch.MultiAgent.AdaptationBound
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Fintype.Pi

/-! F-N, explicit finite-coordinate profile. The index set AND all state/action
coordinates here are finite. Actual `Measure.pi` rows define the action/update
kernels. This does not purport to construct a product kernel over arbitrary
measurable coordinate spaces or represent every game by independent actions. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultiAgent.FiniteProduct

set_option autoImplicit false
open PermanssonLean PermanssonLean.RegimeSpecification

universe uI u0 uS uX uA
variable {I : Type uI} {S0 : Type u0} {S : I → Type uS} {X : Type uX} {A : I → Type uA}
variable [Fintype I] [DecidableEq I]
variable [MeasurableSpace S0] [∀ i, MeasurableSpace (S i)]
variable [MeasurableSpace X] [∀ i, MeasurableSpace (A i)]

abbrev StrategicState (S0 : Type u0) {I : Type uI} (S : I → Type uS) := S0 × (∀ i, S i)

variable (S0 S X A) in
structure Mechanism (i : I) where
  action : Kernel (JointState (StrategicState S0 S) X) (A i)
  update : Kernel (UpdateInput (StrategicState S0 S) X (∀ j, A j)) (S i)
  action_isMarkov : IsMarkovKernel action
  update_isMarkov : IsMarkovKernel update

variable (S0 S X A) in
structure Generator where
  component : ∀ i, Mechanism S0 S X A i
  common : Kernel (UpdateInput (StrategicState S0 S) X (∀ j, A j)) S0
  common_isMarkov : IsMarkovKernel common

variable [Fintype S0] [∀ i, Fintype (S i)] [Fintype X] [∀ i, Fintype (A i)]
variable [MeasurableSingletonClass S0] [∀ i, MeasurableSingletonClass (S i)]
variable [MeasurableSingletonClass X] [∀ i, MeasurableSingletonClass (A i)]

/-- The finite-domain measurability proof applies to the actual product of
the supplied conditional measures, rather than invented rational weights. -/
noncomputable def productKernel {Y : Type*} [MeasurableSpace Y] [Finite Y]
    [MeasurableSingletonClass Y] {Z : I → Type*} [∀ i, MeasurableSpace (Z i)]
    (κ : ∀ i, Kernel Y (Z i)) : Kernel Y (∀ i, Z i) where
  toFun y := Measure.pi (fun i => κ i y)
  measurable' := measurable_of_finite _

instance productKernel_isMarkov {Y : Type*} [MeasurableSpace Y] [Finite Y]
    [MeasurableSingletonClass Y] {Z : I → Type*} [∀ i, MeasurableSpace (Z i)]
    (κ : ∀ i, Kernel Y (Z i)) [∀ i, IsMarkovKernel (κ i)] :
    IsMarkovKernel (productKernel κ) := ⟨fun y => by
  change IsProbabilityMeasure (Measure.pi (fun i => κ i y))
  infer_instance⟩

namespace Generator

noncomputable def toGenerator (G : Generator S0 S X A) :
    StrategicGenerator (StrategicState S0 S) X (∀ i, A i) where
  action := productKernel (fun i => (G.component i).action)
  update := G.common ×ₖ productKernel (fun i => (G.component i).update)
  action_isMarkov := by
    letI : ∀ i, IsMarkovKernel (G.component i).action := fun i => (G.component i).action_isMarkov
    infer_instance
  update_isMarkov := by
    letI := G.common_isMarkov
    letI : ∀ i, IsMarkovKernel (G.component i).update := fun i => (G.component i).update_isMarkov
    infer_instance

noncomputable def toModel (G : Generator S0 S X A)
    (P : Kernel (WorldInput (StrategicState S0 S) X (∀ i, A i)) X) [hP : IsMarkovKernel P] :
    StrategicWorldModel (StrategicState S0 S) X (∀ i, A i) := ⟨G.toGenerator,P,hP⟩

theorem action_cylinder (G : Generator S0 S X A) (y : JointState (StrategicState S0 S) X)
    (E : ∀ i, Set (A i)) :
    G.toGenerator.action y (Set.pi Set.univ E) = ∏ i, (G.component i).action y (E i) := by
  letI : ∀ i, IsMarkovKernel (G.component i).action := fun i => (G.component i).action_isMarkov
  exact Measure.pi_pi _ _

theorem update_cylinder (G : Generator S0 S X A)
    (v : UpdateInput (StrategicState S0 S) X (∀ i, A i))
    (E0 : Set S0) (E : ∀ i, Set (S i)) :
    G.toGenerator.update v (E0 ×ˢ Set.pi Set.univ E) =
      G.common v E0 * ∏ i, (G.component i).update v (E i) := by
  letI := G.common_isMarkov
  letI : ∀ i, IsMarkovKernel (G.component i).update := fun i => (G.component i).update_isMarkov
  change (G.common ×ₖ productKernel (fun i => (G.component i).update)) v _ = _
  rw [Kernel.prod_apply,Measure.prod_prod]
  rw [show productKernel (fun i => (G.component i).update) v =
    Measure.pi (fun i => (G.component i).update v) from rfl,Measure.pi_pi]

theorem action_atom (G : Generator S0 S X A)
    (y : JointState (StrategicState S0 S) X) (a : ∀ i, A i) :
    G.toGenerator.action y {a} = ∏ i, (G.component i).action y {a i} := by
  letI : ∀ i, IsMarkovKernel (G.component i).action := fun i => (G.component i).action_isMarkov
  exact Measure.pi_singleton _ _

theorem update_atom (G : Generator S0 S X A)
    (v : UpdateInput (StrategicState S0 S) X (∀ i, A i)) (s0 : S0) (s : ∀ i, S i) :
    G.toGenerator.update v {(s0,s)} =
      G.common v {s0} * ∏ i, (G.component i).update v {s i} := by
  letI := G.common_isMarkov
  letI : ∀ i, IsMarkovKernel (G.component i).update := fun i => (G.component i).update_isMarkov
  change (G.common ×ₖ productKernel (fun i => (G.component i).update)) v _ = _
  rw [Kernel.prod_apply,← Set.singleton_prod_singleton,Measure.prod_prod]
  rw [show productKernel (fun i => (G.component i).update) v =
    Measure.pi (fun i => (G.component i).update v) from rfl,Measure.pi_singleton]

/-- The complete actual original alpha/P/U row, with the finite indexed
conditional action and update products. -/
theorem actual_atom (G : Generator S0 S X A)
    (P : Kernel (WorldInput (StrategicState S0 S) X (∀ i, A i)) X) [IsMarkovKernel P]
    (y : JointState (StrategicState S0 S) X) (s0 : S0) (s : ∀ i, S i) (x : X) :
    (G.toModel P).inducedKernel y {((s0,s),x)} = ∑ a : ∀ i, A i,
      (∏ i, (G.component i).action y {a i}) * P (y,a) {x} *
        G.common ((y,a),x) {s0} * ∏ i, (G.component i).update ((y,a),x) {s i} := by
  classical
  rw [Autonomous.finite_inducedKernel_atom]
  apply Finset.sum_congr rfl
  intro a _
  change G.toGenerator.action y {a} * P (y,a) {x} *
    G.toGenerator.update ((y,a),x) {(s0,s)} = _
  rw [action_atom,update_atom]
  ring

/-- Only the selected player's action/update pair is replaced. -/
noncomputable def closedLoop (G : Generator S0 S X A) (i : I) (r : Mechanism S0 S X A i) :
    Generator S0 S X A := { G with component := Function.update G.component i r }

/-- Install the declared opponent profile and overwrite its treated coordinate
with the same common replacement used in the closed-loop comparison. -/
noncomputable def openLoop (G : Generator S0 S X A) (i : I) (r : Mechanism S0 S X A i)
    (anchor : ∀ j, Mechanism S0 S X A j) : Generator S0 S X A :=
  { G with component := Function.update anchor i r }

@[simp] theorem closedLoop_self (G : Generator S0 S X A) (i : I)
    (r : Mechanism S0 S X A i) : (G.closedLoop i r).component i = r := by simp [closedLoop]

theorem closedLoop_other (G : Generator S0 S X A) (i j : I) (h : j ≠ i)
    (r : Mechanism S0 S X A i) : (G.closedLoop i r).component j = G.component j := by
  simp [closedLoop,h]

@[simp] theorem openLoop_self (G : Generator S0 S X A) (i : I)
    (r : Mechanism S0 S X A i) (a : ∀ j, Mechanism S0 S X A j) :
    (G.openLoop i r a).component i = r := by simp [openLoop]

theorem openLoop_other (G : Generator S0 S X A) (i j : I) (h : j ≠ i)
    (r : Mechanism S0 S X A i) (a : ∀ j, Mechanism S0 S X A j) :
    (G.openLoop i r a).component j = a j := by simp [openLoop,h]

@[simp] theorem closedLoop_common (G : Generator S0 S X A) (i : I)
    (r : Mechanism S0 S X A i) : (G.closedLoop i r).common = G.common := rfl

@[simp] theorem openLoop_common (G : Generator S0 S X A) (i : I)
    (r : Mechanism S0 S X A i) (a : ∀ j, Mechanism S0 S X A j) :
    (G.openLoop i r a).common = G.common := rfl

end Generator

noncomputable def protocolFamily (G : Generator S0 S X A)
    (P : Kernel (WorldInput (StrategicState S0 S) X (∀ i, A i)) X) [IsMarkovKernel P]
    (i : I) (r : Mechanism S0 S X A i)
    (anchors : Set (∀ j, Mechanism S0 S X A j)) : InterventionFamily (G.toModel P) Protocol where
  targetOf _ := .jointStrategic
  admissible
    | .closedLoop, gen => gen = (G.closedLoop i r).toGenerator
    | .openLoop, gen => ∃ a ∈ anchors, gen = (G.openLoop i r a).toGenerator

noncomputable def closedLoopIntervention (G : Generator S0 S X A)
    (P : Kernel (WorldInput (StrategicState S0 S) X (∀ i, A i)) X) [IsMarkovKernel P]
    (i : I) (r : Mechanism S0 S X A i) (anchors : Set (∀ j, Mechanism S0 S X A j)) :
    AdmissibleStrategicIntervention (protocolFamily G P i r anchors) where
  intervention := ⟨.closedLoop,(G.closedLoop i r).toGenerator⟩
  accepted := rfl
  strategic := InterventionTarget.isStrategic_jointStrategic

noncomputable def openLoopIntervention (G : Generator S0 S X A)
    (P : Kernel (WorldInput (StrategicState S0 S) X (∀ i, A i)) X) [IsMarkovKernel P]
    (i : I) (r : Mechanism S0 S X A i) (anchors : Set (∀ j, Mechanism S0 S X A j))
    (a : ∀ j, Mechanism S0 S X A j) (ha : a ∈ anchors) :
    AdmissibleStrategicIntervention (protocolFamily G P i r anchors) where
  intervention := ⟨.openLoop,(G.openLoop i r a).toGenerator⟩
  accepted := ⟨a,ha,rfl⟩
  strategic := InterventionTarget.isStrategic_jointStrategic

theorem protocol_world_eq (G : Generator S0 S X A)
    (P : Kernel (WorldInput (StrategicState S0 S) X (∀ i, A i)) X) [IsMarkovKernel P]
    (i : I) (r : Mechanism S0 S X A i) (anchors : Set (∀ j, Mechanism S0 S X A j))
    (J : AdmissibleStrategicIntervention (protocolFamily G P i r anchors)) :
    J.intervention.apply.world = P := J.world_eq

theorem protocol_gap_bounds {Z : Type*} [MetricSpace Z] (G : Generator S0 S X A)
    (P : Kernel (WorldInput (StrategicState S0 S) X (∀ i, A i)) X) [IsMarkovKernel P]
    (i : I) (r : Mechanism S0 S X A i) (anchors : Set (∀ j, Mechanism S0 S X A j))
    (a : ∀ j, Mechanism S0 S X A j) (ha : a ∈ anchors)
    (ψ : RegimePropertyMap (JointState (StrategicState S0 S) X) Z)
    (y : JointState (StrategicState S0 S) X) :
    |constitutiveEffect (G.toModel P) ψ (closedLoopIntervention G P i r anchors) y -
      constitutiveEffect (G.toModel P) ψ (openLoopIntervention G P i r anchors a ha) y| ≤
      protocolGap ψ (closedLoopIntervention G P i r anchors)
        (openLoopIntervention G P i r anchors a ha) y ∧
    protocolGap ψ (closedLoopIntervention G P i r anchors)
        (openLoopIntervention G P i r anchors a ha) y ≤
      constitutiveEffect (G.toModel P) ψ (closedLoopIntervention G P i r anchors) y +
        constitutiveEffect (G.toModel P) ψ (openLoopIntervention G P i r anchors a ha) y :=
  ⟨abs_effect_sub_le_protocolGap _ ψ _ _ y,protocolGap_le_effect_add _ ψ _ _ y⟩

theorem original_margin_comparison {H Z : Type*} [MeasurableSpace H] [MetricSpace Z]
    (G : Generator S0 S X A)
    (P : Kernel (WorldInput (StrategicState S0 S) X (∀ i, A i)) X) [IsMarkovKernel P]
    (i : I) (r : Mechanism S0 S X A i) (anchors : Set (∀ j, Mechanism S0 S X A j))
    (a : ∀ j, Mechanism S0 S X A j) (ha : a ∈ anchors)
    (spec : RegimeSpecification (JointState (StrategicState S0 S) X) H)
    (ψ : RegimePropertyMap (JointState (StrategicState S0 S) X) Z)
    (B : ConstitutiveComparisonSet (G.toModel P) spec) (δ : ℝ)
    (hδ : ∀ y ∈ B.states, protocolGap ψ (closedLoopIntervention G P i r anchors)
      (openLoopIntervention G P i r anchors a ha) y ≤ δ) :
    |constitutiveMargin (G.toModel P) spec (protocolFamily G P i r anchors) ψ B
        (closedLoopIntervention G P i r anchors) -
      constitutiveMargin (G.toModel P) spec (protocolFamily G P i r anchors) ψ B
        (openLoopIntervention G P i r anchors a ha)| ≤ δ :=
  abs_constitutiveMargin_sub_le_of_protocolGap _ _ _ _ _ _ _ hδ

/-- Reduction of the actual indexed product measure to the existing binary
conditional product, using the measurable coordinate equivalence. -/
theorem productKernel_two {Y : Type*} [MeasurableSpace Y] [Finite Y]
    [MeasurableSingletonClass Y] {Z : Fin 2 → Type*} [∀ i, MeasurableSpace (Z i)]
    (κ : ∀ i, Kernel Y (Z i)) [∀ i, IsMarkovKernel (κ i)] (y : Y) :
    (productKernel κ y).map (MeasurableEquiv.piFinTwo Z) = (κ 0 y).prod (κ 1 y) :=
  (measurePreserving_piFinTwo (fun i => κ i y)).map_eq

theorem no_treated_empty : ¬ Nonempty (Fin 0) := by simp

end PermanssonResearch.MultiAgent.FiniteProduct
