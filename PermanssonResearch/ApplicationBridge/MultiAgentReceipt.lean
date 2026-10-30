import PermanssonResearch.MultiAgent.FiniteProductTwo
import PermanssonResearch.MultiAgent.MeasurableProductTwoOriginalMarginClosure
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

/-!
# ApplicationBridge — finite two-player protocol receipts

A receipt declares a finite two-player protocol by rational tables: for each
player an action row on the joint state and an update row for its private
state on (joint state, joint action, next world); a common update row; and
the physical world row P on (joint state, joint action). Both players have
`k` private states and `m` actions; there are `k0` common and `nx` world
states. Joint states and joint actions are encoded with `finProdFinEquiv`.

`tableKernel` turns a row-stochastic rational table into a Markov kernel
(PMF rows); `generator` assembles Research's `FiniteProduct.Generator` (the
joint action kernel is the actual product of the players' action kernels,
the update kernel the common update times the product of private updates)
and `world` the kernel P.

* `finite_protocol_induced_kernel` — the induced α/P/U kernel of the
  assembled model has exactly the rational joint rows (`jointRow`), via
  Research's `Generator.actual_atom`; the same holds after the closed-loop
  replacement of player `i`'s mechanism and after the open-loop protocol
  that installs a declared anchor profile and then the same replacement.
* `checked_marked_path_transport` — Research's binary reduction: the
  compressed path law of the indexed model is the path law of the binary
  two-player model, whose atoms are the same rational rows.
* `checked_matched_original_margin` — Research's matched closed-loop and
  open-loop margin closures for this protocol, for every specification,
  comparison set and binary whole-path property.

Physical P is never changed by a protocol (it is not part of the generator).
Asymmetric player types, mediated or correlated actions, private clocks and
empirical game identification are not claimed.
-/

namespace PermanssonResearch.ApplicationBridge.MultiAgentReceipt

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open PermanssonLean
open PermanssonResearch.MultiAgent
open PermanssonResearch.MultiAgent.FiniteProduct

set_option autoImplicit false

variable {k0 k nx m : ℕ}

abbrev SS (k : ℕ) : Fin 2 → Type := fun _ => Fin k
abbrev AA (m : ℕ) : Fin 2 → Type := fun _ => Fin m
abbrev JS (k0 k nx : ℕ) := JointState (StrategicState (Fin k0) (SS k)) (Fin nx)
abbrev JA (m : ℕ) := ∀ i : Fin 2, AA m i
abbrev NJ (k0 k nx : ℕ) := k0 * k * k * nx

def encState (y : JS k0 k nx) : Fin (NJ k0 k nx) :=
  finProdFinEquiv (finProdFinEquiv (finProdFinEquiv (y.1.1, y.1.2 0), y.1.2 1), y.2)

def encAction (a : JA m) : Fin (m * m) := finProdFinEquiv (a 0, a 1)

/-- A probability row. -/
def IsProb {β : Type*} [Fintype β] (r : β → ℚ) : Prop := (∀ b, 0 ≤ r b) ∧ (∑ b, r b) = 1

instance {β : Type*} [Fintype β] [DecidableEq β] (r : β → ℚ) : Decidable (IsProb r) := by
  unfold IsProb; infer_instance

noncomputable def lawOf {β : Type*} [Fintype β] [MeasurableSpace β] (r : β → ℚ) (h : IsProb r) :
    Measure β :=
  (PMF.ofFintype (fun b => ENNReal.ofReal (r b)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => by exact_mod_cast h.1 b)]
    have : (∑ b, (r b : ℝ)) = 1 := by exact_mod_cast h.2
    rw [this, ENNReal.ofReal_one])).toMeasure

instance {β : Type*} [Fintype β] [MeasurableSpace β] (r : β → ℚ) (h : IsProb r) :
    IsProbabilityMeasure (lawOf r h) := by
  unfold lawOf; infer_instance

theorem lawOf_singleton {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (r : β → ℚ) (h : IsProb r) (b : β) : lawOf r h {b} = ENNReal.ofReal (r b) := by
  unfold lawOf
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b)]
  rfl

/-- The Markov kernel with rational rows. -/
noncomputable def tableKernel {α β : Type*} [MeasurableSpace α] [Finite α] [MeasurableSingletonClass α]
    [Fintype β] [MeasurableSpace β] (f : α → β → ℚ) (h : ∀ a, IsProb (f a)) : Kernel α β where
  toFun a := lawOf (f a) (h a)
  measurable' := measurable_of_finite _

instance {α β : Type*} [MeasurableSpace α] [Finite α] [MeasurableSingletonClass α]
    [Fintype β] [MeasurableSpace β] (f : α → β → ℚ) (h : ∀ a, IsProb (f a)) :
    IsMarkovKernel (tableKernel f h) :=
  ⟨fun a => by unfold tableKernel; simp only [Kernel.coe_mk]; infer_instance⟩

theorem tableKernel_atom {α β : Type*} [MeasurableSpace α] [Finite α] [MeasurableSingletonClass α]
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] (f : α → β → ℚ)
    (h : ∀ a, IsProb (f a)) (a : α) (b : β) : tableKernel f h a {b} = ENNReal.ofReal (f a b) :=
  lawOf_singleton (f a) (h a) b

theorem nn {β : Type*} [Fintype β] {r : β → ℚ} (h : IsProb r) (b : β) : (0 : ℝ) ≤ (r b : ℝ) := by
  exact_mod_cast h.1 b

theorem ofReal_mul6 {a b c d e f : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) :
    ENNReal.ofReal (a * b * c * d * e * f) =
      ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c * ENNReal.ofReal d *
        (ENNReal.ofReal e * ENNReal.ofReal f) := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul ha]
  ring

/-- Player tables: action rows and private-update rows. -/
structure Player (k0 k nx m : ℕ) where
  act : Fin (NJ k0 k nx) → Fin m → ℚ
  upd : Fin (NJ k0 k nx) → Fin (m * m) → Fin nx → Fin k → ℚ

def Player.OK (p : Player k0 k nx m) : Prop :=
  (∀ y, IsProb (p.act y)) ∧ ∀ y a x, IsProb (p.upd y a x)

instance (p : Player k0 k nx m) : Decidable p.OK := by
  unfold Player.OK; infer_instance

/-- The mechanism of player `i` built from its tables. -/
noncomputable def mech (p : Player k0 k nx m) (hp : p.OK) (i : Fin 2) :
    Mechanism (Fin k0) (SS k) (Fin nx) (AA m) i where
  action := tableKernel (fun y : JS k0 k nx => p.act (encState y)) (fun _ => hp.1 _)
  update := tableKernel
    (fun v : UpdateInput (StrategicState (Fin k0) (SS k)) (Fin nx) (JA m) =>
      p.upd (encState v.1.1) (encAction v.1.2) v.2) (fun _ => hp.2 _ _ _)
  action_isMarkov := inferInstance
  update_isMarkov := inferInstance

/-- Common update and physical world tables. -/
structure Shared (k0 k nx m : ℕ) where
  common : Fin (NJ k0 k nx) → Fin (m * m) → Fin nx → Fin k0 → ℚ
  world : Fin (NJ k0 k nx) → Fin (m * m) → Fin nx → ℚ

def Shared.OK (c : Shared k0 k nx m) : Prop :=
  (∀ y a x, IsProb (c.common y a x)) ∧ ∀ y a, IsProb (c.world y a)

instance (c : Shared k0 k nx m) : Decidable c.OK := by
  unfold Shared.OK; infer_instance

noncomputable def generator (ps : Fin 2 → Player k0 k nx m) (hps : ∀ i, (ps i).OK)
    (c : Shared k0 k nx m) (hc : c.OK) : Generator (Fin k0) (SS k) (Fin nx) (AA m) where
  component i := mech (ps i) (hps i) i
  common := tableKernel
    (fun v : UpdateInput (StrategicState (Fin k0) (SS k)) (Fin nx) (JA m) =>
      c.common (encState v.1.1) (encAction v.1.2) v.2) (fun _ => hc.1 _ _ _)
  common_isMarkov := inferInstance

noncomputable def world (c : Shared k0 k nx m) (hc : c.OK) :
    Kernel (WorldInput (StrategicState (Fin k0) (SS k)) (Fin nx) (JA m)) (Fin nx) :=
  tableKernel (fun w => c.world (encState w.1) (encAction w.2)) (fun _ => hc.2 _ _)

instance (c : Shared k0 k nx m) (hc : c.OK) : IsMarkovKernel (world c hc) := by
  unfold world; infer_instance

/-- Rational joint row from the encoded state `y` to the decoded target. -/
def jointRow (p0 p1 : Player k0 k nx m) (c : Shared k0 k nx m) (y : Fin (NJ k0 k nx))
    (s0 : Fin k0) (t0 t1 : Fin k) (x : Fin nx) : ℚ :=
  ∑ a : Fin m × Fin m,
    p0.act y a.1 * p1.act y a.2 * c.world y (finProdFinEquiv a) x *
      c.common y (finProdFinEquiv a) x s0 *
      p0.upd y (finProdFinEquiv a) x t0 * p1.upd y (finProdFinEquiv a) x t1

/-- **Induced kernel.** The assembled two-player model has the rational joint rows. -/
theorem finite_protocol_induced_kernel (ps : Fin 2 → Player k0 k nx m) (hps : ∀ i, (ps i).OK)
    (c : Shared k0 k nx m) (hc : c.OK) (y : JS k0 k nx) (s0 : Fin k0) (s : ∀ _ : Fin 2, Fin k)
    (x : Fin nx) :
    ((generator ps hps c hc).toModel (world c hc)).inducedKernel y {((s0, s), x)} =
      ENNReal.ofReal (jointRow (ps 0) (ps 1) c (encState y) s0 (s 0) (s 1) x) := by
  rw [Generator.actual_atom]
  have h0 := hps 0
  have h1 := hps 1
  unfold jointRow
  push_cast
  rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => by
    have := nn (h0.1 (encState y)) a.1; have := nn (h1.1 (encState y)) a.2
    have := nn (hc.2 (encState y) (finProdFinEquiv a)) x
    have := nn (hc.1 (encState y) (finProdFinEquiv a) x) s0
    have := nn (h0.2 (encState y) (finProdFinEquiv a) x) (s 0)
    have := nn (h1.2 (encState y) (finProdFinEquiv a) x) (s 1)
    positivity)]
  rw [← (MeasurableEquiv.piFinTwo (AA m)).toEquiv.symm.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Fin.prod_univ_two, generator, mech, world, tableKernel_atom]
  have he : encAction ((MeasurableEquiv.piFinTwo (AA m)).toEquiv.symm a) = finProdFinEquiv a := by
    rcases a with ⟨a0, a1⟩; rfl
  have e1 : ((MeasurableEquiv.piFinTwo (AA m)).toEquiv.symm a) 0 = a.1 := by
    rcases a with ⟨a0, a1⟩; rfl
  have e2 : ((MeasurableEquiv.piFinTwo (AA m)).toEquiv.symm a) 1 = a.2 := by
    rcases a with ⟨a0, a1⟩; rfl
  simp only [he, e1, e2]
  exact (ofReal_mul6 (nn (h0.1 _) _) (nn (h1.1 _) _) (nn (hc.2 _ _) _) (nn (hc.1 _ _ _) _)
    (nn (h0.2 _ _ _) _)).symm

/-- The closed-loop protocol replaces player `i`'s mechanism by `r`. -/
theorem closedLoop_component (ps : Fin 2 → Player k0 k nx m) (hps : ∀ i, (ps i).OK)
    (c : Shared k0 k nx m) (hc : c.OK) (i : Fin 2) (r : Player k0 k nx m) (hr : r.OK) :
    (generator ps hps c hc).closedLoop i (mech r hr i) =
      generator (Function.update ps i r)
        (fun j => by by_cases h : j = i <;> simp [Function.update, h, hr, hps]) c hc := by
  unfold Generator.closedLoop generator
  congr 1
  funext j
  by_cases h : j = i
  · subst h; simp [Function.update]
  · simp [Function.update, h]

/-- The open-loop protocol installs the anchor profile and replaces player `i`. -/
theorem openLoop_component (ps : Fin 2 → Player k0 k nx m) (hps : ∀ i, (ps i).OK)
    (c : Shared k0 k nx m) (hc : c.OK) (i : Fin 2) (r : Player k0 k nx m) (hr : r.OK)
    (anchor : Fin 2 → Player k0 k nx m) (ha : ∀ j, (anchor j).OK) :
    (generator ps hps c hc).openLoop i (mech r hr i) (fun j => mech (anchor j) (ha j) j) =
      generator (Function.update anchor i r)
        (fun j => by by_cases h : j = i <;> simp [Function.update, h, hr, ha]) c hc := by
  unfold Generator.openLoop generator
  congr 1
  funext j
  by_cases h : j = i
  · subst h; simp [Function.update]
  · simp [Function.update, h]

/-- Declared joint matrices: the receipt's rational rows in encoded order. -/
def ProtocolChecks (ps : Fin 2 → Player k0 k nx m) (c : Shared k0 k nx m) (i : Fin 2)
    (r : Player k0 k nx m) (anchor : Fin 2 → Player k0 k nx m)
    (K Kc Ko : Fin (NJ k0 k nx) → Fin (NJ k0 k nx) → ℚ) : Prop :=
  (ps 0).OK ∧ (ps 1).OK ∧ c.OK ∧ r.OK ∧ (anchor 0).OK ∧ (anchor 1).OK ∧
  (∀ y s0 t0 t1 x, K y (finProdFinEquiv (finProdFinEquiv (finProdFinEquiv (s0, t0), t1), x)) =
    jointRow (ps 0) (ps 1) c y s0 t0 t1 x) ∧
  (∀ y s0 t0 t1 x, Kc y (finProdFinEquiv (finProdFinEquiv (finProdFinEquiv (s0, t0), t1), x)) =
    jointRow (Function.update ps i r 0) (Function.update ps i r 1) c y s0 t0 t1 x) ∧
  (∀ y s0 t0 t1 x, Ko y (finProdFinEquiv (finProdFinEquiv (finProdFinEquiv (s0, t0), t1), x)) =
    jointRow (Function.update anchor i r 0) (Function.update anchor i r 1) c y s0 t0 t1 x)

instance (ps : Fin 2 → Player k0 k nx m) (c : Shared k0 k nx m) (i : Fin 2)
    (r : Player k0 k nx m) (anchor : Fin 2 → Player k0 k nx m)
    (K Kc Ko : Fin (NJ k0 k nx) → Fin (NJ k0 k nx) → ℚ) :
    Decidable (ProtocolChecks ps c i r anchor K Kc Ko) := by
  unfold ProtocolChecks; infer_instance

def checkFiniteMultiAgentProtocol (ps : Fin 2 → Player k0 k nx m) (c : Shared k0 k nx m) (i : Fin 2)
    (r : Player k0 k nx m) (anchor : Fin 2 → Player k0 k nx m)
    (K Kc Ko : Fin (NJ k0 k nx) → Fin (NJ k0 k nx) → ℚ) : Bool :=
  decide (ProtocolChecks ps c i r anchor K Kc Ko)

theorem checkFiniteMultiAgentProtocol_sound (ps : Fin 2 → Player k0 k nx m) (c : Shared k0 k nx m)
    (i : Fin 2) (r : Player k0 k nx m) (anchor : Fin 2 → Player k0 k nx m)
    (K Kc Ko : Fin (NJ k0 k nx) → Fin (NJ k0 k nx) → ℚ)
    (h : checkFiniteMultiAgentProtocol ps c i r anchor K Kc Ko = true) :
    ProtocolChecks ps c i r anchor K Kc Ko := by
  unfold checkFiniteMultiAgentProtocol at h
  exact of_decide_eq_true h

section Checked

variable (ps : Fin 2 → Player k0 k nx m) (c : Shared k0 k nx m) (i : Fin 2) (r : Player k0 k nx m)
  (anchor : Fin 2 → Player k0 k nx m) (K Kc Ko : Fin (NJ k0 k nx) → Fin (NJ k0 k nx) → ℚ)

theorem players_ok (h : checkFiniteMultiAgentProtocol ps c i r anchor K Kc Ko = true) :
    ∀ j, (ps j).OK := by
  obtain ⟨h0, h1, -⟩ := checkFiniteMultiAgentProtocol_sound ps c i r anchor K Kc Ko h
  intro j; fin_cases j; exacts [h0, h1]

theorem shared_ok (h : checkFiniteMultiAgentProtocol ps c i r anchor K Kc Ko = true) : c.OK :=
  (checkFiniteMultiAgentProtocol_sound ps c i r anchor K Kc Ko h).2.2.1

theorem replacement_ok (h : checkFiniteMultiAgentProtocol ps c i r anchor K Kc Ko = true) : r.OK :=
  (checkFiniteMultiAgentProtocol_sound ps c i r anchor K Kc Ko h).2.2.2.1

theorem anchor_ok (h : checkFiniteMultiAgentProtocol ps c i r anchor K Kc Ko = true) :
    ∀ j, (anchor j).OK := by
  obtain ⟨-, -, -, -, ha0, ha1, -⟩ := checkFiniteMultiAgentProtocol_sound ps c i r anchor K Kc Ko h
  intro j; fin_cases j; exacts [ha0, ha1]

theorem encState_mk (s0 : Fin k0) (s : ∀ _ : Fin 2, Fin k) (x : Fin nx) :
    encState (((s0, s), x) : JS k0 k nx) =
      finProdFinEquiv (finProdFinEquiv (finProdFinEquiv (s0, s 0), s 1), x) := rfl

/-- **Protocol kernels.** The baseline, closed-loop and open-loop models have the
    declared rational joint rows. -/
theorem checked_protocol_kernels (hps : ∀ j, (ps j).OK) (hc : c.OK) (hr : r.OK)
    (ha : ∀ j, (anchor j).OK) (h : checkFiniteMultiAgentProtocol ps c i r anchor K Kc Ko = true) :
    (∀ y z : JS k0 k nx, ((generator ps hps c hc).toModel (world c hc)).inducedKernel y {z} =
      ENNReal.ofReal (K (encState y) (encState z))) ∧
    (∀ y z : JS k0 k nx, ((MeasurableProduct.closedLoop (generator ps hps c hc) i (mech r hr i)).toModel
      (world c hc)).inducedKernel y {z} = ENNReal.ofReal (Kc (encState y) (encState z))) ∧
    (∀ y z : JS k0 k nx, ((MeasurableProduct.openLoop (generator ps hps c hc) i (mech r hr i)
      (fun j => mech (anchor j) (ha j) j)).toModel (world c hc)).inducedKernel y {z} =
        ENNReal.ofReal (Ko (encState y) (encState z))) := by
  obtain ⟨-, -, -, -, -, -, hK, hKc, hKo⟩ := checkFiniteMultiAgentProtocol_sound ps c i r anchor K Kc Ko h
  refine ⟨fun y z => ?_, fun y z => ?_, fun y z => ?_⟩
  · rcases z with ⟨⟨s0, s⟩, x⟩
    rw [finite_protocol_induced_kernel, ← hK]
    rfl
  · rcases z with ⟨⟨s0, s⟩, x⟩
    rw [show MeasurableProduct.closedLoop (generator ps hps c hc) i (mech r hr i) =
      (generator ps hps c hc).closedLoop i (mech r hr i) from rfl, closedLoop_component,
      finite_protocol_induced_kernel, ← hKc]
    rfl
  · rcases z with ⟨⟨s0, s⟩, x⟩
    rw [show MeasurableProduct.openLoop (generator ps hps c hc) i (mech r hr i)
        (fun j => mech (anchor j) (ha j) j) =
      (generator ps hps c hc).openLoop i (mech r hr i) (fun j => mech (anchor j) (ha j) j) from rfl,
      openLoop_component, finite_protocol_induced_kernel, ← hKo]
    rfl

/-- **Marked path transport.** The compressed path law of the indexed model is
    the binary two-player model's path law, whose atoms are the same rows. -/
theorem checked_marked_path_transport (hps : ∀ j, (ps j).OK) (hc : c.OK) (hr : r.OK)
    (ha : ∀ j, (anchor j).OK) (h : checkFiniteMultiAgentProtocol ps c i r anchor K Kc Ko = true)
    (μ : Measure (JS k0 k nx)) [IsProbabilityMeasure μ] :
    (((generator ps hps c hc).toModel (world c hc)).pathLaw μ).map Two.compression.pathMap =
      ((Two.binary (generator ps hps c hc)).toModel (Two.physical (world c hc))).pathLaw
        (μ.map Two.state) ∧
    ∀ y z : JS k0 k nx,
      ((Two.binary (generator ps hps c hc)).toModel (Two.physical (world c hc))).inducedKernel
        (Two.state y) {Two.state z} = ENNReal.ofReal (K (encState y) (encState z)) := by
  refine ⟨Two.actual_pathLaw _ _ μ, fun y z => ?_⟩
  rw [Two.actual_atom]
  exact (checked_protocol_kernels ps c i r anchor K Kc Ko hps hc hr ha h).1 y z

/-- **Matched margins.** Research's closed-loop and open-loop margin closures
    for this protocol: the indexed protocols' margins for the pulled-back
    property equal the matched binary protocols' margins. -/
theorem checked_matched_original_margin (hps : ∀ j, (ps j).OK) (hc : c.OK) (hr : r.OK)
    (ha : ∀ j, (anchor j).OK) {H Hb Z : Type*} [MeasurableSpace H] [MeasurableSpace Hb]
    [MetricSpace Z]
    (spec : RegimeSpecification (JS k0 k nx) H)
    (specBar : RegimeSpecification (JointState (GameState (Fin k0) (Fin k) (Fin k)) (Fin nx)) Hb)
    (B₁ : RegimeSpecification.ConstitutiveComparisonSet
      (MeasurableProduct.model (generator ps hps c hc) (world c hc)) spec)
    (Bbar₁ : RegimeSpecification.ConstitutiveComparisonSet
      ((Two.binary (generator ps hps c hc)).toModel (Two.physical (world c hc))) specBar)
    (hB : Bbar₁.states = (MeasurableProduct.Two.compression_two (S0 := Fin k0) (S := SS k)
      (X := Fin nx)).stateMap '' B₁.states)
    (ψbar : RegimePropertyMap (JointState (GameState (Fin k0) (Fin k) (Fin k)) (Fin nx)) Z) :
    RegimeSpecification.constitutiveMargin (MeasurableProduct.model (generator ps hps c hc) (world c hc))
        spec (MeasurableProduct.protocolFamily (generator ps hps c hc) (world c hc) i (mech r hr i)
          {fun j => mech (anchor j) (ha j) j})
        (MeasurableProduct.Two.pullbackWholePathProperty
          (MeasurableProduct.Two.compression_two (S0 := Fin k0) (S := SS k) (X := Fin nx)) ψbar)
        B₁ (MeasurableProduct.closedLoopIntervention (generator ps hps c hc) (world c hc) i
          (mech r hr i) {fun j => mech (anchor j) (ha j) j}) =
      RegimeSpecification.constitutiveMargin
        ((Two.binary (generator ps hps c hc)).toModel (Two.physical (world c hc))) specBar
        (MeasurableProduct.Two.matchedBinaryFamily (generator ps hps c hc) (world c hc) i (mech r hr i)
          {fun j => mech (anchor j) (ha j) j}) ψbar Bbar₁
        (MeasurableProduct.Two.matchedBinaryClosed (generator ps hps c hc) (world c hc) i (mech r hr i)
          {fun j => mech (anchor j) (ha j) j}) ∧
    RegimeSpecification.constitutiveMargin (MeasurableProduct.model (generator ps hps c hc) (world c hc))
        spec (MeasurableProduct.protocolFamily (generator ps hps c hc) (world c hc) i (mech r hr i)
          {fun j => mech (anchor j) (ha j) j})
        (MeasurableProduct.Two.pullbackWholePathProperty
          (MeasurableProduct.Two.compression_two (S0 := Fin k0) (S := SS k) (X := Fin nx)) ψbar)
        B₁ (MeasurableProduct.openLoopIntervention (generator ps hps c hc) (world c hc) i
          (mech r hr i) {fun j => mech (anchor j) (ha j) j} (fun j => mech (anchor j) (ha j) j) rfl) =
      RegimeSpecification.constitutiveMargin
        ((Two.binary (generator ps hps c hc)).toModel (Two.physical (world c hc))) specBar
        (MeasurableProduct.Two.matchedBinaryFamily (generator ps hps c hc) (world c hc) i (mech r hr i)
          {fun j => mech (anchor j) (ha j) j}) ψbar Bbar₁
        (MeasurableProduct.Two.matchedBinaryOpen (generator ps hps c hc) (world c hc) i (mech r hr i)
          {fun j => mech (anchor j) (ha j) j} (fun j => mech (anchor j) (ha j) j) rfl) :=
  ⟨MeasurableProduct.Two.matched_closed_loop_original_margin _ _ i _ _ spec specBar B₁ Bbar₁ hB ψbar,
    MeasurableProduct.Two.matched_open_loop_original_margin _ _ i _ _ _ rfl spec specBar B₁ Bbar₁ hB ψbar⟩

end Checked

end PermanssonResearch.ApplicationBridge.MultiAgentReceipt
