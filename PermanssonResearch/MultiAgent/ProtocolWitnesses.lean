import PermanssonResearch.MultiAgent.AdaptationBound
import PermanssonResearch.StrategicWorld.DeterministicOrbit

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-!
# F1.4 — Protocol witnesses (MA1, agreement, MA2, MA3)

A typed two-player commons toy on `S = Unit × (Bool × Bool)`, `X = Bool`,
`A = Bool × Bool` (`true` = extract). Each player records its own last action;
the COMMON world kernel is `x' = a₁` (the resource is depleted iff player 1
extracted). Baseline: player 1 repeats its last action and the opponent COPIES
player 1's last action (a reactive opponent). The declared replacement makes
player 1 always extract. Property: the opponent extracts at time 2.

* **MA1** (`closedLoop_ne_openLoop`): `Δ_CL = 1`, `Δ_OL = 0`, `A₁ = 1` against
  the constant "never extract" anchor; the protocols separate only after the
  intervention-reachable state where player 1 has extracted.
* **Agreement** (`closedLoop_eq_openLoopWorld`): against the anchor that reads
  the world state the two protocols give the same value.
* **MA2** (`anchors_agree_on_support_but_openLoop_differs`): the two anchors have
  identical kernels at every baseline-reachable state, yet their OL values
  differ: baseline agreement does not identify the anchor off support.
* **MA3** (`correlated_generator_not_product`): a generator whose joint action
  law is perfectly correlated at some state is not the generator of ANY
  two-player conditional-product model.

All values are computed exactly through `pathLaw_dirac_of_deterministic` (frozen
uniqueness), not by assumption.
-/

namespace PermanssonResearch.MultiAgent.Witness

set_option autoImplicit false
open PermanssonLean PermanssonLean.RegimeSpecification
open PermanssonResearch.StrategicWorld PermanssonResearch.MultiAgent
open PermanssonResearch.MultiAgent.TwoPlayerGenerator

abbrev Y := JointState (GameState Unit Bool Bool) Bool
abbrev UI := UpdateInput (GameState Unit Bool Bool) Bool (Bool × Bool)
abbrev WI := WorldInput (GameState Unit Bool Bool) Bool (Bool × Bool)

noncomputable def detK {α β : Type} [MeasurableSpace α] [MeasurableSpace β] [Finite α]
    [MeasurableSingletonClass α] (f : α → β) : Kernel α β :=
  Kernel.deterministic f (measurable_of_finite f)

instance detK_isMarkov {α β : Type} [MeasurableSpace α] [MeasurableSpace β] [Finite α]
    [MeasurableSingletonClass α] (f : α → β) : IsMarkovKernel (detK f) := by
  unfold detK; infer_instance

theorem detK_apply {α β : Type} [MeasurableSpace α] [MeasurableSpace β] [Finite α]
    [MeasurableSingletonClass α] (f : α → β) (a : α) : detK f a = Measure.dirac (f a) :=
  Kernel.deterministic_apply _ _

/-- Treated player's private state (own last action). -/
def s1 (y : Y) : Bool := y.1.2.1
/-- Opponent's private state (own last action). -/
def s2 (y : Y) : Bool := y.1.2.2
/-- World state (resource extracted last period). -/
def xw (y : Y) : Bool := y.2

noncomputable def mech1 (act : Y → Bool) : PlayerOneMechanism Unit Bool Bool Bool Bool Bool :=
  ⟨detK act, detK (fun u : UI => u.1.2.1), inferInstance, inferInstance⟩
noncomputable def mech2 (act : Y → Bool) : PlayerTwoMechanism Unit Bool Bool Bool Bool Bool :=
  ⟨detK act, detK (fun u : UI => u.1.2.2), inferInstance, inferInstance⟩

/-- Product generator: player 1 acts by `a1`, player 2 by `a2`; both record
their own action; the common coordinate is trivial. -/
noncomputable def gen (a1 a2 : Y → Bool) : TwoPlayerGenerator Unit Bool Bool Bool Bool Bool :=
  ⟨mech1 a1, mech2 a2, detK (fun _ : UI => ()), inferInstance⟩

/-- COMMON world kernel for every protocol: `x' = a₁`. -/
noncomputable def world : Kernel WI Bool := detK (fun i : WI => i.2.1)

instance world_isMarkov : IsMarkovKernel world := by unfold world; infer_instance

/-- Baseline: player 1 repeats its last action; the opponent COPIES player 1's
last action (reactive). -/
noncomputable def baseline : TwoPlayerGenerator Unit Bool Bool Bool Bool Bool := gen s1 s1
noncomputable def extract : PlayerOneMechanism Unit Bool Bool Bool Bool Bool := mech1 (fun _ => true)
/-- Open-loop anchor: never extract (state independent). -/
noncomputable def anchorConst : PlayerTwoMechanism Unit Bool Bool Bool Bool Bool := mech2 (fun _ => false)
/-- Anchor reading the world state (agrees with `anchorConst` on baseline support). -/
noncomputable def anchorWorld : PlayerTwoMechanism Unit Bool Bool Bool Bool Bool := mech2 xw
def anchors : Set (PlayerTwoMechanism Unit Bool Bool Bool Bool Bool) := {anchorConst, anchorWorld}

def step (a1 a2 : Y → Bool) (y : Y) : Y := (((), (a1 y, a2 y)), a1 y)

theorem gen_inducedKernel (a1 a2 : Y → Bool) (y : Y) :
    ((gen a1 a2).toModel world).inducedKernel y = Measure.dirac (step a1 a2 y) := by
  apply inducedKernel_eq_dirac_of_deterministic _ (fun y => (a1 y, a2 y)) (fun i => i.2.1)
    (fun i => ((), (i.1.2.1, i.1.2.2)))
  · intro y
    change (detK a1 ×ₖ detK a2) y = _
    rw [Kernel.prod_apply, detK_apply, detK_apply, Measure.dirac_prod_dirac]
  · intro i; exact detK_apply _ i
  · intro i
    change (detK (fun _ : UI => ()) ×ₖ
      (detK (fun u : UI => u.1.2.1) ×ₖ detK (fun u : UI => u.1.2.2))) i = _
    rw [Kernel.prod_apply, Kernel.prod_apply, detK_apply, detK_apply, detK_apply,
      Measure.dirac_prod_dirac, Measure.dirac_prod_dirac]

theorem gen_pathLaw (a1 a2 : Y → Bool) (y : Y) :
    ((gen a1 a2).toModel world).pathLaw (Measure.dirac y) =
      Measure.dirac (detOrbit (step a1 a2) y) :=
  pathLaw_dirac_of_deterministic _ _ (gen_inducedKernel a1 a2) y

/-- Frozen full-path property: the opponent's recorded action at time 2 is
"extract" (`ψ(P) = P(s₂(Y₂) = true)`, metric `|·|`). -/
noncomputable def ψ : RegimePropertyMap Y ℝ :=
  fun law => (law.toMeasure {w : ℕ → Y | s2 (w 2) = true}).toReal

theorem ψ_dirac (w : ℕ → Y) :
    ψ ⟨Measure.dirac w, inferInstance⟩ = if s2 (w 2) = true then 1 else 0 := by
  have hm : MeasurableSet {w : ℕ → Y | s2 (w 2) = true} :=
    (measurableSet_singleton true).preimage
      ((measurable_of_finite s2).comp (measurable_pi_apply 2))
  change (Measure.dirac w {w : ℕ → Y | s2 (w 2) = true}).toReal = _
  rw [Measure.dirac_apply' _ hm]
  by_cases h : s2 (w 2) = true <;> simp [Set.indicator, h]

def y0 : Y := (((), (false, false)), false)

noncomputable abbrev baselineModel : StrategicWorldModel (GameState Unit Bool Bool) Bool (Bool × Bool) :=
  baseline.toModel world
noncomputable abbrev family := protocolFamily baseline world extract anchors
noncomputable def JCL : AdmissibleStrategicIntervention family :=
  closedLoopIntervention baseline world extract anchors
noncomputable def JOLconst : AdmissibleStrategicIntervention family :=
  openLoopIntervention baseline world extract anchors anchorConst (by simp [anchors])
noncomputable def JOLworld : AdmissibleStrategicIntervention family :=
  openLoopIntervention baseline world extract anchors anchorWorld (by simp [anchors])

theorem baseline_value : baselinePropertyValue ψ baselineModel y0 = 0 := by
  change ψ ⟨(gen s1 s1).toModel world |>.pathLaw (Measure.dirac y0), _⟩ = 0
  simp only [gen_pathLaw]
  have h : s2 (detOrbit (step s1 s1) y0 2) = false := rfl
  rw [ψ_dirac]; simp [h]

theorem closedLoop_value : intervenedPropertyValue ψ JCL.intervention y0 = 1 := by
  change ψ ⟨(gen (fun _ => true) s1).toModel world |>.pathLaw (Measure.dirac y0), _⟩ = 1
  simp only [gen_pathLaw]
  have h : s2 (detOrbit (step (fun _ => true) s1) y0 2) = true := rfl
  rw [ψ_dirac]; simp [h]

theorem openLoopConst_value : intervenedPropertyValue ψ JOLconst.intervention y0 = 0 := by
  change ψ ⟨(gen (fun _ => true) (fun _ => false)).toModel world |>.pathLaw
    (Measure.dirac y0), _⟩ = 0
  simp only [gen_pathLaw]
  have h : s2 (detOrbit (step (fun _ => true) (fun _ => false)) y0 2) = false := rfl
  rw [ψ_dirac]; simp [h]

theorem openLoopWorld_value : intervenedPropertyValue ψ JOLworld.intervention y0 = 1 := by
  change ψ ⟨(gen (fun _ => true) xw).toModel world |>.pathLaw (Measure.dirac y0), _⟩ = 1
  simp only [gen_pathLaw]
  have h : s2 (detOrbit (step (fun _ => true) xw) y0 2) = true := rfl
  rw [ψ_dirac]; simp [h]

/-- **MA1.** Closed loop and opponent-locked differ: `Δ_CL = 1`, `Δ_OL = 0`, gap `= 1`. -/
theorem closedLoop_ne_openLoop :
    constitutiveEffect baselineModel ψ JCL y0 = 1 ∧ constitutiveEffect baselineModel ψ JOLconst y0 = 0 ∧
      protocolGap ψ JCL JOLconst y0 = 1 := by
  unfold constitutiveEffect protocolGap
  rw [baseline_value, closedLoop_value, openLoopConst_value]
  norm_num [Real.dist_eq]

/-- **Agreement.** With the world-reading anchor, CL and OL coincide here. -/
theorem closedLoop_eq_openLoopWorld : protocolGap ψ JCL JOLworld y0 = 0 := by
  unfold protocolGap
  rw [closedLoop_value, openLoopWorld_value, dist_self]

theorem baseline_orbit_const (t : ℕ) : detOrbit (step s1 s1) y0 t = y0 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [detOrbit_succ, ih]; rfl

/-- **MA2.** The two anchors have IDENTICAL kernels at every baseline-reachable
state from `y0`, yet their opponent-locked protocol values differ: agreement on
baseline support does not identify the OL protocol off support. -/
theorem anchors_agree_on_support_but_openLoop_differs :
    (∀ t, anchorConst.action (detOrbit (step s1 s1) y0 t) =
        anchorWorld.action (detOrbit (step s1 s1) y0 t)) ∧
      anchorConst.update = anchorWorld.update ∧
      intervenedPropertyValue ψ JOLconst.intervention y0 ≠
        intervenedPropertyValue ψ JOLworld.intervention y0 := by
  refine ⟨fun t => ?_, rfl, ?_⟩
  · rw [baseline_orbit_const]
    change detK (fun _ : Y => false) y0 = detK xw y0
    rw [detK_apply, detK_apply]; rfl
  · rw [openLoopConst_value, openLoopWorld_value]; norm_num

end PermanssonResearch.MultiAgent.Witness

namespace PermanssonResearch.MultiAgent

set_option autoImplicit false
open PermanssonLean

/-! ### MA3: correlated actions are outside the product subclass -/

/-- Perfectly correlated joint action law on `Bool × Bool`. -/
noncomputable def correlatedLaw : Measure (Bool × Bool) :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac (true, true) + (2⁻¹ : ℝ≥0∞) • Measure.dirac (false, false)

instance correlatedLaw_isProbability : IsProbabilityMeasure correlatedLaw :=
  ⟨by simp [correlatedLaw, ENNReal.inv_two_add_inv_two]⟩

/-- `correlatedLaw` is not a product of ANY two (s-finite) marginal measures. -/
theorem correlatedLaw_ne_prod (ν₁ ν₂ : Measure Bool) [SFinite ν₂] :
    correlatedLaw ≠ ν₁.prod ν₂ := by
  intro h
  have key : ∀ a b : Bool, correlatedLaw {(a, b)} = ν₁ {a} * ν₂ {b} := by
    intro a b
    rw [h, ← Set.singleton_prod_singleton, Measure.prod_prod]
  have htt := key true true
  have hff := key false false
  have htf := key true false
  simp [correlatedLaw, Measure.dirac_apply'] at htt hff htf
  rcases htf with h1 | h2
  · rw [h1, zero_mul] at htt; simp at htt
  · rw [h2, mul_zero] at hff; simp at hff

/-- **MA3.** A generator whose joint action law at some state is perfectly
correlated is NOT the generator of any two-player conditional-product model. -/
theorem correlated_generator_not_product
    {S0 : Type*} {S1 : Type*} {S2 : Type*} {X : Type*}
    [MeasurableSpace S0] [MeasurableSpace S1] [MeasurableSpace S2] [MeasurableSpace X]
    (gen : StrategicGenerator (GameState S0 S1 S2) X (Bool × Bool))
    (y : JointState (GameState S0 S1 S2) X) (hy : gen.action y = correlatedLaw)
    (G : TwoPlayerGenerator S0 S1 S2 X Bool Bool) : G.toGenerator ≠ gen := by
  intro hG
  have := G.player2.action_isMarkov
  apply correlatedLaw_ne_prod (G.player1.action y) (G.player2.action y)
  rw [← hy, ← hG, TwoPlayerGenerator.toGenerator_action_apply]

end PermanssonResearch.MultiAgent
