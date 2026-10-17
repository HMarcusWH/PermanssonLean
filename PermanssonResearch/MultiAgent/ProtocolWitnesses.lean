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
player 1's last action (a reactive opponent, NOT strictly non-reactive:
`baselineOpponent_not_strict`). The declared replacement makes player 1 always
extract. Property `ψ`: the opponent's action taken at time 1 (recorded in `s₂` at
time 2) is "extract".

* **MA1** (`closedLoop_ne_openLoop`, STRICT family): against the strictly
  non-reactive "never extract" anchor, `Δ_CL = 1`, `Δ_OL = 0`, `A₁ = 1`.
  `protocols_separate_after_reachable_state` locates the separation: at `y₀` the
  CL opponent and the anchor play the same law; at the CL state at time 1, which
  is not on the baseline orbit, they differ.
* **Agreement** (`closedLoop_eq_openLoopExtract`, STRICT family): against the
  strictly non-reactive "always extract" anchor the two protocols give the same
  value. (`closedLoop_eq_openLoopWorld` is the same equality for a state-feedback
  anchor that reads `x`; it is NOT an opponent-locked protocol in the strict
  sense.)
* **MA2** (`anchors_agree_on_support_but_openLoop_differs`): the strict anchor
  `anchorConst` and the state-feedback anchor `anchorWorld` BOTH coincide with the
  baseline opponent (action and update kernels) at every baseline-reachable
  state, yet their OL values differ: baseline agreement does not identify the
  anchor off support.
* **MA3** (`correlated_generator_not_product`): a generator whose joint action
  law at some state equals the specific perfectly correlated law `correlatedLaw`
  on `Bool × Bool` is not the generator of any two-player conditional-product
  model. Correlation mediated by a shared `S₀` coordinate is NOT excluded.

All property values are computed exactly through `pathLaw_dirac_of_deterministic`
(frozen uniqueness), not by assumption.
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
/-- Strictly non-reactive anchor: never extract. -/
noncomputable def anchorConst : PlayerTwoMechanism Unit Bool Bool Bool Bool Bool := mech2 (fun _ => false)
/-- Strictly non-reactive anchor: always extract. -/
noncomputable def anchorExtract : PlayerTwoMechanism Unit Bool Bool Bool Bool Bool :=
  mech2 (fun _ => true)
/-- State-feedback anchor reading the world state `x` (NOT strictly non-reactive). -/
noncomputable def anchorWorld : PlayerTwoMechanism Unit Bool Bool Bool Bool Bool := mech2 xw
def anchors : Set (PlayerTwoMechanism Unit Bool Bool Bool Bool Bool) :=
  {anchorConst, anchorWorld, anchorExtract}

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

/-- Exact value of `ψ` from `y₀` for any product generator of the toy. -/
theorem gen_value (a1 a2 : Y → Bool) :
    ψ (pathProbability ((gen a1 a2).toModel world) (diracProba y0)) =
      if s2 (detOrbit (step a1 a2) y0 2) = true then 1 else 0 := by
  change ψ ⟨((gen a1 a2).toModel world).pathLaw (Measure.dirac y0), _⟩ = _
  simp only [gen_pathLaw]
  rw [ψ_dirac]

/-! ### Strict non-reactivity of the anchors -/

theorem dirac_false_ne_true : (Measure.dirac false : Measure Bool) ≠ Measure.dirac true := by
  intro h
  have h2 := congrArg (fun μ : Measure Bool => μ {true}) h
  simp at h2

theorem mech2_update_factors (act : Y → Bool) :
    ∃ ū : Kernel ((Unit × Bool) × Bool) Bool,
      (mech2 act).update = ū.comap anchorUpdateKey measurable_anchorUpdateKey :=
  ⟨detK (fun k : (Unit × Bool) × Bool => k.2), Kernel.ext fun u => by
    change detK (fun u : UI => u.1.2.2) u = _
    rw [detK_apply, Kernel.comap_apply, detK_apply]; rfl⟩

theorem const_anchor_strict (b : Bool) : IsStrictlyNonReactive (mech2 (fun _ => b)) :=
  ⟨⟨Kernel.const _ (Measure.dirac b), Kernel.ext fun y => by
      change detK (fun _ : Y => b) y = _
      rw [detK_apply, Kernel.comap_apply, Kernel.const_apply]⟩,
    mech2_update_factors _⟩

theorem anchorConst_strict : IsStrictlyNonReactive anchorConst := const_anchor_strict false
theorem anchorExtract_strict : IsStrictlyNonReactive anchorExtract := const_anchor_strict true

/-- Two states with the same `(s₀, s₂)` but different `s₁` and `x`. -/
theorem mech2_not_strict (act : Y → Bool) {y y' : Y} (hk : anchorKey y = anchorKey y')
    (hne : act y ≠ act y') : ¬ IsStrictlyNonReactive (mech2 act) := by
  intro h
  have := h.action_eq hk
  change detK act y = detK act y' at this
  rw [detK_apply, detK_apply] at this
  cases hy : act y <;> cases hy' : act y' <;> simp_all [dirac_false_ne_true,
    dirac_false_ne_true.symm]

theorem anchorWorld_not_strict : ¬ IsStrictlyNonReactive anchorWorld :=
  mech2_not_strict xw (y := (((), (false, false)), false)) (y' := (((), (false, false)), true))
    rfl (by decide)

theorem baselineOpponent_not_strict : ¬ IsStrictlyNonReactive baseline.player2 :=
  mech2_not_strict s1 (y := (((), (false, false)), false)) (y' := (((), (true, false)), false))
    rfl (by decide)

theorem anchorConst_mem_strict : anchorConst ∈ strictAnchors anchors :=
  ⟨by simp [anchors], anchorConst_strict⟩
theorem anchorExtract_mem_strict : anchorExtract ∈ strictAnchors anchors :=
  ⟨by simp [anchors], anchorExtract_strict⟩
theorem anchorWorld_not_mem_strict : anchorWorld ∉ strictAnchors anchors :=
  fun h => anchorWorld_not_strict h.2

/-! ### Interventions -/

noncomputable abbrev baselineModel : StrategicWorldModel (GameState Unit Bool Bool) Bool (Bool × Bool) :=
  baseline.toModel world

/-- Full menu (declared-kernel reading). -/
noncomputable abbrev family := protocolFamily baseline world extract anchors
/-- Strict menu (strictly non-reactive anchors only). -/
noncomputable abbrev strictFamily := protocolFamily baseline world extract (strictAnchors anchors)

noncomputable def JCL : AdmissibleStrategicIntervention family :=
  closedLoopIntervention baseline world extract anchors
noncomputable def JOLconst : AdmissibleStrategicIntervention family :=
  openLoopIntervention baseline world extract anchors anchorConst (by simp [anchors])
noncomputable def JOLworld : AdmissibleStrategicIntervention family :=
  openLoopIntervention baseline world extract anchors anchorWorld (by simp [anchors])

noncomputable def JCLs : AdmissibleStrategicIntervention strictFamily :=
  closedLoopIntervention baseline world extract (strictAnchors anchors)
noncomputable def JOLconsts : AdmissibleStrategicIntervention strictFamily :=
  openLoopIntervention baseline world extract (strictAnchors anchors) anchorConst
    anchorConst_mem_strict
noncomputable def JOLextracts : AdmissibleStrategicIntervention strictFamily :=
  openLoopIntervention baseline world extract (strictAnchors anchors) anchorExtract
    anchorExtract_mem_strict

/-! ### Exact values -/

theorem baseline_value : baselinePropertyValue ψ baselineModel y0 = 0 := by
  have h : s2 (detOrbit (step s1 s1) y0 2) = false := rfl
  exact (gen_value s1 s1).trans (by simp [h])

theorem cl_value : ψ (pathProbability ((gen (fun _ => true) s1).toModel world)
    (diracProba y0)) = 1 := by
  have h : s2 (detOrbit (step (fun _ => true) s1) y0 2) = true := rfl
  exact (gen_value _ _).trans (by simp [h])

theorem olConst_value : ψ (pathProbability ((gen (fun _ => true) (fun _ => false)).toModel world)
    (diracProba y0)) = 0 := by
  have h : s2 (detOrbit (step (fun _ => true) (fun _ => false)) y0 2) = false := rfl
  exact (gen_value _ _).trans (by simp [h])

theorem olExtract_value : ψ (pathProbability ((gen (fun _ => true) (fun _ => true)).toModel world)
    (diracProba y0)) = 1 := by
  have h : s2 (detOrbit (step (fun _ => true) (fun _ => true)) y0 2) = true := rfl
  exact (gen_value _ _).trans (by simp [h])

theorem olWorld_value : ψ (pathProbability ((gen (fun _ => true) xw).toModel world)
    (diracProba y0)) = 1 := by
  have h : s2 (detOrbit (step (fun _ => true) xw) y0 2) = true := rfl
  exact (gen_value _ _).trans (by simp [h])

theorem closedLoop_value : intervenedPropertyValue ψ JCL.intervention y0 = 1 := cl_value
theorem openLoopConst_value : intervenedPropertyValue ψ JOLconst.intervention y0 = 0 :=
  olConst_value
theorem openLoopWorld_value : intervenedPropertyValue ψ JOLworld.intervention y0 = 1 :=
  olWorld_value
theorem closedLoopStrict_value : intervenedPropertyValue ψ JCLs.intervention y0 = 1 := cl_value
theorem openLoopConstStrict_value : intervenedPropertyValue ψ JOLconsts.intervention y0 = 0 :=
  olConst_value
theorem openLoopExtractStrict_value :
    intervenedPropertyValue ψ JOLextracts.intervention y0 = 1 := olExtract_value

/-! ### MA1, locus, agreement, MA2 -/

/-- **MA1 (strict family).** Closed loop versus the strictly non-reactive
"never extract" anchor: `Δ_CL = 1`, `Δ_OL = 0`, `A = 1`. -/
theorem closedLoop_ne_openLoop :
    constitutiveEffect baselineModel ψ JCLs y0 = 1 ∧
      constitutiveEffect baselineModel ψ JOLconsts y0 = 0 ∧
      protocolGap ψ JCLs JOLconsts y0 = 1 := by
  unfold constitutiveEffect protocolGap
  rw [baseline_value, closedLoopStrict_value, openLoopConstStrict_value]
  norm_num [Real.dist_eq]

theorem baseline_orbit_const (t : ℕ) : detOrbit (step s1 s1) y0 t = y0 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [detOrbit_succ, ih]; rfl

/-- **MA1 locus.** At `y₀` the CL opponent (the baseline opponent, kept by
`closedLoop`) and the strict anchor play the same law; at the CL state at time 1
— which is NOT on the baseline orbit — they play different laws. -/
theorem protocols_separate_after_reachable_state :
    (baseline.closedLoop extract).player2.action y0 = anchorConst.action y0 ∧
      detOrbit (step (fun _ => true) s1) y0 1 ∉ Set.range (detOrbit (step s1 s1) y0) ∧
      (baseline.closedLoop extract).player2.action (detOrbit (step (fun _ => true) s1) y0 1) ≠
        anchorConst.action (detOrbit (step (fun _ => true) s1) y0 1) := by
  refine ⟨?_, ?_, ?_⟩
  · change detK s1 y0 = detK (fun _ : Y => false) y0
    rw [detK_apply, detK_apply]; rfl
  · rintro ⟨t, ht⟩
    rw [baseline_orbit_const] at ht
    have h2 : y0.2 = (detOrbit (step (fun _ => true) s1) y0 1).2 := congrArg Prod.snd ht
    exact absurd h2 (by decide)
  · change detK s1 _ ≠ detK (fun _ : Y => false) _
    rw [detK_apply, detK_apply]
    exact dirac_false_ne_true.symm

/-- **Agreement (strict family).** Against the strictly non-reactive "always
extract" anchor, CL and OL give the same value. -/
theorem closedLoop_eq_openLoopExtract : protocolGap ψ JCLs JOLextracts y0 = 0 := by
  unfold protocolGap
  rw [closedLoopStrict_value, openLoopExtractStrict_value, dist_self]

/-- Same equality for the STATE-FEEDBACK anchor `anchorWorld` (it reads `x`, which
equals player 1's last action, so it is not opponent-locked in the strict sense). -/
theorem closedLoop_eq_openLoopWorld : protocolGap ψ JCL JOLworld y0 = 0 := by
  unfold protocolGap
  rw [closedLoop_value, openLoopWorld_value, dist_self]

/-- **MA2.** The strict anchor `anchorConst` and the state-feedback anchor
`anchorWorld` both coincide with the BASELINE opponent — action kernels at every
baseline-reachable state from `y₀`, and update kernels everywhere — yet their OL
values differ: agreement with the baseline on baseline support does not identify
the anchor (or the OL protocol) off support. -/
theorem anchors_agree_on_support_but_openLoop_differs :
    (∀ t, anchorConst.action (detOrbit (step s1 s1) y0 t) =
        baseline.player2.action (detOrbit (step s1 s1) y0 t)) ∧
      (∀ t, anchorWorld.action (detOrbit (step s1 s1) y0 t) =
        baseline.player2.action (detOrbit (step s1 s1) y0 t)) ∧
      anchorConst.update = baseline.player2.update ∧
      anchorWorld.update = baseline.player2.update ∧
      IsStrictlyNonReactive anchorConst ∧ ¬ IsStrictlyNonReactive anchorWorld ∧
      intervenedPropertyValue ψ JOLconst.intervention y0 ≠
        intervenedPropertyValue ψ JOLworld.intervention y0 := by
  refine ⟨fun t => ?_, fun t => ?_, rfl, rfl, anchorConst_strict, anchorWorld_not_strict, ?_⟩
  · rw [baseline_orbit_const]
    change detK (fun _ : Y => false) y0 = detK s1 y0
    rw [detK_apply, detK_apply]; rfl
  · rw [baseline_orbit_const]
    change detK xw y0 = detK s1 y0
    rw [detK_apply, detK_apply]; rfl
  · rw [openLoopConst_value, openLoopWorld_value]; norm_num

end PermanssonResearch.MultiAgent.Witness

namespace PermanssonResearch.MultiAgent

set_option autoImplicit false
open PermanssonLean

/-! ### MA3: correlated actions are outside the product subclass -/

/-- The perfectly correlated joint action law `½ δ_(t,t) + ½ δ_(f,f)` on `Bool × Bool`. -/
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

/-- **MA3.** A generator whose joint action law at some state EQUALS `correlatedLaw`
is NOT the generator of any two-player conditional-product model. (Correlation
mediated by a shared `S₀` coordinate is representable and is not excluded.) -/
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
