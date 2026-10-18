import PermanssonResearch.MultiAgent.AutonomousAEMechanisms
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! A genuinely nonatomic initial common coordinate. The strict anchors differ
at the null key zero. Moving the initial law onto that key violates the stated
primitive premise and a treated recorder then separates the actual paths. -/

namespace PermanssonResearch.MultiAgent.Autonomous.ContinuumFixture

open MeasureTheory ProbabilityTheory Set PermanssonLean
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance : MeasurableSpace Bool := ⊤
local instance : DiscreteMeasurableSpace Bool := ⟨fun _ => trivial⟩

abbrev Y := State ℝ Bool Unit Unit
abbrev I := Input ℝ Bool Unit Unit Unit Bool

def signal (c : Bool) (q : ℝ × Unit) : Bool := by
  classical
  exact if q.1=0 then c else false

theorem measurable_signal (c : Bool) : Measurable (signal c) := by
  classical
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
    measurable_const measurable_const

def actionFactor (c : Bool) : Kernel (ℝ × Unit) Bool :=
  Kernel.deterministic (signal c) (measurable_signal c)

def anchor (c : Bool) : PlayerTwoMechanism ℝ Bool Unit Unit Unit Bool where
  action := (actionFactor c).comap anchorKey measurable_anchorKey
  update := Kernel.const I (Measure.dirac ())
  action_isMarkov := by unfold actionFactor; infer_instance
  update_isMarkov := inferInstance

def player (record : Bool) : PlayerOneMechanism ℝ Bool Unit Unit Unit Bool where
  action := Kernel.const Y (Measure.dirac ())
  update := Kernel.deterministic
    (fun i : I => if record then i.1.2.2 else false)
    (by cases record <;> fun_prop)
  action_isMarkov := inferInstance
  update_isMarkov := inferInstance

def game : TwoPlayerGenerator ℝ Bool Unit Unit Unit Bool where
  player1 := player false
  player2 := anchor false
  common := (Kernel.id : Kernel ℝ ℝ).comap commonUpdateKey measurable_commonUpdateKey
  common_isMarkov := inferInstance

def world : Kernel (WorldInput (GameState ℝ Bool Unit) Unit (Unit × Bool)) Unit :=
  Kernel.const _ (Measure.dirac ())

instance world_isMarkov : IsMarkovKernel world := by unfold world; infer_instance

def profile (c : Bool) : Profile game (anchor c) where
  common := Kernel.id
  action := actionFactor c
  update := Kernel.const _ (Measure.dirac ())
  common_eq := rfl
  action_eq := rfl
  update_eq := by ext i E hE; rfl

instance profile_common_isMarkov (c : Bool) : IsMarkovKernel (profile c).common := by
  change IsMarkovKernel (Kernel.id : Kernel ℝ ℝ)
  infer_instance

instance profile_action_isMarkov (c : Bool) : IsMarkovKernel (profile c).action := by
  change IsMarkovKernel (actionFactor c)
  unfold actionFactor
  infer_instance

instance profile_update_isMarkov (c : Bool) : IsMarkovKernel (profile c).update := by
  change IsMarkovKernel (Kernel.const ((ℝ × Unit) × Bool) (Measure.dirac ()))
  infer_instance

def initialState (s : ℝ) : Y := ((s,(false,())),())

theorem measurable_initialState : Measurable initialState := by unfold initialState; fun_prop

def commonLaw : Measure ℝ := volume.restrict (Icc 0 1)

instance commonLaw_isProbability : IsProbabilityMeasure commonLaw := by
  constructor
  norm_num [commonLaw,Real.volume_Icc]

instance commonLaw_nullSingleton : NullSingletonClass commonLaw := by
  unfold commonLaw
  infer_instance

def initialLaw : Measure Y := commonLaw.map initialState

instance initialLaw_isProbability : IsProbabilityMeasure initialLaw := by
  unfold initialLaw
  infer_instance

instance initialLaw_nullSingleton : NullSingletonClass initialLaw := by
  constructor
  intro y
  rw [initialLaw,Measure.map_apply measurable_initialState (measurableSet_singleton y)]
  apply measure_mono_null (t := {y.1.1}) _ (measure_singleton _)
  intro s hs
  have h : initialState s=y := Set.mem_singleton_iff.mp hs
  exact congrArg (fun z : Y => z.1.1) h

theorem initial_common_ne : ∀ᵐ y ∂initialLaw, y.1.1 ≠ 0 := by
  apply (ae_map_iff measurable_initialState.aemeasurable
    (measurableSet_eq_fun (measurable_fst.comp measurable_fst) measurable_const).compl).mpr
  exact commonLaw.ae_ne 0

def nextState (record c : Bool) (y : Y) : Y :=
  ((y.1.1,(if record then signal c (anchorKey y) else false,())),())

theorem actual_induced (record c : Bool) (y : Y) :
    ((game.openLoop (player record) (anchor c)).toModel world).inducedKernel y =
      Measure.dirac (nextState record c y) := by
  classical
  ext E hE
  rw [StrategicWorldModel.inducedKernel_apply _ _ hE]
  simp [TwoPlayerGenerator.toModel,TwoPlayerGenerator.toGenerator_action_apply,
    TwoPlayerGenerator.toGenerator_update_apply,TwoPlayerGenerator.openLoop,
    game,player,anchor,actionFactor,Kernel.deterministic_apply,Kernel.comap_apply,
    Kernel.id_apply,Kernel.prod_apply,Measure.dirac_prod_dirac,world,
    nextState,commonUpdateKey,Measure.dirac_apply',hE,Set.indicator]

theorem baseline_stationary : (game.toModel world).inducedKernel ∘ₘ initialLaw = initialLaw := by
  let f : Y → Y := fun y => initialState y.1.1
  have hf : Measurable f := measurable_initialState.comp (measurable_fst.comp measurable_fst)
  have hh : (game.toModel world).inducedKernel ∘ₘ initialLaw =
      Kernel.deterministic f hf ∘ₘ initialLaw := by
    apply Measure.comp_congr
    apply Filter.Eventually.of_forall
    intro y
    have h := actual_induced false false y
    change (game.toModel world).inducedKernel y = Measure.dirac (f y) at h
    simpa only [Kernel.deterministic_apply] using h
  rw [hh,Measure.deterministic_comp_eq_map hf,initialLaw,
    Measure.map_map hf measurable_initialState]
  rfl

theorem baseline_stateLaw (t : ℕ) : baselineStateLaw game world initialLaw t=initialLaw := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change (game.toModel world).inducedKernel ∘ₘ baselineStateLaw game world initialLaw t = _
      rw [ih,baseline_stationary]

theorem baseline_agreement :
    BaselineAEAgreement game (anchor false) (anchor true) world initialLaw := by
  constructor
  · intro t
    exact Filter.EventuallyEq.rfl
  · intro t
    rw [baseline_stateLaw]
    filter_upwards [initial_common_ne] with y hy
    simp [game,anchor,actionFactor,Kernel.deterministic_apply,signal,anchorKey,hy]
  · intro t
    exact Filter.EventuallyEq.rfl
  · intro t
    exact Filter.Eventually.of_forall (fun _ => rfl)

/-- Universal treated-law equality in an actual continuum model with a
nonatomic initial common law and genuinely distinct strict anchors. -/
theorem nonatomic_treated_pathLaw_eq
    (r : PlayerOneMechanism ℝ Bool Unit Unit Unit Bool) :
    ((game.openLoop r (anchor false)).toModel world).pathLaw initialLaw =
      ((game.openLoop r (anchor true)).toModel world).pathLaw initialLaw :=
  ae_anchors_pathLaw_eq (profile false) (profile true) world initialLaw baseline_agreement r

theorem anchors_differ_at_zero :
    (anchor false).action (initialState 0) ≠ (anchor true).action (initialState 0) := by
  intro h
  have hh := congrArg (fun μ : Measure Bool => μ {true}) h
  norm_num [anchor,actionFactor,signal,anchorKey,initialState,Kernel.deterministic_apply,
    Kernel.comap_apply] at hh

theorem point_start_violates_premise :
    ¬ BaselineAEAgreement game (anchor false) (anchor true) world
      (Measure.dirac (initialState 0)) := by
  intro h
  have hh := h.action_b 0
  have he : (anchor false).action (initialState 0)=(anchor true).action (initialState 0) := by
    simpa [baselineStateLaw,stateLaw,game,Filter.EventuallyEq] using hh
  exact anchors_differ_at_zero he

/-- The treated player records the realized opponent action. The exceptional
point now has full initial mass, and the actual original path laws separate. -/
theorem point_start_treated_pathLaw_ne :
    ((game.openLoop (player true) (anchor false)).toModel world).pathLaw
        (Measure.dirac (initialState 0)) ≠
      ((game.openLoop (player true) (anchor true)).toModel world).pathLaw
        (Measure.dirac (initialState 0)) := by
  intro h
  have hh := congrArg (fun μ : Measure (ℕ → Y) => μ.map (fun w => w 1)) h
  rw [actual_eval_succ _ _ 0,actual_eval_succ _ _ 0,
    actual_eval_zero,actual_eval_zero] at hh
  rw [Measure.dirac_bind (Kernel.measurable _),Measure.dirac_bind (Kernel.measurable _),
    actual_induced,actual_induced] at hh
  have he := congrArg (fun μ : Measure Y => μ {y | y.1.2.1=true}) hh
  have hE : MeasurableSet {y : Y | y.1.2.1=true} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  simp [nextState,signal,anchorKey,initialState,Measure.dirac_apply',hE] at he

end
end PermanssonResearch.MultiAgent.Autonomous.ContinuumFixture
