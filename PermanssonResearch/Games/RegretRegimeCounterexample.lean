import PermanssonResearch.Games.BimatrixRegret
import PermanssonResearch.Games.EquilibriumRegimeTransport
import PermanssonResearch.Perturbation.ProductActionError
import PermanssonResearch.ReverseSolver.InfiniteSafetyLeakage
import PermanssonResearch.X1.StrategyOriginalBridge
import PermanssonResearch.ConstitutiveQuasi.ComparisonTransport
import PermanssonLean.Regime.Persistence
import PermanssonLean.Regime.ConstitutiveMargin

/-! Two strategic counterexamples with fixed physical primitives. The
numerical survival recurrence and original typed path-law proofs are distinct.
No general GR or PR classification is asserted. -/
namespace PermanssonResearch.ApproxEquilibrium.Examples

open ActionTrace MeasureTheory ProbabilityTheory PermanssonLean
open PermanssonLean.RegimeSpecification PermanssonLean.ProbabilitySupport
open PermanssonResearch.Perturbation PermanssonResearch.ConstitutiveQuasi
open PermanssonResearch.DiscountedVerification
open scoped ENNReal BigOperators Topology
open Filter
set_option autoImplicit false

def dominant (a _b : Bool) : ℚ := if a then 0 else 1
def coordination (a b : Bool) : ℚ := if a = b then 1 else 0
def coinRow (e : ℚ) (a : Bool) : ℚ := if a then e else 1-e

theorem coinRow_simplex (e : ℚ) (h : 0 ≤ e ∧ e ≤ 1) : Simplex (coinRow e) := by
  constructor
  · intro b; cases b <;> simp [coinRow] <;> linarith [h.1, h.2]
  · simp [coinRow, PermanssonResearch.X1.sum_bool]

theorem coordination_two_exact :
    checkNash coordination coordination (coinRow 0) (coinRow 0) 0 = true ∧
    checkNash coordination coordination (coinRow 1) (coinRow 1) 0 = true := by
  decide +kernel

/-- The pure coordination equilibria are strictly Nash: the unique
other pure action loses one full payoff unit, for each player. -/
theorem coordination_strict_gaps :
    rationalGain coordination (coinRow 0) (coinRow 0) true = -1 ∧
    rationalGain coordination (coinRow 1) (coinRow 1) false = -1 := by
  decide +kernel

theorem dominant_regret_attained (e : ℚ) :
    rationalGain dominant (coinRow e) (coinRow 0) false = e ∧
    rationalGain dominant (coinRow 0) (coinRow e) false = 0 := by
  simp [rationalGain, rationalScore, dominant, coinRow, PermanssonResearch.X1.sum_bool] <;> ring

theorem dominant_approx (e : ℚ) (h : 0 ≤ e ∧ e ≤ 1) :
    NashChecks dominant dominant (coinRow e) (coinRow 0) e := by
  refine ⟨coinRow_simplex e h, coinRow_simplex 0 (by norm_num), h.1, ?_, ?_⟩
  · intro a
    cases a <;> simp [rationalGain, rationalScore, dominant, coinRow,
      PermanssonResearch.X1.sum_bool] <;> linarith [h.1, h.2]
  · intro a
    cases a <;> simp [rationalGain, rationalScore, dominant, coinRow,
      PermanssonResearch.X1.sum_bool] <;> linarith [h.1, h.2]

/-- With strictly dominant zero, an exact equilibrium must put mass one on zero. -/
theorem dominant_exact_unique (p q : Row Bool)
    (h : ApproxNash (fun a b => (dominant a b : ℝ))
      (fun a b => (dominant a b : ℝ)) p q 0) :
    p.mass true = 0 ∧ q.mass true = 0 := by
  have hs (r : Row Bool) (a : Bool) :
      score (fun a b => (dominant a b : ℝ)) r a = if a then 0 else 1 := by
    cases a <;> simp [score, dominant]
  have hp := (approxBestResponse_iff_pure _ _ _ _).1 h.2.1 false
  have hq := (approxBestResponse_iff_pure _ _ _ _).1 h.2.2 false
  unfold gain at hp hq
  simp [hs, Row.expect, PermanssonResearch.X1.sum_bool] at hp hq
  have ep := p.total
  have eq := q.total
  rw [PermanssonResearch.X1.sum_bool] at ep eq
  constructor <;> linarith [p.nonneg true, q.nonneg true]

abbrev State := JointState Unit (Fin 3)
abbrev Moves := Bool × Bool

/-- Both safe states remain distinct in the fixed comparison set. Exit is
absorbing; either player's action true causes exit. -/
def nextWorld (x : Fin 3) (a : Moves) : Fin 3 :=
  if a.1 || a.2 then 2 else x

noncomputable def physical : Kernel (WorldInput Unit (Fin 3) Moves) (Fin 3) :=
  Kernel.deterministic (fun w => nextWorld w.1.2 w.2) Measurable.of_discrete

noncomputable def update : Kernel (UpdateInput Unit (Fin 3) Moves) Unit :=
  Kernel.deterministic (fun _ => ()) measurable_const

noncomputable def action (e f : ℚ) : Kernel State Moves where
  toFun _ := (PermanssonResearch.X1.coin e).prod (PermanssonResearch.X1.coin f)
  measurable' := Measurable.of_discrete

noncomputable def generator (e f : ℚ) (he : 0 ≤ e ∧ e ≤ 1)
    (hf : 0 ≤ f ∧ f ≤ 1) : StrategicGenerator Unit (Fin 3) Moves where
  action := action e f
  update := update
  action_isMarkov := by
    refine ⟨fun y => ?_⟩
    haveI := PermanssonResearch.X1.coin_probability e he
    haveI := PermanssonResearch.X1.coin_probability f hf
    change IsProbabilityMeasure ((PermanssonResearch.X1.coin e).prod (PermanssonResearch.X1.coin f))
    infer_instance
  update_isMarkov := by unfold update; infer_instance

noncomputable def model (e f : ℚ) (he : 0 ≤ e ∧ e ≤ 1)
    (hf : 0 ≤ f ∧ f ≤ 1) : StrategicWorldModel Unit (Fin 3) Moves where
  generator := generator e f he hf
  world := physical
  world_isMarkov := by unfold physical; infer_instance

theorem same_world (e f e' f' : ℚ) (he : 0 ≤ e ∧ e ≤ 1)
    (hf : 0 ≤ f ∧ f ≤ 1) (he' : 0 ≤ e' ∧ e' ≤ 1)
    (hf' : 0 ≤ f' ∧ f' ≤ 1) :
    (model e f he hf).world = (model e' f' he' hf').world := rfl

theorem same_update (e f e' f' : ℚ) (he : 0 ≤ e ∧ e ≤ 1)
    (hf : 0 ≤ f ∧ f ≤ 1) (he' : 0 ≤ e' ∧ e' ≤ 1)
    (hf' : 0 ≤ f' ∧ f' ≤ 1) :
    (model e f he hf).generator.update =
      (model e' f' he' hf').generator.update := rfl

/-- Actual typed kernel evaluation, not a postulated matrix correspondence. -/
private theorem action_lintegral (e f : ℚ) (he : 0 ≤ e ∧ e ≤ 1)
    (hf : 0 ≤ f ∧ f ≤ 1) (y : State) (g : Moves → ℝ≥0∞) :
    (∫⁻ a, g a ∂action e f y) =
      ∑ a : Moves, ENNReal.ofReal (coinRow e a.1 : ℝ) *
        ENNReal.ofReal (coinRow f a.2 : ℝ) * g a := by
  haveI := PermanssonResearch.X1.coin_probability e he
  haveI := PermanssonResearch.X1.coin_probability f hf
  change (∫⁻ a, g a ∂(PermanssonResearch.X1.coin e).prod
    (PermanssonResearch.X1.coin f)) = _
  rw [MeasureTheory.lintegral_prod _ (Measurable.of_discrete.aemeasurable)]
  simp only [PermanssonResearch.X1.coin_lintegral]
  simp [Fintype.sum_prod_type, PermanssonResearch.X1.sum_bool, coinRow,
    mul_add, mul_assoc, add_comm, add_left_comm]

/-- Every atom is computed from the same ordered action/world/update law. -/
theorem actual_atom (e f : ℚ) (he : 0 ≤ e ∧ e ≤ 1) (hf : 0 ≤ f ∧ f ≤ 1)
    (y z : State) :
    (model e f he hf).inducedKernel y {z} =
      ∑ a : Moves, ENNReal.ofReal (coinRow e a.1 : ℝ) *
        ENNReal.ofReal (coinRow f a.2 : ℝ) *
          (if ((), nextWorld y.2 a) = z then 1 else 0) := by
  classical
  rw [StrategicWorldModel.inducedKernel_apply _ _ (measurableSet_singleton z)]
  change (∫⁻ a, ∫⁻ x, update ((y,a),x) {s | (s,x) ∈ ({z} : Set State)}
    ∂Measure.dirac (nextWorld y.2 a) ∂action e f y) = _
  rw [action_lintegral e f he hf]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  rw [lintegral_dirac]
  simp [update, Kernel.deterministic_apply, Measure.dirac_apply, Set.indicator]

def region : Set State := {y | y.2 ≠ 2}

noncomputable def specification : RegimeSpecification State Bool where
  region := region
  region_measurable := MeasurableSet.of_discrete
  basin := region
  basin_measurable := MeasurableSet.of_discrete
  basin_subset_region := fun _ h => h
  descriptor := fun y => decide (y.2 ≠ 2)
  descriptor_measurable := Measurable.of_discrete
  target := ⟨Measure.dirac true, inferInstance⟩
  convergenceMode := ConvergenceMode.almostSureWeak State Bool

noncomputable def comparison (e f : ℚ) (he : 0 ≤ e ∧ e ≤ 1)
    (hf : 0 ≤ f ∧ f ≤ 1) :
    RegimeSpecification.ConstitutiveComparisonSet (model e f he hf) specification where
  states := region
  states_measurable := MeasurableSet.of_discrete
  states_subset_basin := fun _ h => h
  pathLawNontrivial := by
    refine ⟨((),0), ?_, ((),1), ?_, ?_⟩
    · change (0 : Fin 3) ≠ 2
      decide
    · change (1 : Fin 3) ≠ 2
      decide
    · exact PermanssonResearch.ConstitutiveQuasi.pointStarted_pathLaw_ne_of_ne
        (model e f he hf) (by decide)

noncomputable def forcedExit : Kernel State Moves :=
  action 1 0


/-- Same named action-selection component, with the admissible replacement
frozen separately in each protocol. Rate one is the original forced exit. -/
noncomputable def familyAt (e f r : ℚ) (he : 0 ≤ e ∧ e ≤ 1) (hf : 0 ≤ f ∧ f ≤ 1) :
    InterventionFamily (model e f he hf) Unit where
  targetOf := fun _ => .actionSelection
  admissible := fun _ replacement => replacement.kernel = action r 0

noncomputable def interventionAt (e f r : ℚ) (he : 0 ≤ e ∧ e ≤ 1)
    (hf : 0 ≤ f ∧ f ≤ 1) (hr : 0 ≤ r ∧ r ≤ 1) :
    AdmissibleStrategicIntervention (familyAt e f r he hf) where
  intervention := ⟨(), ⟨action r 0, (generator r 0 hr (by norm_num)).action_isMarkov⟩⟩
  accepted := rfl
  strategic := InterventionTarget.isStrategic_actionSelection

noncomputable def family (e f : ℚ) (he : 0 ≤ e ∧ e ≤ 1) (hf : 0 ≤ f ∧ f ≤ 1) :=
  familyAt e f 1 he hf

noncomputable def intervention (e f : ℚ) (he : 0 ≤ e ∧ e ≤ 1) (hf : 0 ≤ f ∧ f ≤ 1) :
    AdmissibleStrategicIntervention (family e f he hf) :=
  interventionAt e f 1 he hf (by norm_num)

theorem intervened_eq_modelAt (e f r : ℚ) (he : 0 ≤ e ∧ e ≤ 1)
    (hf : 0 ≤ f ∧ f ≤ 1) (hr : 0 ≤ r ∧ r ≤ 1) :
    (interventionAt e f r he hf hr).intervention.apply = model r 0 hr (by norm_num) := by
  rfl

theorem intervention_world_fixed (e f : ℚ) (he : 0 ≤ e ∧ e ≤ 1)
    (hf : 0 ≤ f ∧ f ≤ 1) :
    (intervention e f he hf).intervention.apply.world = (model e f he hf).world :=
  (intervention e f he hf).world_eq

/-- Separate scalar recurrence for the declared independent leaking policy.
The actual atom theorem above identifies the one-step rows; the
all-horizon correspondence is given below by the killed-kernel recurrence. -/
noncomputable def survival (e : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => (1-e)*survival e n

theorem survival_eq_power (e : ℝ) (n : ℕ) : survival e n = (1-e)^n := by
  induction n with
  | zero => simp [survival]
  | succ n ih => simp [survival, ih, pow_succ, mul_comm]

theorem survival_limit (e : ℝ) (h0 : 0 < e) (h1 : e ≤ 1) :
    Filter.Tendsto (survival e) Filter.atTop (nhds 0) := by
  have hfun : survival e = (fun n : ℕ => (1-e)^n) := by
    funext n
    exact survival_eq_power e n
  rw [hfun]
  exact PermanssonResearch.ReverseSolver.InfiniteSafety.fixed_leakage_tends_to_zero e h0 h1

theorem sharp_finite_scalar :
    survival (1/10) 3 = (729/1000 : ℝ) ∧
      1-survival (1/10) 3 = (271/1000 : ℝ) := by
  norm_num [survival]

/-- The forced replacement uses the very same typed physical and update
primitives and the same action law as the literal exit model. -/
theorem intervened_eq_exit (e f : ℚ) (he : 0 ≤ e ∧ e ≤ 1) (hf : 0 ≤ f ∧ f ≤ 1) :
    (intervention e f he hf).intervention.apply = model 1 0 (by norm_num) (by norm_num) := by
  rfl

/-- Exact one-step retention on the entire declared safe region. -/
theorem actual_retention (e f : ℚ) (he : 0 ≤ e ∧ e ≤ 1) (hf : 0 ≤ f ∧ f ≤ 1)
    (y : State) (hy : y ∈ specification.region) :
    (model e f he hf).inducedKernel y specification.region =
      ENNReal.ofReal ((1-e : ℚ) : ℝ) * ENNReal.ofReal ((1-f : ℚ) : ℝ) := by
  classical
  have hy' : y.2 ≠ 2 := hy
  rw [StrategicWorldModel.inducedKernel_apply _ _ specification.region_measurable]
  change (∫⁻ a, ∫⁻ x, update ((y,a),x) {s | (s,x) ∈ specification.region}
    ∂Measure.dirac (nextWorld y.2 a) ∂action e f y) = _
  rw [action_lintegral e f he hf]
  simp [Fintype.sum_prod_type, PermanssonResearch.X1.sum_bool, coinRow,
    update, Kernel.deterministic_apply, Measure.dirac_apply, lintegral_dirac,
    specification, region, nextWorld, hy', Set.indicator]

/-- Retention recurrence on the actual original killed kernel, not merely a
matrix recurrence. Both safe starts and every horizon are quantified. -/
theorem actual_survival (e f : ℚ) (he : 0 ≤ e ∧ e ≤ 1) (hf : 0 ≤ f ∧ f ≤ 1)
    (y : State) (hy : y ∈ specification.region) (n : ℕ) :
    survivalProbability (model e f he hf) specification y n =
      (ENNReal.ofReal ((1-e : ℚ) : ℝ) * ENNReal.ofReal ((1-f : ℚ) : ℝ))^n := by
  rw [survivalProbability_eq_killedSurvivalMass _ _ n hy]
  let M := model e f he hf
  let r : ℝ≥0∞ := ENNReal.ofReal ((1-e : ℚ) : ℝ) * ENNReal.ofReal ((1-f : ℚ) : ℝ)
  change killedSurvivalMass M specification n y = r^n
  induction n with
  | zero => simp [killedSurvivalMass_zero M specification hy]
  | succ n ih =>
      rw [killedSurvivalMass_succ]
      have hae : (fun z => M.inducedKernel z specification.region) =ᵐ[
          ((killedKernel M specification)^n) y] (fun _ => r) :=
        (killedKernel_pow_ae_mem_region M specification n hy).mono
          (fun z hz => actual_retention e f he hf z hz)
      rw [lintegral_congr_ae hae, lintegral_const]
      have hmass : ((killedKernel M specification)^n) y Set.univ =
          ((killedKernel M specification)^n) y specification.region :=
        (ae_mem_iff_measure_eq specification.region_measurable.nullMeasurableSet).mp
          (killedKernel_pow_ae_mem_region M specification n hy) |>.symm
      calc
        r * ((killedKernel M specification)^n) y Set.univ =
            r * killedSurvivalMass M specification n y := by
          rw [hmass]
        _ = r * r^n := by rw [ih]
        _ = r^(n+1) := by rw [pow_succ, mul_comm]

/-- Exact equilibrium selects a retaining law; the other strict equilibrium
of the coordination game selects the absorbing exit law. -/
theorem forever_zero_zero (y : State) (hy : y ∈ specification.region) :
    survivalForeverProbability (model 0 0 (by norm_num) (by norm_num)) specification y = 1 := by
  apply exactInvariant_survivalForever _ _ _ hy
  intro z hz
  rw [actual_retention 0 0 (by norm_num) (by norm_num) z hz]
  norm_num

theorem forever_leak_zero (e : ℚ) (he : 0 < e ∧ e ≤ 1)
    (y : State) (hy : y ∈ specification.region) :
    survivalForeverProbability (model e 0 ⟨he.1.le,he.2⟩ (by norm_num)) specification y = 0 := by
  let M := model e 0 ⟨he.1.le,he.2⟩ (by norm_num)
  have hle (n : ℕ) : (survivalForeverProbability M specification y).toReal ≤
      (1-(e:ℝ))^n := by
    have h : survivalForeverProbability M specification y ≤ survivalProbability M specification y n :=
      measure_mono (survivesForeverSet_subset_survivesThroughSet specification n)
    have hr := ENNReal.toReal_mono (by unfold survivalProbability; finiteness) h
    rw [actual_survival e 0 ⟨he.1.le,he.2⟩ (by norm_num) y hy n] at hr
    have hn : 0 ≤ ((1-e : ℚ) : ℝ) := by exact_mod_cast sub_nonneg.mpr he.2
    simpa [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal hn] using hr
  have ht := PermanssonResearch.ReverseSolver.InfiniteSafety.fixed_leakage_tends_to_zero
    (e:ℝ) (by exact_mod_cast he.1) (by exact_mod_cast he.2)
  have hz : (survivalForeverProbability M specification y).toReal = 0 :=
    le_antisymm (ge_of_tendsto ht (Filter.Eventually.of_forall hle)) ENNReal.toReal_nonneg
  apply (ENNReal.toReal_eq_toReal_iff' (by unfold survivalForeverProbability; finiteness) (by norm_num)).1
  simpa using hz

theorem forever_coordination_exit (y : State) (hy : y ∈ specification.region) :
    survivalForeverProbability (model 1 1 (by norm_num) (by norm_num)) specification y = 0 := by
  apply le_antisymm _ bot_le
  calc
    _ ≤ survivalProbability (model 1 1 (by norm_num) (by norm_num)) specification y 1 :=
      measure_mono (survivesForeverSet_subset_survivesThroughSet specification 1)
    _ = 0 := by rw [actual_survival 1 1 (by norm_num) (by norm_num) y hy 1]; norm_num

/-- Frozen finite prefix survival as an original full-path property. -/

noncomputable def survivalPropertyAt (T : ℕ) : RegimePropertyMap State ℝ :=
  fun law => (law.toMeasure (survivesThroughSet specification T)).toReal

noncomputable def survivalProperty : RegimePropertyMap State ℝ :=
  survivalPropertyAt 3

/-- The SAME original survival observable, represented as a bounded prefix
score, with time zero included. This is equality as property maps, not just
equality of their values in the example. -/
noncomputable def survivalScore (T : ℕ) : FinitePathProperty State T where
  score := (prefixSurvivalSet specification T).indicator (fun _ => (1:ℝ))
  measurable_score := measurable_const.indicator (measurableSet_prefixSurvivalSet specification T)
  score_nonneg := by
    intro w
    by_cases hw : w ∈ prefixSurvivalSet specification T <;> simp [Set.indicator, hw]
  score_le_one := by
    intro w
    by_cases hw : w ∈ prefixSurvivalSet specification T <;> simp [Set.indicator, hw]

theorem survivalScore_property_eq (T : ℕ) :
    (survivalScore T).toRegimeProperty T = survivalPropertyAt T := by
  funext law
  unfold FinitePathProperty.toRegimeProperty survivalPropertyAt
  rw [survivesThroughSet_eq_preimage_prefix]
  change (∫ w, (prefixSurvivalSet specification T).indicator (fun _ => (1:ℝ))
      (Preorder.frestrictLe T w) ∂law.toMeasure) =
      (law.toMeasure (Preorder.frestrictLe T ⁻¹' prefixSurvivalSet specification T)).toReal
  have heq : (fun w : ℕ → State =>
        (prefixSurvivalSet specification T).indicator (fun _ => (1:ℝ))
          (Preorder.frestrictLe T w)) =
      (Preorder.frestrictLe T ⁻¹' prefixSurvivalSet specification T).indicator
        (fun _ => (1:ℝ)) := by
    funext w
    by_cases h : Preorder.frestrictLe T w ∈ prefixSurvivalSet specification T <;>
      simp [Set.indicator, h]
  rw [heq]
  exact integral_indicator_one
    ((measurableSet_prefixSurvivalSet specification T).preimage (Preorder.measurable_frestrictLe T))


theorem effect_survival (e : ℚ) (he : 0 ≤ e ∧ e ≤ 1)
    (y : State) (hy : y ∈ region) :
    constitutiveEffect (model e 0 he (by norm_num)) survivalProperty
      (intervention e 0 he (by norm_num)) y = (1-(e:ℝ))^3 := by
  unfold constitutiveEffect baselinePropertyValue intervenedPropertyValue survivalProperty survivalPropertyAt
  change dist (survivalProbability (model e 0 he (by norm_num)) specification y 3).toReal
    (survivalProbability (intervention e 0 he (by norm_num)).intervention.apply specification y 3).toReal = _
  rw [intervened_eq_exit, actual_survival e 0 he (by norm_num) y hy 3,
    actual_survival 1 0 (by norm_num) (by norm_num) y hy 3, Real.dist_eq]
  have hn : 0 ≤ ((1-e : ℚ) : ℝ) := by exact_mod_cast sub_nonneg.mpr he.2
  have hn' : 0 ≤ 1-(e:ℝ) := by exact_mod_cast sub_nonneg.mpr he.2
  simp [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal hn,
    abs_of_nonneg (pow_nonneg hn' 3)]

theorem actual_margin (e : ℚ) (he : 0 ≤ e ∧ e ≤ 1) :
    constitutiveMargin (model e 0 he (by norm_num)) specification (family e 0 he (by norm_num))
      survivalProperty (comparison e 0 he (by norm_num))
      (intervention e 0 he (by norm_num)) = (1-(e:ℝ))^3 := by
  have heq : constitutiveEffect (model e 0 he (by norm_num)) survivalProperty
      (intervention e 0 he (by norm_num)) '' (comparison e 0 he (by norm_num)).states =
      {((1-(e:ℝ))^3)} := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact Set.mem_singleton_iff.mpr (effect_survival e he y hy)
    · intro hx
      have hx' : x = (1-(e:ℝ))^3 := hx
      refine ⟨((),0), ?_, ?_⟩
      · change (0 : Fin 3) ≠ 2
        decide
      · rw [effect_survival e he ((),0) (by change (0 : Fin 3) ≠ 2; decide), hx']
  rw [constitutiveMargin, heq, csInf_singleton]

theorem actual_sharp_margins :
    constitutiveMargin (model 0 0 (by norm_num) (by norm_num)) specification
      (family 0 0 (by norm_num) (by norm_num)) survivalProperty
      (comparison 0 0 (by norm_num) (by norm_num)) (intervention 0 0 (by norm_num) (by norm_num)) = 1 ∧
    constitutiveMargin (model (1/10) 0 (by norm_num) (by norm_num)) specification
      (family (1/10) 0 (by norm_num) (by norm_num)) survivalProperty
      (comparison (1/10) 0 (by norm_num) (by norm_num))
      (intervention (1/10) 0 (by norm_num) (by norm_num)) = (729/1000 : ℝ) := by
  rw [actual_margin 0 (by norm_num), actual_margin (1/10) (by norm_num)]
  norm_num


/-- Exact margin of an arbitrary registered exit-rate replacement on the
same two safe starts. The horizon remains fixed before evaluation. -/
theorem effect_at (e r : ℚ) (he : 0 ≤ e ∧ e ≤ 1) (hr : 0 ≤ r ∧ r ≤ 1)
    (T : ℕ) (y : State) (hy : y ∈ region) :
    constitutiveEffect (model e 0 he (by norm_num)) (survivalPropertyAt T)
      (interventionAt e 0 r he (by norm_num) hr) y =
      |(1-(e:ℝ))^T-(1-(r:ℝ))^T| := by
  unfold constitutiveEffect baselinePropertyValue intervenedPropertyValue survivalPropertyAt
  change dist (survivalProbability (model e 0 he (by norm_num)) specification y T).toReal
    (survivalProbability (interventionAt e 0 r he (by norm_num) hr).intervention.apply
      specification y T).toReal = _
  rw [intervened_eq_modelAt, actual_survival e 0 he (by norm_num) y hy T,
    actual_survival r 0 hr (by norm_num) y hy T, Real.dist_eq]
  have he' : 0 ≤ ((1-e : ℚ) : ℝ) := by exact_mod_cast sub_nonneg.mpr he.2
  have hr' : 0 ≤ ((1-r : ℚ) : ℝ) := by exact_mod_cast sub_nonneg.mpr hr.2
  simp [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal he',
    ENNReal.toReal_ofReal hr']

theorem margin_at (e r : ℚ) (he : 0 ≤ e ∧ e ≤ 1) (hr : 0 ≤ r ∧ r ≤ 1) (T : ℕ) :
    constitutiveMargin (model e 0 he (by norm_num)) specification
      (familyAt e 0 r he (by norm_num)) (survivalPropertyAt T)
      (comparison e 0 he (by norm_num)) (interventionAt e 0 r he (by norm_num) hr) =
      |(1-(e:ℝ))^T-(1-(r:ℝ))^T| := by
  have heq : constitutiveEffect (model e 0 he (by norm_num)) (survivalPropertyAt T)
      (interventionAt e 0 r he (by norm_num) hr) '' (comparison e 0 he (by norm_num)).states =
      { |(1-(e:ℝ))^T-(1-(r:ℝ))^T| } := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact Set.mem_singleton_iff.mpr (effect_at e r he hr T y hy)
    · intro hx
      have hx' : x = |(1-(e:ℝ))^T-(1-(r:ℝ))^T| := hx
      refine ⟨((),0), ?_, ?_⟩
      · change (0 : Fin 3) ≠ 2
        decide
      · rw [effect_at e r he hr T ((),0) (by change (0 : Fin 3) ≠ 2; decide), hx']
  rw [constitutiveMargin, heq, csInf_singleton]

theorem boolean_rowTV (e r : ℚ) (he : 0 ≤ e ∧ e ≤ 1) (hr : 0 ≤ r ∧ r ≤ 1) :
    rowTV (PermanssonResearch.X1.booleanRow e he) (PermanssonResearch.X1.booleanRow r hr) =
      |(e:ℝ)-(r:ℝ)| := by
  rw [rowTV_half_l1, PermanssonResearch.X1.sum_bool]
  simp only [PermanssonResearch.X1.booleanRow, PermanssonResearch.X1.boolMass,
    Bool.false_eq_true, ↓reduceIte]
  push_cast
  rw [show 1-(e:ℝ)-(1-(r:ℝ)) = (r:ℝ)-(e:ℝ) by ring,
    abs_sub_comm (r:ℝ) (e:ℝ)]
  ring

/-- The product-row theorem is applied to the actual alpha of the model.
This proves the discrepancy globally, including the absorbing exit state. -/
theorem action_error (e r : ℚ) (he : 0 ≤ e ∧ e ≤ 1) (hr : 0 ≤ r ∧ r ≤ 1) :
    HasUniformEventTVBound (action e 0) (action r 0) |(e:ℝ)-(r:ℝ)| := by
  apply uniform_product_action_tv (action e 0) (action r 0)
    (fun _ => PermanssonResearch.X1.booleanRow e he)
    (fun _ => PermanssonResearch.X1.booleanRow r hr)
    (fun _ => PermanssonResearch.X1.booleanRow 0 (by norm_num))
    (fun _ => PermanssonResearch.X1.booleanRow 0 (by norm_num))
  · intro y
    rw [PermanssonResearch.X1.booleanRow_measure_eq_coin,
      PermanssonResearch.X1.booleanRow_measure_eq_coin]
    rfl
  · intro y
    rw [PermanssonResearch.X1.booleanRow_measure_eq_coin,
      PermanssonResearch.X1.booleanRow_measure_eq_coin]
    rfl
  · intro y
    rw [boolean_rowTV, boolean_rowTV]
    simp

noncomputable def pairAt (e r e' r' : ℚ)
    (he : 0 ≤ e ∧ e ≤ 1) (hr : 0 ≤ r ∧ r ≤ 1)
    (he' : 0 ≤ e' ∧ e' ≤ 1) (hr' : 0 ≤ r' ∧ r' ≤ 1) :
    PrimitiveModelPair (model e 0 he (by norm_num)) (familyAt e 0 r he (by norm_num))
      (interventionAt e 0 r he (by norm_num) hr) where
  approximate := model e' 0 he' (by norm_num)
  approximateFamily := familyAt e' 0 r' he' (by norm_num)
  approximateIntervention := interventionAt e' 0 r' he' (by norm_num) hr'
  component_eq := rfl
  target_eq := rfl

theorem rate_error_le_one (e r : ℚ) (he : 0 ≤ e ∧ e ≤ 1) (hr : 0 ≤ r ∧ r ≤ 1) :
    |(e:ℝ)-(r:ℝ)| ≤ 1 := by
  have he0 : 0 ≤ (e:ℝ) := by exact_mod_cast he.1
  have he1 : (e:ℝ) ≤ 1 := by exact_mod_cast he.2
  have hr0 : 0 ≤ (r:ℝ) := by exact_mod_cast hr.1
  have hr1 : (r:ℝ) ≤ 1 := by exact_mod_cast hr.2
  rw [abs_le]
  constructor <;> linarith

/-- Both typed error records are constructed from the same actual action
laws used in the survival computation. P and U are literally unchanged. -/
noncomputable def protocolErrorsAt (e r e' r' : ℚ)
    (he : 0 ≤ e ∧ e ≤ 1) (hr : 0 ≤ r ∧ r ≤ 1)
    (he' : 0 ≤ e' ∧ e' ≤ 1) (hr' : 0 ≤ r' ∧ r' ≤ 1) :
    PrimitiveProtocolErrors _ _ _ (pairAt e r e' r' he hr he' hr') where
  baseline := fixedWorldUpdateBudget _ _ |(e:ℝ)-(e':ℝ)| (abs_nonneg _)
    (rate_error_le_one e e' he he') (action_error e e' he he') rfl rfl
  intervention := by
    change PrimitiveErrorBounds (model r 0 hr (by norm_num))
      (model r' 0 hr' (by norm_num))
    exact fixedWorldUpdateBudget _ _ |(r:ℝ)-(r':ℝ)| (abs_nonneg _)
      (rate_error_le_one r r' hr hr') (action_error r r' hr hr') rfl rfl

/-- Read only the numeric fields of the constructed baseline budget. -/
theorem baseline_budget_at (e r e' r' : ℚ)
    (he : 0 ≤ e ∧ e ≤ 1) (hr : 0 ≤ r ∧ r ≤ 1)
    (he' : 0 ≤ e' ∧ e' ≤ 1) (hr' : 0 ≤ r' ∧ r' ≤ 1) (T : ℕ) :
    (protocolErrorsAt e r e' r' he hr he' hr').baselineProductPrefixBudget T =
      geometricTVEnvelope |(e:ℝ)-(e':ℝ)| T := by
  change geometricTVEnvelope
    (1-(1-|(e:ℝ)-(e':ℝ)|)*(1-0)*(1-0)) T = _
  congr 1
  ring

/-- Read only the numeric fields of the separately constructed intervention budget. -/
theorem intervention_budget_at (e r e' r' : ℚ)
    (he : 0 ≤ e ∧ e ≤ 1) (hr : 0 ≤ r ∧ r ≤ 1)
    (he' : 0 ≤ e' ∧ e' ≤ 1) (hr' : 0 ≤ r' ∧ r' ≤ 1) (T : ℕ) :
    (protocolErrorsAt e r e' r' he hr he' hr').interventionProductPrefixBudget T =
      geometricTVEnvelope |(r:ℝ)-(r':ℝ)| T := by
  change geometricTVEnvelope
    (1-(1-|(r:ℝ)-(r':ℝ)|)*(1-0)*(1-0)) T = _
  congr 1
  ring

/-- A typed original-margin theorem, before evaluating either margin to a
scalar. The proof consumes the actual primitive records and the general
product-error theorem on the unchanged comparison domain. -/
theorem original_margin_transport (e r e' r' : ℚ)
    (he : 0 ≤ e ∧ e ≤ 1) (hr : 0 ≤ r ∧ r ≤ 1)
    (he' : 0 ≤ e' ∧ e' ≤ 1) (hr' : 0 ≤ r' ∧ r' ≤ 1) (T : ℕ) :
    |constitutiveMargin (model e' 0 he' (by norm_num)) specification
        (familyAt e' 0 r' he' (by norm_num)) (survivalPropertyAt T)
        (comparison e' 0 he' (by norm_num))
        (interventionAt e' 0 r' he' (by norm_num) hr') -
      constitutiveMargin (model e 0 he (by norm_num)) specification
        (familyAt e 0 r he (by norm_num)) (survivalPropertyAt T)
        (comparison e 0 he (by norm_num))
        (interventionAt e 0 r he (by norm_num) hr)| ≤
      geometricTVEnvelope |(e:ℝ)-(e':ℝ)| T +
        geometricTVEnvelope |(r:ℝ)-(r':ℝ)| T := by
  let pair := pairAt e r e' r' he hr he' hr'
  let bounds := protocolErrorsAt e r e' r' he hr he' hr'
  have h := primitive_product_constitutiveMargin_abs_le
    (spec := specification) (B₁ := comparison e 0 he (by norm_num)) bounds T (survivalScore T)
  rw [survivalScore_property_eq] at h
  have hset : pair.comparisonSet specification (comparison e 0 he (by norm_num)) =
      comparison e' 0 he' (by norm_num) := rfl
  change |constitutiveMargin (model e' 0 he' (by norm_num)) specification
      (familyAt e' 0 r' he' (by norm_num)) (survivalPropertyAt T)
      (pair.comparisonSet specification (comparison e 0 he (by norm_num)))
      (interventionAt e' 0 r' he' (by norm_num) hr') -
      constitutiveMargin (model e 0 he (by norm_num)) specification
      (familyAt e 0 r he (by norm_num)) (survivalPropertyAt T)
      (comparison e 0 he (by norm_num))
      (interventionAt e 0 r he (by norm_num) hr)| ≤
    (protocolErrorsAt e r e' r' he hr he' hr').baselineProductPrefixBudget T +
    (protocolErrorsAt e r e' r' he hr he' hr').interventionProductPrefixBudget T at h
  rw [hset, baseline_budget_at, intervention_budget_at] at h
  exact h

/-- Scalar specialization of the actual original-margin theorem. -/
theorem transport_instance (e r e' r' : ℚ)
    (he : 0 ≤ e ∧ e ≤ 1) (hr : 0 ≤ r ∧ r ≤ 1)
    (he' : 0 ≤ e' ∧ e' ≤ 1) (hr' : 0 ≤ r' ∧ r' ≤ 1) (T : ℕ) :
    | |(1-(e':ℝ))^T-(1-(r':ℝ))^T| -
        |(1-(e:ℝ))^T-(1-(r:ℝ))^T| | ≤
      geometricTVEnvelope |(e:ℝ)-(e':ℝ)| T +
      geometricTVEnvelope |(r:ℝ)-(r':ℝ)| T := by
  have h := original_margin_transport e r e' r' he hr he' hr' T
  rw [margin_at, margin_at] at h
  exact h

/-- For the strictly dominant candidate the attaining pure-action gain is
exactly e. Its actual action kernel is within that amount of the exact
equilibrium's action kernel. This conclusion is specific to the declared
family and does not assert a general regret-to-joint-equilibrium bound. -/
theorem dominant_regret_action_error (e : ℚ) (he : 0 ≤ e ∧ e ≤ 1) :
    HasUniformEventTVBound (action 0 0) (action e 0)
      (rationalGain dominant (coinRow e) (coinRow 0) false : ℝ) := by
  rw [(dominant_regret_attained e).1]
  have h := action_error 0 e (by norm_num) he
  have he0 : 0 ≤ (e:ℝ) := by exact_mod_cast he.1
  simpa [abs_of_nonneg he0] using h

/-- The actual margin at the registered equilibrium and approximate
dominant profile is transported using the attained regret itself. The
intervention is literally identical, so its error is zero. -/
theorem dominant_original_margin_transport (e : ℚ) (he : 0 ≤ e ∧ e ≤ 1) :
    |constitutiveMargin (model e 0 he (by norm_num)) specification
        (family e 0 he (by norm_num)) survivalProperty
        (comparison e 0 he (by norm_num)) (intervention e 0 he (by norm_num)) -
      constitutiveMargin (model 0 0 (by norm_num) (by norm_num)) specification
        (family 0 0 (by norm_num) (by norm_num)) survivalProperty
        (comparison 0 0 (by norm_num) (by norm_num)) (intervention 0 0 (by norm_num) (by norm_num))| ≤
      geometricTVEnvelope (rationalGain dominant (coinRow e) (coinRow 0) false : ℝ) 3 := by
  have h := original_margin_transport 0 1 e 1 (by norm_num) (by norm_num) he (by norm_num) 3
  have he0 : 0 ≤ (e:ℝ) := by exact_mod_cast he.1
  rw [(dominant_regret_attained e).1]
  have hbudget :
      geometricTVEnvelope |((0:ℚ):ℝ)-(e:ℝ)| 3 +
        geometricTVEnvelope |((1:ℚ):ℝ)-((1:ℚ):ℝ)| 3 =
        geometricTVEnvelope (e:ℝ) 3 := by
    simp [geometricTVEnvelope, abs_of_nonneg he0]
  rw [hbudget] at h
  exact h

theorem sharp_transport_from_general :
    | |(1-(1/10:ℝ))^3-(1-(1:ℝ))^3| -
        |(1-(0:ℝ))^3-(1-(1:ℝ))^3| | ≤
      geometricTVEnvelope (1/10) 3 + geometricTVEnvelope 0 3 := by
  have h := transport_instance 0 1 (1/10) 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 3
  norm_num at h ⊢ <;> exact h

/-- Both actual protocol errors can be nonzero. At one transition the
margin loss is 1/5, with budgets 1/10 on each side; either alone is false. -/
theorem both_budgets_necessary :
    | |(1-(1/10:ℝ))-(1-(9/10:ℝ))| - |(1-(0:ℝ))-(1-(1:ℝ))| | ≤
      geometricTVEnvelope (1/10) 1 + geometricTVEnvelope (1/10) 1 ∧
    ¬ (| |(1-(1/10:ℝ))-(1-(9/10:ℝ))| - |(1-(0:ℝ))-(1-(1:ℝ))| | ≤
      geometricTVEnvelope (1/10) 1) := by
  constructor
  · have h := transport_instance 0 1 (1/10) (9/10) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) 1
    norm_num at h ⊢ <;> exact h
  · norm_num

/-- The exit rule is symmetric in the two action coordinates. -/
theorem nextWorld_swap (x : Fin 3) (a b : Bool) :
    nextWorld x (a,b) = nextWorld x (b,a) := by
  cases a <;> cases b <;> rfl

/-- State-independent rewards on the chronological own-action-first trace.
The symmetric exit rule agrees with the global physical law also for
player two. This identifies the erased state law, not a globally ordered
action-retaining trace. Rates e and f below are in own/opponent order;
for player two the corresponding global rates are f and e. -/
noncomputable def traceGame (u : Bool → Bool → ℝ) (i : Fin 2)
    (op : Row Bool) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) : Game State Bool where
  player := i
  physical y a b := Row.pure ((), nextWorld y.2 (a,b))
  opponent _ := op
  reward _ a b := u a b
  discount := β
  discount_nonneg := hβ0
  discount_lt_one := hβ1

/-- Exact atom correspondence of the controlled trace to the actual alpha,
P and U. This is not an independently postulated transition matrix. -/
theorem trace_stateStep_actual (u : Bool → Bool → ℝ) (i : Fin 2)
    (e f : ℚ) (he : 0 ≤ e ∧ e ≤ 1) (hf : 0 ≤ f ∧ f ≤ 1)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (y : State) :
    (stateStep (traceGame u i (PermanssonResearch.X1.booleanRow f hf) β hβ0 hβ1)
      (fun _ => PermanssonResearch.X1.booleanRow e he) y).measure =
      (model e f he hf).inducedKernel y := by
  classical
  apply Measure.ext_of_singleton
  intro z
  rw [Row.measure_singleton, actual_atom]
  have hm : (stateStep (traceGame u i (PermanssonResearch.X1.booleanRow f hf) β hβ0 hβ1)
      (fun _ => PermanssonResearch.X1.booleanRow e he) y).mass z =
      ∑ a : Moves, (coinRow e a.1 : ℝ)*(coinRow f a.2 : ℝ)*
        (if ((),nextWorld y.2 a)=z then 1 else 0) := by
    simp only [stateStep, traceGame, PermanssonResearch.X1.strategy_bind_mass,
      PermanssonResearch.X1.booleanRow, Row.pure, Fintype.sum_prod_type,
      coinRow, PermanssonResearch.X1.boolMass, Finset.mul_sum, mul_assoc]
  rw [hm, ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro a _
    have h₁ : 0 ≤ (coinRow e a.1 : ℝ) :=
      (PermanssonResearch.X1.booleanRow e he).nonneg a.1
    have h₂ : 0 ≤ (coinRow f a.2 : ℝ) :=
      (PermanssonResearch.X1.booleanRow f hf).nonneg a.2
    rw [ENNReal.ofReal_mul (mul_nonneg h₁ h₂), ENNReal.ofReal_mul h₁]
    split_ifs <;> simp
  · intro a _
    have h₁ : 0 ≤ (coinRow e a.1 : ℝ) :=
      (PermanssonResearch.X1.booleanRow e he).nonneg a.1
    have h₂ : 0 ≤ (coinRow f a.2 : ℝ) :=
      (PermanssonResearch.X1.booleanRow f hf).nonneg a.2
    exact mul_nonneg (mul_nonneg h₁ h₂) (by split_ifs <;> norm_num)

theorem trace_stateLaw_actual (u : Bool → Bool → ℝ) (i : Fin 2)
    (e f : ℚ) (he : 0 ≤ e ∧ e ≤ 1) (hf : 0 ≤ f ∧ f ≤ 1)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (μ : Row State) :
    (canonicalLaw (traceGame u i (PermanssonResearch.X1.booleanRow f hf) β hβ0 hβ1)
      (markovBehavior (fun _ => PermanssonResearch.X1.booleanRow e he)) μ).map statePath =
      (model e f he hf).pathLaw μ.measure :=
  canonical_state_erasure_eq_original _ _ _ _
    (trace_stateStep_actual u i e f he hf β hβ0 hβ1)

/-- Dominant-action game: exact discounted loss, including every
nonanticipating behavioral deviation in the same fixed-opponent game. -/
theorem dominant_discounted_exact (e f : ℚ) (he : 0 ≤ e ∧ e ≤ 1)
    (hf : 0 ≤ f ∧ f ≤ 1) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (i : Fin 2) (μ : Row State) :
    let G := traceGame (fun a b => (dominant a b : ℝ)) i
      (PermanssonResearch.X1.booleanRow f hf) β hβ0 hβ1
    let π := markovBehavior (fun _ : State => PermanssonResearch.X1.booleanRow e he)
    (∀ σ : BehavioralPolicy State Bool,
      payoff G σ μ - payoff G π μ ≤ (e:ℝ)/(1-β)) ∧
      (∃ σ : BehavioralPolicy State Bool,
        payoff G σ μ - payoff G π μ = (e:ℝ)/(1-β)) := by
  dsimp only
  let G := traceGame (fun a b => (dominant a b : ℝ)) i
    (PermanssonResearch.X1.booleanRow f hf) β hβ0 hβ1
  have hd : 1-β ≠ 0 := ne_of_gt (sub_pos.mpr hβ1)
  have hR : ∀ y a b, |G.reward y a b| ≤ (1:ℝ) := by
    intro y a b
    cases a <;> norm_num [G, traceGame, dominant]
  have hQ (c : ℝ) (y : State) (a : Bool) :
      Q G (fun _ => c) y a = (if a then 0 else 1)+β*c := by
    cases a <;> simp [Q, G, traceGame, dominant]
  have hfix (p : ℚ) :
      1-(p:ℝ)+β*((1-(p:ℝ))/(1-β)) = (1-(p:ℝ))/(1-β) := by
    field_simp [hd] <;> ring
  have hvalue (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) :
      payoff G (markovBehavior (fun _ : State => PermanssonResearch.X1.booleanRow p hp)) μ =
        (1-(p:ℝ))/(1-β) := by
    let c : ℝ := (1-(p:ℝ))/(1-β)
    have hc : ∀ _ : State, |c| ≤ |c| := fun _ => le_rfl
    have hπ : ∀ n hist,
        ((markovBehavior (fun _ : State => PermanssonResearch.X1.booleanRow p hp)) n hist).expect
          (fun a => Q G (fun _ => c) (last n hist) a) = c := by
      intro n hist
      simp only [markovBehavior, hQ, PermanssonResearch.X1.booleanRow_expect,
        Bool.false_eq_true, ↓reduceIte]
      calc
        _ = 1-(p:ℝ)+β*c := by ring
        _ = c := hfix p
    simpa [c] using discounted_attainment G _ μ (fun _ => c) hR hc hπ
  have hb : ∀ σ : BehavioralPolicy State Bool, payoff G σ μ ≤ 1/(1-β) := by
    intro σ
    let c : ℝ := 1/(1-β)
    have hc : ∀ _ : State, |c| ≤ |c| := fun _ => le_rfl
    have hv : ∀ y a, Q G (fun _ => c) y a ≤ c := by
      intro y a
      rw [hQ]
      have hh : 1+β*c=c := by
        dsimp [c]
        simpa using hfix 0
      cases a <;> simp <;> linarith
    simpa [c] using discounted_verification G σ μ (fun _ => c) hR hc hv
  have hbase := hvalue e he
  constructor
  · intro σ
    change payoff G σ μ -
      payoff G (markovBehavior (fun _ : State => PermanssonResearch.X1.booleanRow e he)) μ ≤ _
    rw [hbase]
    calc
      _ ≤ 1/(1-β)-(1-(e:ℝ))/(1-β) := sub_le_sub_right (hb σ) _
      _ = _ := by ring
  · refine ⟨markovBehavior (fun _ : State => PermanssonResearch.X1.booleanRow 0 (by norm_num)), ?_⟩
    change payoff G (markovBehavior (fun _ : State => PermanssonResearch.X1.booleanRow 0 (by norm_num))) μ -
      payoff G (markovBehavior (fun _ : State => PermanssonResearch.X1.booleanRow e he)) μ = _
    rw [hvalue 0 (by norm_num), hbase]
    push_cast
    ring

/-- Arbitrarily small strictly positive rational regret still gives a
unit discrepancy of the original infinite survival probabilities. -/
theorem arbitrarily_small_regret_unit_survival_gap (δ : ℚ) (hδ : 0 < δ) :
    ∃ e : ℚ, ∃ he : 0 < e ∧ e ≤ 1,
      e < δ ∧ NashChecks dominant dominant (coinRow e) (coinRow 0) e ∧
      rationalGain dominant (coinRow e) (coinRow 0) false = e ∧
      |(survivalForeverProbability (model 0 0 (by norm_num) (by norm_num))
          specification ((),0)).toReal -
        (survivalForeverProbability (model e 0 ⟨he.1.le,he.2⟩ (by norm_num))
          specification ((),0)).toReal| = 1 := by
  let e := min δ 1 / 2
  have hm : 0 < min δ (1:ℚ) := lt_min hδ (by norm_num)
  have he0 : 0 < e := by dsimp [e]; positivity
  have he1 : e ≤ 1 := by
    dsimp [e]
    linarith [min_le_right δ (1:ℚ)]
  have hlt : e < δ := by
    dsimp [e]
    linarith [min_le_left δ (1:ℚ)]
  have hy : ((),(0:Fin 3)) ∈ specification.region := by
    change (0:Fin 3) ≠ 2
    decide
  refine ⟨e,⟨he0,he1⟩,hlt,dominant_approx e ⟨he0.le,he1⟩,
    (dominant_regret_attained e).1,?_⟩
  rw [forever_zero_zero _ hy, forever_leak_zero e ⟨he0,he1⟩ _ hy]
  norm_num

/-- A modulus vanishing at zero would eventually be less than 1/2 on
positive rational inputs. The actual unit-gap family rules this out. -/
theorem no_vanishing_regret_modulus (f : ℚ → ℝ)
    (hsmall : ∃ δ : ℚ, 0 < δ ∧ ∀ e : ℚ, 0 < e → e < δ → f e < 1/2)
    (hbound : ∀ e : ℚ, ∀ he : 0 < e ∧ e ≤ 1,
      |(survivalForeverProbability (model 0 0 (by norm_num) (by norm_num))
        specification ((),0)).toReal -
        (survivalForeverProbability (model e 0 ⟨he.1.le,he.2⟩ (by norm_num))
          specification ((),0)).toReal| ≤ f e) : False := by
  obtain ⟨δ,hδ,hs⟩ := hsmall
  obtain ⟨e,he,heδ,_,_,hgap⟩ := arbitrarily_small_regret_unit_survival_gap δ hδ
  have hb := hbound e he
  rw [hgap] at hb
  linarith [hs e he.1 heδ]

end PermanssonResearch.ApproxEquilibrium.Examples
