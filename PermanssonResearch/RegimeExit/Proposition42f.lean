import PermanssonResearch.RegimeExit.InProbabilityOccupation
import PermanssonResearch.RegimeExit.SwitchRouting
import PermanssonResearch.RegimeExit.SwitchRetention
import PermanssonResearch.RegimeExit.SwitchConstitution
import PermanssonResearch.RegimeExit.SwitchGrounded
import Mathlib.Tactic

/-!
# C-Exit E (C70.3) — scoped Proposition 4.2f (intervention-driven switching)

Integrates, without changing any upstream statement:

* PR #66 actual first-exit routing (`exitRoutingInfinite_eq_prob_exit_in`);
* PR #67 source/target Exact-GR certificates (`CertifiedSwitchData`), the
  routing bound `R_B^{J,∞}(y, B'_0) ≥ 1 − η` on `B₁` (`SwitchRoutingBound`),
  target retention (`switch_eventual_retention_ae`) and the margin bound for
  the FROZEN property `ψ_B(P_y) = P_y(τ_B = ∞)`
  (`switchSurvivalProperty`, `switch_constitutive_margin_ge`);
* PR #69 unconditional restart (C69) and C70.1/C70.2 random-entry occupation.

## Statements

For the two SUPPORTED convergence modes of the target specification:

* `proposition_4_2f_almostSure` (frozen `ConvergenceMode.almostSureWeak`):
  `κ_{ψ_B,J}(B₁) ≥ 1 − η`, and for every `y ∈ B₁` the event
  "finite first exit into `B'_0`, retention in `B'` from then on, and whole-path
  target occupation convergence to `ν'`" has probability at least `1 − η`
  (outer measure; the event agrees a.e. with the measurable routed event).
* `proposition_4_2f_inProbability` (research `inProbabilityWeak`): margin
  bound, retention event probability `≥ 1 − η`, and for every bounded
  continuous `f`, `ε > 0`: the routed-and-deviating probability tends to 0 and
  eventually the whole-path deviation probability is at most `η + δ`.
* `proposition_4_2f_eta_zero_almostSure`: with `η = 0` the switching event
  has probability one.
* Positive uniform constitution and grounded confirmatory PR require
  `η < 1` and all original gates; they are the unchanged PR #67 theorems
  `switch_uniformly_strategically_constitutive` and
  `switch_grounded_confirmatory_uniformPR`, re-exported here as
  `proposition_4_2f_uniformPR` with every hypothesis explicit.

## Nonclaims

* No other `ConvergenceMode.custom` predicate is transported.
* `η = 1` gives no positive margin (vacuous bound, unchanged).
* Nothing here identifies an empirical political or economic transition.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal BoundedContinuousFunction

namespace PermanssonResearch.RegimeExit

set_option autoImplicit false
open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA uH uT uK uG
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH} {T : Type uT}
variable {G : Type uG}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H] [MeasurableSpace T] [MeasurableSpace G]
variable [TopologicalSpace S] [TopologicalSpace X]

/-- The measurable switch-and-retain event: finite first exit into the
target basin at `n + 1` and target-region membership at every later time. -/
def switchRetainEvent
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T) :
    Set (ℕ → JointState S X) :=
  {w | ∃ n : ℕ, w ∈ firstExitAtDestination source n target.basin ∧
    ∀ t ≥ n+1, w t ∈ target.region}

theorem switchRetainEvent_measurable
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T) :
    MeasurableSet (switchRetainEvent source target) := by
  have hset : switchRetainEvent source target =
      ⋃ n : ℕ, (firstExitAtDestination source n target.basin ∩
        ⋂ t : ℕ, ⋂ (_ : n+1 ≤ t),
          (fun w : ℕ → JointState S X => w t) ⁻¹' target.region) := by
    ext w
    simp only [switchRetainEvent, Set.mem_setOf_eq, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, ge_iff_le]
  rw [hset]
  refine MeasurableSet.iUnion fun n => ?_
  refine (firstExitAtDestination_measurable source n target.basin
    target.basin_measurable).inter ?_
  refine MeasurableSet.iInter fun t => MeasurableSet.iInter fun _ => ?_
  exact target.region_measurable.preimage (measurable_pi_apply t)

theorem switchRetainEvent_subset_routed
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T) :
    switchRetainEvent source target ⊆
      firstExitEverDestination source target.basin := by
  rintro w ⟨n, hn, -⟩
  exact Set.mem_iUnion.mpr ⟨n, hn⟩

/-- The full almost-sure switching event (possibly non-measurable because of
the weak-convergence clause; its measure is the outer measure). -/
def switchOccupationEvent
    [TopologicalSpace T] [OpensMeasurableSpace T]
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T) :
    Set (ℕ → JointState S X) :=
  {w | w ∈ switchRetainEvent source target ∧
    Tendsto (fun m : ℕ => empiricalOccupation target w (m+1) (Nat.succ_pos m))
      atTop (𝓝 target.target)}

/-- Retention: the routed and switch-and-retain events agree almost surely
(PR #67 retention, unchanged). -/
theorem switch_routed_le_retain_ae
    (M : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    (mSource mTarget : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M source)
    (J : AdmissibleStrategicIntervention F)
    (cert : CertifiedSwitchData M source target mSource mTarget F B₁ J)
    (y : JointState S X) :
    ∀ᵐ w ∂J.intervention.apply.pathLaw (Measure.dirac y),
      w ∈ firstExitEverDestination source target.basin →
        w ∈ switchRetainEvent source target :=
  switch_eventual_retention_ae M source target mSource mTarget F B₁ J cert
    (diracProba y)

/-- Retention probability is at least `1 − η` on every comparison state. -/
theorem switchRetainEvent_prob_ge
    (M : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    (mSource mTarget : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M source)
    (J : AdmissibleStrategicIntervention F)
    (cert : CertifiedSwitchData M source target mSource mTarget F B₁ J)
    (eta : ℝ≥0∞) (hBound : SwitchRoutingBound M source target F B₁ J eta)
    {y : JointState S X} (hy : y ∈ B₁.states) :
    1 - eta ≤ J.intervention.apply.pathLaw (Measure.dirac y)
      (switchRetainEvent source target) :=
  (switch_first_exit_event_lower_bound M source target F B₁ J eta hBound hy).trans
    (measure_mono_ae (switch_routed_le_retain_ae M source target mSource mTarget
      F B₁ J cert y))

/-- **Scoped Proposition 4.2f, almost-sure weak mode.** -/
theorem proposition_4_2f_almostSure
    [TopologicalSpace T] [OpensMeasurableSpace T]
    (M : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    (mSource mTarget : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M source)
    (J : AdmissibleStrategicIntervention F)
    (cert : CertifiedSwitchData M source target mSource mTarget F B₁ J)
    (hmode : target.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) T)
    (eta : ℝ≥0∞) (hBound : SwitchRoutingBound M source target F B₁ J eta) :
    1 - eta.toReal ≤ constitutiveMargin M source F
        (switchSurvivalProperty source) B₁ J ∧
      ∀ y ∈ B₁.states,
        1 - eta ≤ J.intervention.apply.pathLaw (Measure.dirac y)
          (switchOccupationEvent source target) := by
  refine ⟨switch_constitutive_margin_ge M source target mSource mTarget F B₁ J
    cert eta hBound, fun y hy => ?_⟩
  have hyB : y ∈ source.region :=
    ConstitutiveComparisonSet.states_subset_region M source B₁ hy
  have hocc := randomEntry_occupation_ae J.intervention.apply source target
    mTarget cert.targetExact hmode hyB
  have hret := switch_routed_le_retain_ae M source target mSource mTarget F B₁ J
    cert y
  refine (switch_first_exit_event_lower_bound M source target F B₁ J eta
    hBound hy).trans (measure_mono_ae ?_)
  filter_upwards [hocc, hret] with w ho hr hroute
  exact ⟨hr hroute, ho hroute⟩

/-- With `η = 0` the full switching event is almost sure. -/
theorem proposition_4_2f_eta_zero_almostSure
    [TopologicalSpace T] [OpensMeasurableSpace T]
    (M : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    (mSource mTarget : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M source)
    (J : AdmissibleStrategicIntervention F)
    (cert : CertifiedSwitchData M source target mSource mTarget F B₁ J)
    (hmode : target.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) T)
    (hBound : SwitchRoutingBound M source target F B₁ J 0)
    {y : JointState S X} (hy : y ∈ B₁.states) :
    J.intervention.apply.pathLaw (Measure.dirac y)
      (switchOccupationEvent source target) = 1 := by
  apply le_antisymm prob_le_one
  have h := (proposition_4_2f_almostSure M source target mSource mTarget F B₁ J
    cert hmode 0 hBound).2 y hy
  simpa using h

/-- **Scoped Proposition 4.2f, research in-probability weak mode.** -/
theorem proposition_4_2f_inProbability
    [TopologicalSpace T] [OpensMeasurableSpace T]
    (M : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    (mSource mTarget : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M source)
    (J : AdmissibleStrategicIntervention F)
    (cert : CertifiedSwitchData M source target mSource mTarget F B₁ J)
    (hmode : target.convergenceMode = inProbabilityWeak (JointState S X) T)
    (eta : ℝ≥0∞) (hBound : SwitchRoutingBound M source target F B₁ J eta) :
    1 - eta.toReal ≤ constitutiveMargin M source F
        (switchSurvivalProperty source) B₁ J ∧
      ∀ y ∈ B₁.states,
        1 - eta ≤ J.intervention.apply.pathLaw (Measure.dirac y)
            (switchRetainEvent source target) ∧
        ∀ f : T →ᵇ ℝ, ∀ ε : ℝ, 0 < ε →
          Tendsto (fun n : ℕ => J.intervention.apply.pathLaw (Measure.dirac y)
            (firstExitEverDestination source target.basin ∩
              occupationDeviationSet target f ε n)) atTop (𝓝 0) ∧
          ∀ δ : ℝ≥0∞, 0 < δ → ∀ᶠ n : ℕ in atTop,
            J.intervention.apply.pathLaw (Measure.dirac y)
              (occupationDeviationSet target f ε n) ≤ eta + δ := by
  refine ⟨switch_constitutive_margin_ge M source target mSource mTarget F B₁ J
    cert eta hBound, fun y hy => ⟨switchRetainEvent_prob_ge M source target
      mSource mTarget F B₁ J cert eta hBound hy, fun f ε hε => ⟨?_, ?_⟩⟩⟩
  · exact randomEntry_occupation_inProbability J.intervention.apply source target
      mTarget cert.targetExact hmode
      (ConstitutiveComparisonSet.states_subset_region M source B₁ hy) f hε
  · intro δ hδ
    exact inProbability_deviation_eventually_le J.intervention.apply source
      target mTarget cert.targetExact hmode
      (ConstitutiveComparisonSet.states_subset_region M source B₁ hy) f hε
      (switch_first_exit_event_lower_bound M source target F B₁ J eta hBound hy)
      hδ

/-- Positive uniform constitution and grounded confirmatory PR for the frozen
survival property: the PR #67 theorem with every gate explicit (`η < 1`,
confirmatory source GR, grounded property relative to `g`). -/
theorem proposition_4_2f_uniformPR
    (M : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    (mSource mTarget : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M source)
    (J : AdmissibleStrategicIntervention F)
    (cert : CertifiedSwitchData M source target mSource mTarget F B₁ J)
    (eta : ℝ≥0∞) (hBound : SwitchRoutingBound M source target F B₁ J eta)
    (hEta : eta < 1)
    (g : GroundedRelevanceMap source G)
    (hConfirmatory : IsConfirmatoryGeneratedRegime M source mSource)
    (hGrounded : IsGroundedPropertyRelative M source F
      (switchSurvivalProperty source) g J) :
    IsGroundedConfirmatoryUniformPermanssonRegimeRelative
      M source mSource F (switchSurvivalProperty source) g B₁ J :=
  switch_grounded_confirmatory_uniformPR M source target mSource mTarget F B₁ J
    cert eta hBound hEta g hConfirmatory hGrounded

end PermanssonResearch.RegimeExit
