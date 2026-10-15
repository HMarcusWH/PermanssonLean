import PermanssonResearch.RegimeExit.ExitSubkernel
import PermanssonLean.Regime.ExitTimeExpectation
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Tactic

/-!
# C-Exit — first-exit routing as genuine measures, not scalar surrogates

The canonical path law and the actual killed/exit kernels are the only
stochastic objects. Every path identity has an inside-B support premise;
arbitrary-start routing measures are not a distribution of time-zero exits.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory Topology

namespace PermanssonResearch.RegimeExit

universe uS uX uA uH
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]
open PermanssonLean PermanssonLean.RegimeSpecification

/-- Missing original law-initialized forever-survival API, kept in research. -/
noncomputable def survivalForeverProbabilityFromLaw
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X)) : ℝ≥0∞ :=
  M.pathLaw μ.toMeasure (survivesForeverSet spec)

/-- Actual law-started n-th first-exit destination measure. -/
noncomputable def firstExitStepMeasureFromLaw
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (n : ℕ) : Measure (JointState S X) :=
  exitSubkernel M spec ∘ₘ killedMeasureIterate M spec μ.toMeasure n

/-- Recursively constructed finite routing measure, with no normalization trick. -/
noncomputable def exitRoutingFiniteMeasure
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X) : ℕ → Measure (JointState S X)
  | 0 => 0
  | L + 1 => exitRoutingFiniteMeasure M spec y L +
      firstExitStepMeasure M spec L y

/-- Countable sum of genuine subprobability first-exit destination measures. -/
noncomputable def exitRoutingInfiniteMeasure
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X) : Measure (JointState S X) :=
  Measure.sum (fun n : ℕ => firstExitStepMeasure M spec n y)

/-- Corresponding finite law-initialized measure, not assumed point-initial. -/
noncomputable def exitRoutingFiniteMeasureFromLaw
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X)) : ℕ → Measure (JointState S X)
  | 0 => 0
  | L + 1 => exitRoutingFiniteMeasureFromLaw M spec μ L +
      firstExitStepMeasureFromLaw M spec μ L

noncomputable def exitRoutingInfiniteMeasureFromLaw
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X)) : Measure (JointState S X) :=
  Measure.sum (fun n : ℕ => firstExitStepMeasureFromLaw M spec μ n)

noncomputable def exitRoutingFinite
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (L : ℕ) (y : JointState S X)
    (D : Set (JointState S X)) : ℝ≥0∞ :=
  exitRoutingFiniteMeasure M spec y L D

noncomputable def exitRoutingInfinite
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X)
    (D : Set (JointState S X)) : ℝ≥0∞ :=
  exitRoutingInfiniteMeasure M spec y D

noncomputable def exitRoutingFiniteFromLaw
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (L : ℕ) (μ : ProbabilityMeasure (JointState S X))
    (D : Set (JointState S X)) : ℝ≥0∞ :=
  exitRoutingFiniteMeasureFromLaw M spec μ L D

noncomputable def exitRoutingInfiniteFromLaw
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (D : Set (JointState S X)) : ℝ≥0∞ :=
  exitRoutingInfiniteMeasureFromLaw M spec μ D

theorem exitRoutingFinite_zero
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X) (D : Set (JointState S X)) :
    exitRoutingFinite M spec 0 y D = 0 := rfl

theorem exitRoutingFinite_succ
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (L : ℕ) (y : JointState S X)
    (D : Set (JointState S X))
    (hD : MeasurableSet D) :
    exitRoutingFinite M spec (L+1) y D =
      exitRoutingFinite M spec L y D +
        firstExitStepMass M spec L y D := by
  simp [exitRoutingFinite, exitRoutingFiniteMeasure,
    firstExitStepMass, Measure.add_apply hD]

theorem exitRoutingFiniteMeasure_apply
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (L : ℕ) (y : JointState S X)
    (D : Set (JointState S X)) (hD : MeasurableSet D) :
    exitRoutingFiniteMeasure M spec y L D =
      ∑ n ∈ Finset.range L, firstExitStepMass M spec n y D := by
  induction L with
  | zero => simp [exitRoutingFiniteMeasure]
  | succ L ih =>
      rw [exitRoutingFiniteMeasure, Measure.add_apply hD, ih]
      simp [Finset.sum_range_succ, firstExitStepMass]

theorem exitRoutingInfiniteMeasure_apply
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X)
    (D : Set (JointState S X)) (hD : MeasurableSet D) :
    exitRoutingInfiniteMeasure M spec y D =
      ∑' n : ℕ, firstExitStepMass M spec n y D := by
  simp only [exitRoutingInfiniteMeasure, Measure.sum_apply hD, firstExitStepMass]

theorem exitRoutingFiniteMeasureFromLaw_apply
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (L : ℕ) (μ : ProbabilityMeasure (JointState S X))
    (D : Set (JointState S X)) (hD : MeasurableSet D) :
    exitRoutingFiniteMeasureFromLaw M spec μ L D =
      ∑ n ∈ Finset.range L, firstExitStepMeasureFromLaw M spec μ n D := by
  induction L with
  | zero => simp [exitRoutingFiniteMeasureFromLaw]
  | succ L ih =>
      rw [exitRoutingFiniteMeasureFromLaw, Measure.add_apply hD, ih]
      simp [Finset.sum_range_succ]

theorem exitRoutingInfiniteMeasureFromLaw_apply
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (D : Set (JointState S X)) (hD : MeasurableSet D) :
    exitRoutingInfiniteMeasureFromLaw M spec μ D =
      ∑' n : ℕ, firstExitStepMeasureFromLaw M spec μ n D := by
  simp only [exitRoutingInfiniteMeasureFromLaw, Measure.sum_apply hD]

/-- The actual source law conditional on survival through n drives one exit row. -/
theorem firstExitAt_eq_stepFromLaw
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (n : ℕ) (D : Set (JointState S X))
    (hD : MeasurableSet D) :
    (M.pathLaw μ.toMeasure) (firstExitAtDestination spec n D) =
      (exitSubkernel M spec ∘ₘ survivingEndpointMeasureFromLaw M spec μ n) D := by
  let P := M.pathLaw μ.toMeasure
  let K := M.inducedKernel
  letI : IsMarkovKernel K := StrategicWorldModel.inducedKernel_isMarkov M
  let pairFn : (ℕ → JointState S X) →
      (((i : Finset.Iic n) → JointState S X) × JointState S X) :=
    fun w => (Preorder.frestrictLe n w, w (n+1))
  let last : ((i : Finset.Iic n) → JointState S X) → JointState S X :=
    fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩
  have hDout : MeasurableSet (D \ spec.region) :=
    hD.diff spec.region_measurable
  have hprefix := measurableSet_prefixSurvivalSet spec n
  have hlast : Measurable last := by dsimp [last]; fun_prop
  have hpairFn : Measurable pairFn := by fun_prop
  have hK : Measurable (fun z : JointState S X => K z (D \ spec.region)) :=
    Kernel.measurable_coe K hDout
  have hevent : pairFn ⁻¹' (prefixSurvivalSet spec n ×ˢ (D \ spec.region)) =
      firstExitAtDestination spec n D := by
    ext w
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff, Set.mem_diff]
    change (Preorder.frestrictLe n w ∈ prefixSurvivalSet spec n ∧
      w (n+1) ∈ D \ spec.region) ↔
      (w ∈ survivesThroughSet spec n ∧ w (n+1) ∈ D \ spec.region)
    rw [survivesThroughSet_eq_preimage_prefix spec n]
    rfl
  have hpair : (P.map (Preorder.frestrictLe n)) ⊗ₘ
      StrategicWorldModel.stationaryHistoryKernel K n = P.map pairFn :=
    StrategicWorldModel.pathLaw_has_transition_pair M μ.toMeasure n
  calc
    P (firstExitAtDestination spec n D) =
        (P.map pairFn) (prefixSurvivalSet spec n ×ˢ (D \ spec.region)) := by
      rw [Measure.map_apply hpairFn (hprefix.prod hDout), hevent]
    _ = ((P.map (Preorder.frestrictLe n)) ⊗ₘ
          StrategicWorldModel.stationaryHistoryKernel K n)
          (prefixSurvivalSet spec n ×ˢ (D \ spec.region)) := by rw [hpair]
    _ = ∫⁻ h in prefixSurvivalSet spec n,
          K (last h) (D \ spec.region)
          ∂(P.map (Preorder.frestrictLe n)) := by
      rw [Measure.compProd_apply_prod hprefix hDout]
      rfl
    _ = ∫⁻ w in survivesThroughSet spec n,
          K (w n) (D \ spec.region) ∂P := by
      change
        (∫⁻ h in prefixSurvivalSet spec n,
          ((fun z : JointState S X => K z (D \ spec.region)) ∘ last) h
          ∂(P.map (Preorder.frestrictLe n))) =
        ∫⁻ w in survivesThroughSet spec n,
          K (w n) (D \ spec.region) ∂P
      rw [setLIntegral_map hprefix (hK.comp hlast)
        (Preorder.measurable_frestrictLe n)]
      rw [← survivesThroughSet_eq_preimage_prefix spec n]
      rfl
    _ = ∫⁻ z, K z (D \ spec.region)
          ∂survivingEndpointMeasureFromLaw M spec μ n := by
      rw [survivingEndpointMeasureFromLaw,
        lintegral_map hK (measurable_pi_apply n)]
    _ = (exitSubkernel M spec ∘ₘ
          survivingEndpointMeasureFromLaw M spec μ n) D := by
      rw [Measure.bind_apply hD (Kernel.aemeasurable _)]
      congr with z
      exact (exitSubkernel_apply M spec z hD).symm

/-- Real path event = the genuine killed^n / exit composed measure. -/
theorem firstExitStep_eq_pathEvent
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) {y : JointState S X} (hy : y ∈ spec.region)
    (D : Set (JointState S X)) (hD : MeasurableSet D) :
    M.pathLaw (Measure.dirac y) (firstExitAtDestination spec n D) =
      firstExitStepMass M spec n y D := by
  have h := firstExitAt_eq_stepFromLaw M spec (diracProba y) n D hD
  change (M.pathLaw (Measure.dirac y)) (firstExitAtDestination spec n D) =
    (exitSubkernel M spec ∘ₘ
      survivingEndpointMeasure M spec y n) D at h
  rw [survivingEndpointMeasure_eq_killedPow M spec n hy] at h
  exact h

/-- The same actual route-step identity from a supported initial law. -/
theorem firstExitStepFromLaw_eq_pathEvent
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (hSupport : μ.toMeasure spec.region = 1)
    (n : ℕ) (D : Set (JointState S X)) (hD : MeasurableSet D) :
    (M.pathLaw μ.toMeasure) (firstExitAtDestination spec n D) =
      firstExitStepMeasureFromLaw M spec μ n D := by
  rw [firstExitAt_eq_stepFromLaw M spec μ n D hD,
    survivingEndpointMeasureFromLaw_eq_killedMeasureIterate M spec μ hSupport n]
  rfl

end PermanssonResearch.RegimeExit
