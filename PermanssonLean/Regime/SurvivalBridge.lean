import PermanssonLean.Regime.ExitTime
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonLean

universe uS uX uA uH

variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]

namespace RegimeSpecification

/-- Finite-prefix version of the pathwise survival event. -/
def prefixSurvivalSet
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) :
    Set ((i : Set.Iic n) → JointState S X) :=
  {h | ∀ i, h i ∈ spec.region}

theorem measurableSet_prefixSurvivalSet
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) :
    MeasurableSet (prefixSurvivalSet spec n) := by
  have hEq :
      prefixSurvivalSet spec n =
        ⋂ i : Set.Iic n,
          (fun h : (j : Set.Iic n) → JointState S X => h i) ⁻¹' spec.region := by
    ext h
    simp [prefixSurvivalSet]
  rw [hEq]
  exact MeasurableSet.iInter fun i =>
    spec.region_measurable.preimage (measurable_pi_apply i)

theorem survivesThroughSet_eq_preimage_prefix
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) :
    survivesThroughSet spec n =
      Preorder.frestrictLe n ⁻¹' prefixSurvivalSet spec n := by
  ext w
  constructor
  · intro hw
    intro i
    exact hw i.1 (Set.mem_Iic.mp i.2)
  · intro hw t ht
    exact hw ⟨t, Set.mem_Iic.mpr ht⟩

theorem survivesThroughSet_zero
    (spec : RegimeSpecification (JointState S X) H) :
    survivesThroughSet spec 0 =
      (fun w : ℕ → JointState S X => w 0) ⁻¹' spec.region := by
  ext w
  simp [survivesThroughSet, SurvivesThrough]

/-- Distribution of the current endpoint among paths that have remained in B
through the current horizon. Missing mass is exactly the exit probability. -/
noncomputable def survivingEndpointMeasure
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X)
    (n : ℕ) :
    Measure (JointState S X) :=
  ((M.pathLaw (Measure.dirac y)).restrict (survivesThroughSet spec n)).map
    (fun w : ℕ → JointState S X => w n)

theorem survivingEndpointMeasure_zero
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {y : JointState S X}
    (hy : y ∈ spec.region) :
    survivingEndpointMeasure M spec y 0 = Measure.dirac y := by
  classical
  rw [survivingEndpointMeasure, survivesThroughSet_zero]
  rw [← Measure.restrict_map (measurable_pi_apply 0) spec.region_measurable]
  rw [StrategicWorldModel.pathLaw_eval_zero M (Measure.dirac y)]
  rw [Measure.restrict_dirac' spec.region_measurable]
  simp [hy]

/-- A one-step path decomposition: survival through n+1 is survival through n
plus membership of the new coordinate in B. -/
theorem survivesThroughSet_succ
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) :
    survivesThroughSet spec (n + 1) =
      survivesThroughSet spec n ∩
        (fun w : ℕ → JointState S X => w (n + 1)) ⁻¹' spec.region := by
  ext w
  constructor
  · intro hw
    refine ⟨?_, hw (n + 1) le_rfl⟩
    intro t ht
    exact hw t (ht.trans n.le_succ)
  · rintro ⟨hn, hnew⟩ t ht
    rcases lt_or_eq_of_le ht with hlt | rfl
    · exact hn t (Nat.lt_succ_iff.mp hlt)
    · exact hnew

/-- Preimage identity used to turn the path transition-pair law into a
survival recursion. -/
theorem pair_preimage_prefixSurvival_prod
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) {C : Set (JointState S X)} :
    (fun w : ℕ → JointState S X =>
      (Preorder.frestrictLe n w, w (n + 1))) ⁻¹'
        (prefixSurvivalSet spec n ×ˢ (C ∩ spec.region)) =
      ((fun w : ℕ → JointState S X => w (n + 1)) ⁻¹' C) ∩
        survivesThroughSet spec (n + 1) := by
  ext w
  constructor
  · rintro ⟨hp, hC, hB⟩
    refine ⟨hC, ?_⟩
    rw [survivesThroughSet_succ]
    refine ⟨?_, hB⟩
    rw [survivesThroughSet_eq_preimage_prefix]
    exact hp
  · rintro ⟨hC, hs⟩
    rw [survivesThroughSet_succ] at hs
    refine ⟨?_, hC, hs.2⟩
    rw [← survivesThroughSet_eq_preimage_prefix spec n]
    exact hs.1

/-- Surviving endpoint laws evolve by the killed kernel. -/
theorem survivingEndpointMeasure_succ
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X)
    (n : ℕ) :
    survivingEndpointMeasure M spec y (n + 1) =
      killedKernel M spec ∘ₘ survivingEndpointMeasure M spec y n := by
  let P := M.pathLaw (Measure.dirac y)
  let K := M.inducedKernel
  let pairFn : (ℕ → JointState S X) →
      (((i : Set.Iic n) → JointState S X) × JointState S X) :=
    fun w => (Preorder.frestrictLe n w, w (n + 1))
  let last : ((i : Set.Iic n) → JointState S X) → JointState S X :=
    fun h => h ⟨n, Set.mem_Iic.mpr le_rfl⟩
  ext C hC
  have hpair :
      (P.map (Preorder.frestrictLe n)) ⊗ₘ
          StrategicWorldModel.stationaryHistoryKernel K n =
        P.map pairFn := by
    exact StrategicWorldModel.pathLaw_has_transition_pair M (Measure.dirac y) n
  have hprefix := measurableSet_prefixSurvivalSet spec n
  have hCB : MeasurableSet (C ∩ spec.region) := hC.inter spec.region_measurable
  have hlast : Measurable last := by
    exact measurable_pi_apply ⟨n, Set.mem_Iic.mpr le_rfl⟩
  have hkernel :
      Measurable (fun z : JointState S X => K z (C ∩ spec.region)) :=
    Kernel.measurable_coe K hCB
  have hpairFn : Measurable pairFn := by
    fun_prop
  calc
    survivingEndpointMeasure M spec y (n + 1) C
        = P (((fun w : ℕ → JointState S X => w (n + 1)) ⁻¹' C) ∩
            survivesThroughSet spec (n + 1)) := by
          rw [survivingEndpointMeasure, Measure.map_apply (measurable_pi_apply (n + 1)) hC,
            Measure.restrict_apply]
          · rfl
          · exact hC.preimage (measurable_pi_apply (n + 1))
    _ = (P.map pairFn)
          (prefixSurvivalSet spec n ×ˢ (C ∩ spec.region)) := by
          rw [Measure.map_apply hpairFn (hprefix.prod hCB)]
          rw [pair_preimage_prefixSurvival_prod spec n]
    _ = ((P.map (Preorder.frestrictLe n)) ⊗ₘ
          StrategicWorldModel.stationaryHistoryKernel K n)
          (prefixSurvivalSet spec n ×ˢ (C ∩ spec.region)) := by
          rw [hpair]
    _ = ∫⁻ h in prefixSurvivalSet spec n,
          K (last h) (C ∩ spec.region)
          ∂(P.map (Preorder.frestrictLe n)) := by
          rw [Measure.compProd_apply_prod hprefix hCB]
          rfl
    _ = ∫⁻ w in survivesThroughSet spec n,
          K (w n) (C ∩ spec.region) ∂P := by
          rw [Measure.setLIntegral_map hprefix
            (hkernel.comp hlast) (measurable_frestrictLe n)]
          congr 1
          · rw [← survivesThroughSet_eq_preimage_prefix spec n]
          · funext w
            rfl
    _ = ∫⁻ z, K z (C ∩ spec.region)
          ∂survivingEndpointMeasure M spec y n := by
          rw [survivingEndpointMeasure, Measure.lintegral_map hkernel
            (measurable_pi_apply n)]
          rfl
    _ = (killedKernel M spec ∘ₘ survivingEndpointMeasure M spec y n) C := by
          rw [Measure.bind_apply hC (Kernel.aemeasurable _)]
          congr with z
          exact (killedKernel_apply M spec z hC).symm

/-- Strong bridge theorem: the endpoint law of paths surviving through n is
exactly the n-step killed-kernel law, for an initial state inside B. -/
theorem survivingEndpointMeasure_eq_killedPow
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) {y : JointState S X}
    (hy : y ∈ spec.region) :
    survivingEndpointMeasure M spec y n =
      ((killedKernel M spec) ^ n) y := by
  induction n with
  | zero =>
      simpa using survivingEndpointMeasure_zero M spec hy
  | succ n ih =>
      rw [survivingEndpointMeasure_succ M spec y n, ih]
      ext C hC
      rw [Measure.bind_apply hC (Kernel.aemeasurable _)]
      rw [Kernel.pow_succ_apply_eq_lintegral
        (killedKernel M spec) n y hC]

/-- Theorem 4.2a, equation (11b): finite path survival is exactly killed-kernel
survival mass. -/
theorem survivalProbability_eq_killedSurvivalMass
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) {y : JointState S X}
    (hy : y ∈ spec.region) :
    survivalProbability M spec y n =
      killedSurvivalMass M spec n y := by
  have hmeasure := survivingEndpointMeasure_eq_killedPow M spec n hy
  have htotal := congrArg (fun μ : Measure (JointState S X) => μ Set.univ) hmeasure
  rw [survivingEndpointMeasure, Measure.map_apply (measurable_pi_apply n) MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ] at htotal
  simpa [survivalProbability, killedSurvivalMass] using htotal

end RegimeSpecification

end PermanssonLean
