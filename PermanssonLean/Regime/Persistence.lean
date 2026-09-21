import PermanssonLean.Regime.SurvivalBridge
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Restrict

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory Topology

namespace PermanssonLean

universe uS uX uA uH

variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]

namespace RegimeSpecification

/-- Positive powers of the killed kernel remain output-restricted to B. -/
theorem killedKernel_pow_succ_restrict
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) :
    ((killedKernel M spec) ^ (n + 1)).restrict spec.region_measurable =
      (killedKernel M spec) ^ (n + 1) := by
  induction n with
  | zero =>
      ext y C hC
      rw [pow_one]
      rw [Kernel.restrict_apply]
      unfold killedKernel
      rw [Kernel.restrict_apply]
      rw [Measure.restrict_apply hC]
      rw [Measure.restrict_apply (hC.inter spec.region_measurable)]
      congr 1
      ext z
      simp [and_assoc]
  | succ n ih =>
      rw [pow_succ]
      rw [← Kernel.comp_restrict spec.region_measurable]
      rw [ih]

/-- Starting in B, every killed-kernel power is supported in B almost everywhere. -/
theorem killedKernel_pow_ae_mem_region
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) {y : JointState S X}
    (hy : y ∈ spec.region) :
    ∀ᵐ z ∂(((killedKernel M spec) ^ n) y), z ∈ spec.region := by
  cases n with
  | zero =>
      rw [pow_zero, Kernel.id_apply]
      exact (mem_ae_dirac_iff spec.region_measurable).2 hy
  | succ n =>
      have hres := congrArg
        (fun κ : Kernel (JointState S X) (JointState S X) => κ y)
        (killedKernel_pow_succ_restrict M spec n)
      rw [Kernel.restrict_apply] at hres
      rw [← hres]
      exact ae_restrict_mem spec.region_measurable

/-- Under a uniform one-step retention floor q on B, surviving mass obeys the
paper's q^L lower bound. -/
theorem oneStepRetention_pow_lowerBound
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (q : ℝ≥0∞)
    (hq : ∀ z ∈ spec.region, q ≤ M.inducedKernel z spec.region)
    (n : ℕ) {y : JointState S X}
    (hy : y ∈ spec.region) :
    q ^ n ≤ killedSurvivalMass M spec n y := by
  induction n with
  | zero =>
      simpa [killedSurvivalMass_zero M spec hy]
  | succ n ih =>
      rw [pow_succ, killedSurvivalMass_succ]
      have hae :
          (fun _ : JointState S X => q) ≤ᵐ[((killedKernel M spec) ^ n) y]
            (fun z => M.inducedKernel z spec.region) :=
        (killedKernel_pow_ae_mem_region M spec n hy).mono fun z hz => hq z hz
      have hint :
          ∫⁻ z, q ∂(((killedKernel M spec) ^ n) y) ≤
            ∫⁻ z, M.inducedKernel z spec.region
              ∂(((killedKernel M spec) ^ n) y) :=
        lintegral_mono_ae hae
      have hmass :
          (((killedKernel M spec) ^ n) y) Set.univ =
            (((killedKernel M spec) ^ n) y) spec.region := by
        exact (ae_mem_iff_measure_eq
          spec.region_measurable.nullMeasurableSet).mp
            (killedKernel_pow_ae_mem_region M spec n hy) |>.symm
      letI : IsFiniteKernel ((killedKernel M spec) ^ n) := by infer_instance
      letI : IsFiniteMeasure (((killedKernel M spec) ^ n) y) := by infer_instance
      rw [MeasureTheory.lintegral_const, hmass] at hint
      dsimp [killedSurvivalMass] at ih ⊢
      calc
        q ^ n * q ≤ (((killedKernel M spec) ^ n) y spec.region) * q := by
          exact mul_le_mul_right' ih q
        _ = q * (((killedKernel M spec) ^ n) y spec.region) := by
          rw [mul_comm]
        _ ≤ ∫⁻ z, M.inducedKernel z spec.region
              ∂(((killedKernel M spec) ^ n) y) := by
          simpa using hint

/-- Exact finite-horizon persistence, stated on path probabilities as in (11). -/
def IsFinitePersistent
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (L : ℕ) (eta : ℝ≥0∞) : Prop :=
  eta ≤ 1 ∧
  ∀ y ∈ spec.region, 1 - eta ≤ survivalProbability M spec y L

/-- Killed-kernel form of the same finite-horizon gate. -/
def IsKilledFinitePersistent
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (L : ℕ) (eta : ℝ≥0∞) : Prop :=
  eta ≤ 1 ∧
  ∀ y ∈ spec.region, 1 - eta ≤ killedSurvivalMass M spec L y

/-- Corollary 4.2b: the path-probability finite-persistence gate is
equivalent to the killed-kernel gate. The infimum notation in the paper is
represented by the equivalent pointwise lower-bound form. -/
theorem finitePersistence_iff_killed
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (L : ℕ) (eta : ℝ≥0∞) :
    IsFinitePersistent M spec L eta ↔
      IsKilledFinitePersistent M spec L eta := by
  constructor
  · rintro ⟨heta, h⟩
    refine ⟨heta, ?_⟩
    intro y hy
    rw [← survivalProbability_eq_killedSurvivalMass M spec L hy]
    exact h y hy
  · rintro ⟨heta, h⟩
    refine ⟨heta, ?_⟩
    intro y hy
    rw [survivalProbability_eq_killedSurvivalMass M spec L hy]
    exact h y hy

/-- The finite-horizon survival sets are decreasing in the horizon. -/
theorem survivesThroughSet_antitone
    (spec : RegimeSpecification (JointState S X) H) :
    Antitone (survivesThroughSet spec) := by
  intro m n hmn w hw
  exact fun t ht => hw t (ht.trans hmn)

/-- Indefinite retention is the countable intersection of all finite-horizon
retention events. -/
theorem survivesForeverSet_eq_iInter
    (spec : RegimeSpecification (JointState S X) H) :
    survivesForeverSet spec = ⋂ n : ℕ, survivesThroughSet spec n := by
  ext w
  change SurvivesForever spec w ↔ ∀ n : ℕ, SurvivesThrough spec n w
  constructor
  · intro h n t ht
    exact h t
  · intro h t
    exact h t t le_rfl


theorem survivesForeverSet_subset_survivesThroughSet
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) :
    survivesForeverSet spec ⊆ survivesThroughSet spec n := by
  intro w hw t ht
  exact hw t

theorem exactInvariant_survivalProbability_eq_one
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (hInv : IsExactlyInvariant M spec)
    (n : ℕ) {y : JointState S X}
    (hy : y ∈ spec.region) :
    survivalProbability M spec y n = 1 := by
  rw [survivalProbability_eq_killedSurvivalMass M spec n hy]
  apply le_antisymm
  · rw [← survivalProbability_eq_killedSurvivalMass M spec n hy]
    unfold survivalProbability
    exact prob_le_one
  · simpa using
      (oneStepRetention_pow_lowerBound M spec (1 : ℝ≥0∞)
        (fun z hz => by simpa [hInv z hz]) n hy)

/-- Exact invariance implies almost-sure indefinite retention. -/
theorem exactInvariant_survivalForever
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (hInv : IsExactlyInvariant M spec)
    {y : JointState S X}
    (hy : y ∈ spec.region) :
    survivalForeverProbability M spec y = 1 := by
  let P := M.pathLaw (Measure.dirac y)
  have hEach : ∀ n : ℕ, ∀ᵐ w ∂P, w ∈ survivesThroughSet spec n := by
    intro n
    apply (ae_mem_iff_measure_eq
      (measurableSet_survivesThroughSet spec n).nullMeasurableSet).2
    have hprob := exactInvariant_survivalProbability_eq_one M spec hInv n hy
    simpa [P, survivalProbability] using hprob
  have hAll : ∀ᵐ w ∂P, ∀ n : ℕ, w ∈ survivesThroughSet spec n :=
    MeasureTheory.ae_all_iff.2 hEach
  have hForever : ∀ᵐ w ∂P, w ∈ survivesForeverSet spec := by
    filter_upwards [hAll] with w hw
    rw [survivesForeverSet_eq_iInter]
    exact Set.mem_iInter.2 hw
  have hmeasure :
      P (survivesForeverSet spec) = P Set.univ :=
    (ae_mem_iff_measure_eq
      (measurableSet_survivesForeverSet spec).nullMeasurableSet).1 hForever
  simpa [survivalForeverProbability, P] using hmeasure

/-- Proposition 4.2: almost-sure indefinite retention implies exact one-step
invariance. -/
theorem survivalForever_implies_exactInvariant
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (hForever :
      ∀ y ∈ spec.region, survivalForeverProbability M spec y = 1) :
    IsExactlyInvariant M spec := by
  intro y hy
  let P := M.pathLaw (Measure.dirac y)
  have hsubset :
      survivesForeverSet spec ⊆ survivesThroughSet spec 1 :=
    survivesForeverSet_subset_survivesThroughSet spec 1
  have hmono :
      P (survivesForeverSet spec) ≤ P (survivesThroughSet spec 1) :=
    measure_mono hsubset
  have hforeverP : P (survivesForeverSet spec) = 1 := by
    simpa [P, survivalForeverProbability] using hForever y hy
  have hfinLower : 1 ≤ P (survivesThroughSet spec 1) := by
    simpa [hforeverP] using hmono
  have hfin : survivalProbability M spec y 1 = 1 := by
    apply le_antisymm
    · unfold survivalProbability
      exact prob_le_one
    · simpa [P, survivalProbability] using hfinLower
  rw [survivalProbability_eq_killedSurvivalMass M spec 1 hy,
    killedSurvivalMass_one] at hfin
  exact hfin

/-- Proposition 4.2 in iff form. -/
theorem exactInvariant_iff_survivalForever
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H) :
    IsExactlyInvariant M spec ↔
      ∀ y ∈ spec.region, survivalForeverProbability M spec y = 1 := by
  constructor
  · intro hInv y hy
    exact exactInvariant_survivalForever M spec hInv hy
  · exact survivalForever_implies_exactInvariant M spec

end RegimeSpecification

end PermanssonLean
