import PermanssonLean.Regime.ExitTime
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
      simp [killedKernel, Kernel.restrict_apply' _ spec.region_measurable _ hC,
        Measure.restrict_apply hC, Set.inter_assoc]
  | succ n ih =>
      rw [pow_succ]
      have hpow :
          (killedKernel M spec) ^ (n + 1) =
            ((killedKernel M spec) ^ (n + 1)).restrict spec.region_measurable := ih.symm
      rw [hpow]
      symm
      exact Kernel.comp_restrict spec.region_measurable

/-- Starting in B, every killed-kernel power is supported in B almost everywhere. -/
theorem killedKernel_pow_ae_mem_region
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) {y : JointState S X}
    (hy : y ∈ spec.region) :
    ∀ᵐ z ∂(((killedKernel M spec) ^ n) y), z ∈ spec.region := by
  cases n with
  | zero =>
      simp only [pow_zero, Kernel.id_apply]
      simpa [MeasureTheory.ae_dirac_iff] using hy
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
      rw [MeasureTheory.lintegral_const, hmass] at hint
      dsimp [killedSurvivalMass] at ih ⊢
      calc
        q * q ^ n ≤ q * (((killedKernel M spec) ^ n) y spec.region) := by
          gcongr
        _ ≤ ∫⁻ z, M.inducedKernel z spec.region
              ∂(((killedKernel M spec) ^ n) y) := by
          simpa [mul_comm] using hint

/-- Exact finite-horizon persistence, stated on path probabilities as in (11). -/
def IsFinitePersistent
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (L : ℕ) (eta : ℝ≥0∞) : Prop :=
  ∀ y ∈ spec.region, 1 - eta ≤ survivalProbability M spec y L

/-- Killed-kernel form of the same finite-horizon gate. -/
def IsKilledFinitePersistent
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (L : ℕ) (eta : ℝ≥0∞) : Prop :=
  ∀ y ∈ spec.region, 1 - eta ≤ killedSurvivalMass M spec L y

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
  simp [survivesForeverSet, SurvivesForever, survivesThroughSet, SurvivesThrough]

end RegimeSpecification

end PermanssonLean
