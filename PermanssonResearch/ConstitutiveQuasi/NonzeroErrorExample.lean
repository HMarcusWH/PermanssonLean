import PermanssonResearch.ConstitutiveQuasi.CertificateTransport
import PermanssonLean.Examples.ConstitutiveNoninvariance
import Mathlib.Probability.Distributions.Bernoulli

/-!
# CQ-1 Part 3: a genuinely randomized typed strategic-pair construction

The approximate baseline randomizes the action (3/4 true, 1/4 false)
while retaining the frozen world primitive of modelB. Both baseline and
intervention remain typed strategic models. Numerical finite-step kernels
and margins are separately exercised by exact-rational regression fixtures.

This construction by itself does *not* assert an unproved uniform TV bound
or the full transported certificate: those require additional proved input
hypotheses to transportFiniteConstitutiveCertificate.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch
namespace ConstitutiveQuasi
namespace NonzeroErrorExample

open PermanssonLean
open PermanssonLean.Section7ConstitutiveNoninvariance

noncomputable section

/-- Probability of choosing baseline-preserving action true. -/
def preserveActionProbability : unitInterval :=
  ⟨(3 / 4 : ℝ), by norm_num⟩

/-- A state-independent genuinely randomized action selection. -/
def randomizedAction : Kernel (JointState Bool Bool) Bool :=
  Kernel.const _ (bernoulliMeasure true false preserveActionProbability)

def randomizedGenerator : StrategicGenerator Bool Bool Bool where
  action := randomizedAction
  update := updatePreserve
  action_isMarkov := by
    unfold randomizedAction
    infer_instance
  update_isMarkov := by
    unfold updatePreserve
    infer_instance

/-- Only the strategic generator changes; the world primitive is identical. -/
def randomizedModel : StrategicWorldModel Bool Bool Bool where
  generator := randomizedGenerator
  world := worldB
  world_isMarkov := by
    unfold worldB
    infer_instance

def randomizedFamily : InterventionFamily randomizedModel Unit where
  targetOf _ := .actionSelection
  admissible _ _ := True

def randomizedTypedIntervention : TypedIntervention randomizedFamily where
  component := ()
  replacement := falseReplacement

def randomizedIntervention :
    AdmissibleStrategicIntervention randomizedFamily where
  intervention := randomizedTypedIntervention
  accepted := by trivial
  strategic := by
    simp [TypedIntervention.IsStrategic,
      randomizedTypedIntervention, randomizedFamily]

/-- Fully typed original/approximate strategic pair with a single frozen P.
The construction does not assume equality of induced joint kernels. -/
def randomizedPair : StrategicApproximationPair modelB familyB interventionB where
  approx := randomizedModel
  approxFamily := randomizedFamily
  approxIntervention := randomizedIntervention
  approx_world_eq := rfl

theorem randomizedPair_preserves_original_world :
    randomizedIntervention.intervention.apply.world = modelB.world :=
  randomizedPair.approxIntervened_world_eq_original

end
end NonzeroErrorExample
end ConstitutiveQuasi
end PermanssonResearch
