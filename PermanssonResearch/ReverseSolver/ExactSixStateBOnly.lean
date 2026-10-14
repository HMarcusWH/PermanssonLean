import PermanssonResearch.ReverseSolver.ComputableSixStateFixtures
import PermanssonResearch.ReverseSolver.RationalTypedSupportBridge
import PermanssonResearch.MultipleLimit.TypedEventResponse
import PermanssonResearch.MultipleLimit.FiniteObservedUniformMargin
import Mathlib.Tactic

/-!
# C10 — genuinely typed B-only zero original constitutive margin

Unlike C6's prior Python B_ONLY fixture, this is an original typed
admissible alpha-only intervention preserving P/U. Both comparison starts
reach the true B recurrent class, so the SAME original eventual-true path
property has probability one on both sides and original margin zero.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

open PermanssonLean
open PermanssonLean.RegimeSpecification
open PermanssonResearch.MultipleLimit
open PermanssonResearch.MultipleLimit.KernelCommunication
open PermanssonResearch.MultipleLimit.CanonicalRecurrentResidence
open PermanssonResearch.MultipleLimit.ExactSixState
open PermanssonResearch.MultipleLimit.ExactSixStateCanonical
open PermanssonResearch.MultipleLimit.ExactSixStateObservedGR
open PermanssonResearch.MultipleLimit.ExactSixStateTyped
open PermanssonResearch.MultipleLimit.RecurrentClassDecomposition
open PermanssonResearch.MultipleLimit.ExactSixStateConstitution
open PermanssonResearch.MultipleLimit.TypedEventResponse
open PermanssonResearch.MultipleLimit.FrozenObservedEvent
open PermanssonResearch.MultipleLimit.FiniteObservedUniformMargin
open FiniteStrategicRealization
open RationalTypedSupportBridge

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

private abbrev KB := bOnlyJ.intervention.apply.inducedKernel
private abbrev SixY := JointState Unit (Fin 6)

def bOnlyBSet : Set SixY :=
  {decode (4 : Fin 6), decode (5 : Fin 6)}

private theorem bOnlyBSet_closed : ClosedSubset KB bOnlyBSet := by
  intro y hy z hedge
  have hi : y = decode (4 : Fin 6) ∨ y = decode (5 : Fin 6) := by
    simpa [bOnlyBSet] using hy
  rcases z with ⟨u, j⟩
  cases u
  have hp (i : Fin 6) (he : y = decode i) :
      0 < bOnlyMatrixExecutable.entry i j := by
    subst y
    have hedge' : PositiveEdge
        (rationalStrategicIntervention sixStateMatrix
          bOnlyMatrixExecutable).intervention.apply.inducedKernel
        (decode i) (decode j) := by
      simpa [KB, bOnlyJ, decode] using hedge
    exact (rationalTyped_positiveEdge_iff
      sixStateMatrix bOnlyMatrixExecutable i j).mp hedge'
  have hj : j = 4 ∨ j = 5 := by
    rcases hi with h4 | h5
    · have hpos := hp 4 h4
      fin_cases j <;>
        simp_all [bOnlyMatrixExecutable, bOnlyEntryExecutable, transition]
    · have hpos := hp 5 h5
      fin_cases j <;>
        simp_all [bOnlyMatrixExecutable, bOnlyEntryExecutable, transition]
  rcases hj with rfl | rfl <;> simp [bOnlyBSet, decode]

/-- Each of the six states has an actual strict-positive rational path
into the original B recurrent set; no zero-probability graph edge counts. -/
private theorem all_reach_b0 (x : Fin 6) :
    Reachable KB (decode x) (decode (4 : Fin 6)) := by
  have h : RationalReachable bOnlyMatrixExecutable x (4 : Fin 6) := by
    fin_cases x
    · exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (show
          0 < bOnlyMatrixExecutable.entry (0 : Fin 6) (1 : Fin 6) by
            norm_num [bOnlyMatrixExecutable, bOnlyEntryExecutable, transition]))
        (Relation.ReflTransGen.single (show
          0 < bOnlyMatrixExecutable.entry (1 : Fin 6) (4 : Fin 6) by
            norm_num [bOnlyMatrixExecutable, bOnlyEntryExecutable, transition]))
    · exact Relation.ReflTransGen.single (show
        0 < bOnlyMatrixExecutable.entry (1 : Fin 6) (4 : Fin 6) by
          norm_num [bOnlyMatrixExecutable, bOnlyEntryExecutable, transition])
    · exact Relation.ReflTransGen.single (show
        0 < bOnlyMatrixExecutable.entry (2 : Fin 6) (4 : Fin 6) by
          norm_num [bOnlyMatrixExecutable, bOnlyEntryExecutable, transition])
    · exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (show
          0 < bOnlyMatrixExecutable.entry (3 : Fin 6) (2 : Fin 6) by
            norm_num [bOnlyMatrixExecutable, bOnlyEntryExecutable, transition]))
        (Relation.ReflTransGen.single (show
          0 < bOnlyMatrixExecutable.entry (2 : Fin 6) (4 : Fin 6) by
            norm_num [bOnlyMatrixExecutable, bOnlyEntryExecutable, transition]))
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (show
        0 < bOnlyMatrixExecutable.entry (5 : Fin 6) (4 : Fin 6) by
          norm_num [bOnlyMatrixExecutable, bOnlyEntryExecutable, transition])
  exact (rationalTyped_reachable_iff sixStateMatrix
    bOnlyMatrixExecutable x 4).mp h

/-- The only possible recurrent states under the typed B-only model are
within the true-labelled B set. -/
private theorem bOnly_recurrent_true (y : SixY)
    (hy : y ∈ RecurrentStates KB) :
    observedDescriptor y = true := by
  rcases y with ⟨u, i⟩
  cases u
  have hto := all_reach_b0 i
  have hclosed : ClosedSubset KB (CommunicatingClass KB (decode i)) := hy
  have h4 : decode (4 : Fin 6) ∈ CommunicatingClass KB (decode i) :=
    closed_reachable KB hclosed (mem_communicatingClass KB (decode i)) hto
  have hback := h4.2
  have hin : decode i ∈ bOnlyBSet :=
    closed_reachable KB bOnlyBSet_closed
      (by simp [bOnlyBSet]) hback
  have hi : i = 4 ∨ i = 5 := by
    simpa [bOnlyBSet, decode] using hin
  rcases hi with rfl | rfl <;>
    norm_num [observedDescriptor, observedRecurrent, encode, decode]

/-- Actual infinite typed path law, not a reference-matrix heuristic. -/
theorem bOnly_eventually_true_ae (y : SixY) :
    ∀ᵐ w ∂bOnlyJ.intervention.apply.pathLaw (Measure.dirac y),
      w ∈ eventuallyObserved observedDescriptor true := by
  have h := canonical_eventually_observed_ae KB observedDescriptor
    bOnly_recurrent_true (diracProba y)
  change ∀ᵐ w ∂bOnlyJ.intervention.apply.pathLaw (Measure.dirac y),
    w ∈ eventuallyObserved observedDescriptor true at h
  exact h

/-- Exact genuine path-law probability from every original starting state. -/
theorem bOnly_event_probability_one (y : SixY) :
    bOnlyJ.intervention.apply.pathLaw (Measure.dirac y)
      (eventuallyObserved observedDescriptor true) = 1 := by
  let P := bOnlyJ.intervention.apply.pathLaw (Measure.dirac y)
  have hAE := bOnly_eventually_true_ae y
  rw [ae_iff] at hAE
  have hzero : P (eventuallyObserved observedDescriptor true)ᶜ = 0 := by
    exact hAE
  have hsum := measure_add_measure_compl
    (eventuallyObserved_measurable observedDescriptor true
      Measurable.of_discrete) (μ := P)
  rw [hzero] at hsum
  simpa using hsum

/-- The original positive-probability property is the SAME fixed
path-law functional as in the frozen C6 experiment. -/
theorem bOnly_original_effect_zero (y : SixY) :
    constitutiveEffect typedModel
      (eventuallyObservedProperty observedDescriptor true) bOnlyJ y = 0 := by
  change dist
    ((typedModel.pathLaw (Measure.dirac y))
      (eventuallyObserved observedDescriptor true)).toReal
    ((bOnlyJ.intervention.apply.pathLaw (Measure.dirac y))
      (eventuallyObserved observedDescriptor true)).toReal = 0
  have hbase :
      (typedModel.pathLaw (Measure.dirac y))
        (eventuallyObserved observedDescriptor true) = 1 := by
    simpa only [TypedEventResponse.eventuallyTrue] using
      baseline_event_probability_one y
  rw [hbase, bOnly_event_probability_one y]
  simp

/-- True original B₁ margin, not a C10 surrogate. -/
theorem bOnly_original_margin_zero :
    constitutiveMargin typedModel observedSpec
      (researchActionFamily sixStateMatrix)
      (eventuallyObservedProperty observedDescriptor true)
      comparison bOnlyJ = 0 := by
  obtain ⟨y, hy, hmin⟩ :=
    finite_margin_attained typedModel observedSpec
      (researchActionFamily sixStateMatrix)
      (eventuallyObservedProperty observedDescriptor true)
      comparison bOnlyJ
  rw [hmin, bOnly_original_effect_zero y]

end
end C10
end ReverseSolver
end PermanssonResearch