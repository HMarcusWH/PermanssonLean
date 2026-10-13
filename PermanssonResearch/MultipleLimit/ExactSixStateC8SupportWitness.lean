import PermanssonResearch.MultipleLimit.TypedObservedSupportInvariance
import PermanssonResearch.MultipleLimit.ExactSixStateConstitution
import PermanssonResearch.MultipleLimit.ExactSixStateRecurrentGeometry
import Mathlib.Tactic

/-!
# C8 — two truly typed interventions, identical positive support, unequal probabilities

The frozen ORIGINAL six-state baseline is C6's proper-region Exact GR,
with the original two-point comparison set and observed Boolean descriptor.
Both interventions change only the action-selection kernel, leaving the
same world P and strategic update U. They have EQUAL positive kernel
support, but independent exact-rational adversaries demonstrate
different constitutive margins. Here Lean proves real typed admission,
equal intervention support, positive opposing-class reachability at
BOTH comparison states, original uniform PR for both, and G7 transport.

No empirical claim or numerical margin equality is inferred from
matching graph support.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactSixStateC8SupportWitness

set_option autoImplicit false

open PermanssonLean
open PermanssonLean.RegimeSpecification
open ReverseSolver
open ReverseSolver.FiniteStrategicRealization
open ExactSixState
open ExactSixStateCanonical
open ExactSixStateObservedGR
open ExactSixStateTyped
open ExactSixStateTargetDisruption
open ExactSixStateRecurrentGeometry
open ExactSixStateConstitution
open FrozenObservedEvent
open FiniteObservedBadClassReachability
open OppositeClassConstitutiveMargin
open ObservedSupportInvariance
open TypedObservedSupportInvariance
open FiniteObservedClassSupport
open KernelCommunication
open RecurrentClassDecomposition
open CanonicalClassSelector

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

abbrev SixY := JointState Unit (Fin 6)

/-- Both replacements make u absorbing and give a0 a one-time
split between false recurrent u and true recurrent B (b0).
No other row differs from the baseline six-state model. -/
def softEntry (ε : ℚ) (i j : Fin 6) : ℚ :=
  if i = 1 then (if j = 1 then 1 else 0)
  else if i = 2 then
    (if j = 1 then ε else if j = 4 then 1-ε else 0)
  else transition i j

def halfEntry (i j : Fin 6) : ℚ := softEntry (1/2) i j
def tinyEntry (i j : Fin 6) : ℚ := softEntry (1/1000) i j

theorem halfEntry_nonneg (i j : Fin 6) : 0 ≤ halfEntry i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [halfEntry, softEntry, transition]

theorem tinyEntry_nonneg (i j : Fin 6) : 0 ≤ tinyEntry i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [tinyEntry, softEntry, transition]

theorem halfEntry_row_sum (i : Fin 6) :
    (∑ j : Fin 6, halfEntry i j) = 1 := by
  fin_cases i <;>
    norm_num [halfEntry, softEntry, transition, Fin.sum_univ_succ]

theorem tinyEntry_row_sum (i : Fin 6) :
    (∑ j : Fin 6, tinyEntry i j) = 1 := by
  fin_cases i <;>
    norm_num [tinyEntry, softEntry, transition, Fin.sum_univ_succ]

def halfMatrix : RationalMarkovMatrix 6 where
  entry := halfEntry
  entry_nonneg := halfEntry_nonneg
  row_sum_one := halfEntry_row_sum

def tinyMatrix : RationalMarkovMatrix 6 where
  entry := tinyEntry
  entry_nonneg := tinyEntry_nonneg
  row_sum_one := tinyEntry_row_sum

def halfJ : AdmissibleStrategicIntervention
    (researchActionFamily sixStateMatrix) :=
  rationalStrategicIntervention sixStateMatrix halfMatrix

def tinyJ : AdmissibleStrategicIntervention
    (researchActionFamily sixStateMatrix) :=
  rationalStrategicIntervention sixStateMatrix tinyMatrix

private abbrev Kh := halfJ.intervention.apply.inducedKernel
private abbrev Kt := tinyJ.intervention.apply.inducedKernel

/-- True singleton atoms of the actual alpha/P/U induced kernel,
rather than an unconnected reference-matrix assertion. -/
theorem half_atom (i j : Fin 6) :
    Kh (decode i) ({decode j} : Set SixY) =
      ENNReal.ofReal ((halfEntry i j : ℚ) : ℝ) := by
  have hset : ({decode j} : Set SixY) =
      encode ⁻¹' ({j} : Set (Fin 6)) := by
    ext y
    rcases y with ⟨s,k⟩
    cases s
    simp [encode, decode]
  rw [hset]
  exact inducedKernel_encodedEntry halfMatrix i j

theorem tiny_atom (i j : Fin 6) :
    Kt (decode i) ({decode j} : Set SixY) =
      ENNReal.ofReal ((tinyEntry i j : ℚ) : ℝ) := by
  have hset : ({decode j} : Set SixY) =
      encode ⁻¹' ({j} : Set (Fin 6)) := by
    ext y
    rcases y with ⟨s,k⟩
    cases s
    simp [encode, decode]
  rw [hset]
  exact inducedKernel_encodedEntry tinyMatrix i j

/-- The two genuine typed intervention kernels have EXACTLY
the same POSITIVE support, despite distinct rational entries. -/
theorem same_intervened_positive_support :
    SamePositiveSupport Kh Kt := by
  intro x z
  rcases x with ⟨sx,i⟩
  rcases z with ⟨sz,j⟩
  cases sx
  cases sz
  change 0 < Kh (decode i) ({decode j} : Set SixY) ↔
    0 < Kt (decode i) ({decode j} : Set SixY)
  rw [half_atom, tiny_atom]
  fin_cases i <;> fin_cases j <;>
    norm_num [halfEntry, tinyEntry, softEntry, transition]

private theorem singleton_u_closed_of_row
    (L : Kernel SixY SixY)
    (hrow : L (decode (1 : Fin 6)) =
      Measure.dirac (decode (1 : Fin 6))) :
    ClosedSubset L ({decode (1 : Fin 6)} : Set SixY) := by
  intro y hy z hedge
  have hyu : y = decode (1 : Fin 6) :=
    Set.mem_singleton_iff.mp hy
  subst y
  change 0 < L (decode (1 : Fin 6)) ({z} : Set SixY) at hedge
  rw [hrow] at hedge
  by_contra hnot
  have hzero : (Measure.dirac (decode (1 : Fin 6)))
    ({z} : Set SixY) = 0 := by
    have hz : z ≠ decode (1 : Fin 6) := by simpa using hnot
    simp [hz]
  exact (ne_of_gt hedge) hzero

theorem half_u_absorbing :
    Kh (decode (1 : Fin 6)) =
      Measure.dirac (decode (1 : Fin 6)) := by
  apply Measure.ext_of_singleton
  intro z
  rcases z with ⟨sz,j⟩
  cases sz
  change Kh (decode (1 : Fin 6))
      ({decode j} : Set SixY) =
    Measure.dirac (decode (1 : Fin 6)) ({decode j} : Set SixY)
  rw [half_atom]
  fin_cases j <;> norm_num [halfEntry, softEntry, decode]

theorem tiny_u_absorbing :
    Kt (decode (1 : Fin 6)) =
      Measure.dirac (decode (1 : Fin 6)) := by
  apply Measure.ext_of_singleton
  intro z
  rcases z with ⟨sz,j⟩
  cases sz
  change Kt (decode (1 : Fin 6))
      ({decode j} : Set SixY) =
    Measure.dirac (decode (1 : Fin 6)) ({decode j} : Set SixY)
  rw [tiny_atom]
  fin_cases j <;> norm_num [tinyEntry, softEntry, decode]

/-- An absorbing false state is a BAD recurrent class, with its own
canonical class representative. No equality of differently chosen
noncomputable representatives is assumed. -/
private theorem absorbing_u_is_bad
    (L : Kernel SixY SixY) [IsMarkovKernel L]
    (hrow : L (decode (1 : Fin 6)) =
      Measure.dirac (decode (1 : Fin 6))) :
    decode (1 : Fin 6) ∈
      badRecurrentRepresentatives L observedDescriptor := by
  let u : SixY := decode (1 : Fin 6)
  have hclosed : ClosedSubset L ({u} : Set SixY) :=
    singleton_u_closed_of_row L hrow
  have hclass : CommunicatingClass L u = {u} := by
    ext z
    constructor
    · intro hz
      exact closed_reachable L hclosed
        (Set.mem_singleton u) hz.1
    · intro hz
      have heq : z = u := Set.mem_singleton_iff.mp hz
      subst z
      exact mem_communicatingClass L u
  have hrec : u ∈ RecurrentStates L := by
    change ClosedSubset L (CommunicatingClass L u)
    rw [hclass]
    exact hclosed
  have hrep : classRepresentative L u = u := by
    have hm := classRepresentative_mem L u
    rw [hclass] at hm
    exact Set.mem_singleton_iff.mp hm
  have hm : u ∈ recurrentRepresentatives L := by
    simp [recurrentRepresentatives, hrec, hrep]
  have hbad : ¬ AllTrueClass L observedDescriptor u := by
    intro hb
    have ht := hb u (mem_communicatingClass L u)
    have hf : observedDescriptor u = false := by
      simpa only [u] using descriptor_u_false
    rw [hf] at ht
    cases ht
  exact Finset.mem_filter.mpr ⟨hm, hbad⟩

theorem half_bad_u :
    decode (1 : Fin 6) ∈
      badRecurrentRepresentatives Kh observedDescriptor :=
  absorbing_u_is_bad Kh half_u_absorbing

theorem tiny_bad_u :
    decode (1 : Fin 6) ∈
      badRecurrentRepresentatives Kt observedDescriptor :=
  absorbing_u_is_bad Kt tiny_u_absorbing

theorem half_a0_to_u_positive :
    PositiveEdge Kh (decode (2 : Fin 6)) (decode (1 : Fin 6)) := by
  unfold PositiveEdge
  rw [half_atom]
  norm_num [halfEntry, softEntry]

theorem tiny_a0_to_u_positive :
    PositiveEdge Kt (decode (2 : Fin 6)) (decode (1 : Fin 6)) := by
  unfold PositiveEdge
  rw [tiny_atom]
  norm_num [tinyEntry, softEntry]

theorem half_opposing_reachable (y : SixY)
    (hy : y ∈ comparison.states) :
    OpposingClassReachable Kh observedDescriptor
      observedSpec.target y := by
  change ∃ i ∈ badRecurrentRepresentatives Kh observedDescriptor,
    Reachable Kh y i
  rcases (comparison_states y).mp hy with hyu | hya
  · subst y
    exact ⟨decode (1 : Fin 6), half_bad_u,
      reachable_refl Kh (decode (1 : Fin 6))⟩
  · subst y
    exact ⟨decode (1 : Fin 6), half_bad_u,
      reachable_single Kh half_a0_to_u_positive⟩

theorem tiny_opposing_reachable (y : SixY)
    (hy : y ∈ comparison.states) :
    OpposingClassReachable Kt observedDescriptor
      observedSpec.target y := by
  change ∃ i ∈ badRecurrentRepresentatives Kt observedDescriptor,
    Reachable Kt y i
  rcases (comparison_states y).mp hy with hyu | hya
  · subst y
    exact ⟨decode (1 : Fin 6), tiny_bad_u,
      reachable_refl Kt (decode (1 : Fin 6))⟩
  · subst y
    exact ⟨decode (1 : Fin 6), tiny_bad_u,
      reachable_single Kt tiny_a0_to_u_positive⟩

/-- Two distinct permissively admitted alpha-only replacements
both satisfy the ORIGINAL unweakened uniform PR predicate. -/
theorem half_uniformRelativePR :
    IsUniformGeneralizedPermanssonRegimeRelative
      typedModel observedSpec observedReference
      (researchActionFamily sixStateMatrix)
      (eventuallyObservedProperty observedDescriptor true)
      comparison halfJ := by
  apply (original_uniformRelativePR_iff_opposingReachability
    typedModel observedSpec observedReference
    (researchActionFamily sixStateMatrix)
    comparison halfJ rfl).mpr
  exact ⟨observedExactGeneratedRegime,
    fun y hy => half_opposing_reachable y hy⟩

theorem tiny_uniformRelativePR :
    IsUniformGeneralizedPermanssonRegimeRelative
      typedModel observedSpec observedReference
      (researchActionFamily sixStateMatrix)
      (eventuallyObservedProperty observedDescriptor true)
      comparison tinyJ := by
  apply (original_uniformRelativePR_iff_opposingReachability
    typedModel observedSpec observedReference
    (researchActionFamily sixStateMatrix)
    comparison tinyJ rfl).mpr
  exact ⟨observedExactGeneratedRegime,
    fun y hy => tiny_opposing_reachable y hy⟩

/-- G7 specialized to two genuinely admissible interventions.
The theorem only equates original PR status, NOT numerical margins. -/
theorem qualitative_uniformPR_invariance :
    IsUniformGeneralizedPermanssonRegimeRelative
      typedModel observedSpec observedReference
      (researchActionFamily sixStateMatrix)
      (eventuallyObservedProperty observedDescriptor true)
      comparison halfJ ↔
    IsUniformGeneralizedPermanssonRegimeRelative
      typedModel observedSpec observedReference
      (researchActionFamily sixStateMatrix)
      (eventuallyObservedProperty observedDescriptor true)
      comparison tinyJ :=
  original_uniformPR_iff_of_same_intervened_support
    typedModel observedSpec observedReference
    (researchActionFamily sixStateMatrix)
    comparison halfJ tinyJ rfl same_intervened_positive_support

theorem half_world_fixed :
    halfJ.intervention.apply.world = typedModel.world :=
  rationalStrategicIntervention_world_fixed sixStateMatrix halfMatrix

theorem tiny_world_fixed :
    tinyJ.intervention.apply.world = typedModel.world :=
  rationalStrategicIntervention_world_fixed sixStateMatrix tinyMatrix

theorem half_update_fixed :
    halfJ.intervention.apply.generator.update =
      typedModel.generator.update :=
  rationalStrategicIntervention_update_fixed sixStateMatrix halfMatrix

theorem tiny_update_fixed :
    tinyJ.intervention.apply.generator.update =
      typedModel.generator.update :=
  rationalStrategicIntervention_update_fixed sixStateMatrix tinyMatrix

end
end ExactSixStateC8SupportWitness
end MultipleLimit
end PermanssonResearch
