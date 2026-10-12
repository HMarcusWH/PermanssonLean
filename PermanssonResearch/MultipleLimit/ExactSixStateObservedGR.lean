import PermanssonResearch.MultipleLimit.ExactSixStateRecurrentGeometry
import PermanssonResearch.MultipleLimit.FiniteExactGRRecovery
import PermanssonResearch.MultipleLimit.FiniteEventuallyObserved
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Tactic

/-!
# C53-11 — a proper-region exact Generated Regime with random physical classes

This concrete six-state alpha/P/U construction has two transient points
and two non-singleton closed recurrent classes, one periodic. The FROZEN
region excludes transient t; the basin contains u and a0; the
nonconstant declared Boolean descriptor sends both recurrent classes
to the same value true.

The actual canonical path almost surely reaches a recurrent state.
Consequently all original Exact GR gates hold: Assumption 4.1 (with a
genuine two-point basin), proper-region exact invariance, and a common
almost-sure observed occupation target δ_true for EVERY admissible initial
law. This is an Exact GR witness, not a constitutive PR witness.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactSixStateObservedGR

open PermanssonLean
open PermanssonLean.RegimeSpecification
open ReverseSolver.FiniteStrategicRealization
open ExactSixState
open ExactSixStateTyped
open ExactSixStateKernelRegion
open ExactSixStateRecurrentGeometry
open FiniteEventuallyObserved
open FiniteExactGRRecovery

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

abbrev SixY := JointState Unit (Fin 6)

def observedBasin : Set SixY :=
  {decode (1 : Fin 6), decode (2 : Fin 6)}

def observedDescriptor (y : SixY) : Bool :=
  observedRecurrent (encode y)

theorem observedBasin_subset_region :
    observedBasin ⊆ typedRegion := by
  intro y hy
  change y = decode (1 : Fin 6) ∨ y = decode (2 : Fin 6) at hy
  rcases hy with rfl | rfl <;>
    norm_num [typedRegion, ExactSixStateRegion.region, encode, decode]

def observedSpec : RegimeSpecification SixY Bool where
  region := typedRegion
  region_measurable := typed_region_measurable
  basin := observedBasin
  basin_measurable := (Set.toFinite observedBasin).measurableSet
  basin_subset_region := observedBasin_subset_region
  descriptor := observedDescriptor
  descriptor_measurable := Measurable.of_discrete
  target := diracProba true
  convergenceMode := ConvergenceMode.almostSureWeak SixY Bool

def observedReference : Measure SixY := Measure.count

theorem observedAssumption41 :
    Assumption41 typedModel observedSpec observedReference := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨decode (1 : Fin 6), by simp [observedSpec, observedBasin]⟩
  · right
    have hsub : ({decode (1 : Fin 6)} : Set SixY) ⊆ typedRegion := by
      intro y hy
      have h : y = decode (1 : Fin 6) := Set.mem_singleton_iff.mp hy
      subst y
      simp [typedRegion, ExactSixStateRegion.region, decode, encode]
    change 0 < observedReference typedRegion
    calc
      0 < Measure.count ({decode (1 : Fin 6)} : Set SixY) := by simp
      _ ≤ observedReference typedRegion := measure_mono hsub
  · refine ⟨decode (1 : Fin 6), ?_,
      decode (2 : Fin 6), ?_, ?_⟩
    · simp [observedSpec, typedRegion, ExactSixStateRegion.region,
        decode, encode]
    · simp [observedSpec, typedRegion, ExactSixStateRegion.region,
        decode, encode]
    · decide
  · apply two_states_implies_basinPathLawNontrivial typedModel observedSpec
    refine ⟨decode (1 : Fin 6), ?_,
      decode (2 : Fin 6), ?_, ?_⟩
    · simp [observedSpec, observedBasin]
    · simp [observedSpec, observedBasin]
    · decide

theorem observedExactlyInvariant :
    IsExactlyInvariant typedModel observedSpec := by
  intro y hy
  exact typedRegion_kernel_mass_one y

/-- At EVERY finite positive horizon, the ORIGINAL frozen occupation
formula is precisely the pushforward of the true physical empirical law
under the declared nonconstant six-state observation. -/
theorem observedEmpirical_eq_original_map
    (w : ℕ → SixY) (T : ℕ) (hT : 0 < T) :
    RegimeSpecification.empiricalOccupation observedSpec w T hT =
      FiniteEventuallyObserved.observedEmpirical
        observedDescriptor w T hT := by
  rw [original_empirical_eq_physical_map]
  rfl

/-- All four original Exact GR gates hold on the actual typed six-state
infinite path law. The transient u belongs to the proper basin and keeps
the descriptor nonconstant on the proper region. Physical A/B class
occupations remain distinct and random; only their observation collapses.
No intervention-relative PR status follows from this theorem. -/
theorem observedExactGeneratedRegime :
    IsExactGeneratedRegime typedModel observedSpec observedReference := by
  refine ⟨canonicalProcessWellPosed typedModel,
    observedAssumption41, observedExactlyInvariant, ?_⟩
  intro μ hμ
  unfold IsLimitingOccupationLaw
  change ∀ᵐ w ∂typedModel.pathLaw μ.toMeasure,
    Tendsto (fun n : ℕ =>
      RegimeSpecification.empiricalOccupation observedSpec w
        (n+1) (Nat.succ_pos n))
      atTop (𝓝 (diracProba true))
  rw [FiniteCanonicalPath.typed_pathLaw_eq_canonical typedModel μ.toMeasure]
  have hrec : ∀ y ∈
      RecurrentClassDecomposition.RecurrentStates typedModel.inducedKernel,
      observedDescriptor y = true := by
    intro y hy
    exact recurrent_observed_true y hy
  filter_upwards
    [canonical_observed_occupation_ae_true
      typedModel.inducedKernel observedDescriptor hrec μ]
    with w hw
  simpa only [observedEmpirical_eq_original_map] using hw

end
end ExactSixStateObservedGR
end MultipleLimit
end PermanssonResearch
