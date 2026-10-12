import PermanssonResearch.MultipleLimit.SharpFamilyExactGRBridge
import PermanssonResearch.MultipleLimit.ExactSixStateC3Witness
import PermanssonResearch.MultipleLimit.ExactSixStateStationaryCoordinates
import Mathlib.Tactic

/-!
# C56-04 — concrete typed six-state sharp-family witnesses

The genuine alpha -> P -> U model has two different recurrent physical
stationary measures. The fixed identity descriptor exposes both and
the existing nonconstant Boolean descriptor collapses both to one.
These are statements about ACTUAL class-selection laws, not arbitrary
rational reference vectors or an empirically identified world.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactSixStateSharpFamily

open PermanssonLean
open PermanssonLean.RegimeSpecification
open ReverseSolver.FiniteStrategicRealization
open ExactSixStateTyped
open ExactSixStateClassLaws
open ExactSixStateC3Witness
open ExactSixStateObservedGR
open FiniteCanonicalPath
open FiniteExactGRRecovery
open BasinFamily
open SharpObservedFamily
open SharpFamilyExactGRBridge

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

abbrev SixY := JointState Unit (Fin 6)
private noncomputable abbrev K := typedModel.inducedKernel

/-- Freeze the same genuine typed model, identity descriptor, original
proper region and two-point (u,a0) basin used in C3. -/
def identityFrozenFamily (ν : ProbabilityMeasure SixY) :
    FrozenBasinFamily K SixY :=
  frozenFamilyOfExactSpec typedModel (identitySpec ν)
    observedReference (identityAssumption41 ν) (identityExactlyInvariant ν)

/-- C3's proven positive-probability canonical class selector, followed
by the identity descriptor, gives actual stationary law πA as a sharp
observed-limit atom. -/
theorem identitySharp_contains_A (ν : ProbabilityMeasure SixY) :
    ExactSixStateClassLaws.πA ∈
      sharpObservedFamily K (identityFrozenFamily ν) := by
  classical
  have hA := (identity_classes_reachable ν).1
  exact Finset.mem_image.mpr
    ⟨rA, hA, identity_observed_A ν⟩

theorem identitySharp_contains_B (ν : ProbabilityMeasure SixY) :
    ExactSixStateClassLaws.πB ∈
      sharpObservedFamily K (identityFrozenFamily ν) := by
  classical
  have hB := (identity_classes_reachable ν).2
  exact Finset.mem_image.mpr
    ⟨rB, hB, identity_observed_B ν⟩

/-- Both positive canonical physical limits are genuinely distinct.
Hence the identity-sharp family cannot be a singleton for ANY proposed
original target. -/
theorem identitySharp_ne_any_singleton (ν : ProbabilityMeasure SixY) :
    sharpObservedFamily K (identityFrozenFamily ν) ≠
      ({ν} : Finset (ProbabilityMeasure SixY)) := by
  intro heq
  have hA := identitySharp_contains_A ν
  have hB := identitySharp_contains_B ν
  rw [heq] at hA hB
  have hA' : ExactSixStateClassLaws.πA = ν :=
    Finset.mem_singleton.mp hA
  have hB' : ExactSixStateClassLaws.πB = ν :=
    Finset.mem_singleton.mp hB
  exact πA_ne_πB (hA'.trans hB'.symm)

/-- The abstract C2 actual πA/πB have positive observed-limit
canonical atom witnesses in the original two-point basin, not just
separately guessed rational coefficients. -/
theorem identityA_positive_atom (ν : ProbabilityMeasure SixY) :
    ∃ y ∈ (identityFrozenFamily ν).basin,
      canonicalPathLaw K (Measure.dirac y)
        (observedAtomEvent K (identityFrozenFamily ν)
          ExactSixStateClassLaws.πA) ≠ 0 :=
  (mem_sharp_iff_positive_atom K (identityFrozenFamily ν)
    ExactSixStateClassLaws.πA).mp (identitySharp_contains_A ν)

theorem identityB_positive_atom (ν : ProbabilityMeasure SixY) :
    ∃ y ∈ (identityFrozenFamily ν).basin,
      canonicalPathLaw K (Measure.dirac y)
        (observedAtomEvent K (identityFrozenFamily ν)
          ExactSixStateClassLaws.πB) ≠ 0 :=
  (mem_sharp_iff_positive_atom K (identityFrozenFamily ν)
    ExactSixStateClassLaws.πB).mp (identitySharp_contains_B ν)

/-- Despite two different physical random occupation limits, the
predeclared Boolean descriptor of C2/C3 identifies them both with
a SINGLE observed limit. This uses the original positive Exact GR
proof and the conservative C5 bridge, not a new assumed limit. -/
theorem booleanSharp_eq_singleton :
    sharpObservedFamily K
      (frozenFamilyOfExactSpec typedModel observedSpec observedReference
        observedAssumption41 observedExactlyInvariant) =
      ({diracProba true} : Finset (ProbabilityMeasure Bool)) := by
  exact (exactGR_iff_sharp_singleton
    typedModel observedSpec observedReference
    observedAssumption41 observedExactlyInvariant rfl).mp
      observedExactGeneratedRegime

/-- The identity version still fails the ORIGINAL one-target Exact GR
definition, as C3 proved; a sharp multiple-limit family is not itself
an Exact GR certificate or a new constitutive PR certificate. -/
theorem identity_not_original_exactGR (ν : ProbabilityMeasure SixY) :
    ¬ IsExactGeneratedRegime typedModel
      (identitySpec ν) observedReference :=
  identity_no_exactGR_for_any_target ν

end
end ExactSixStateSharpFamily
end MultipleLimit
end PermanssonResearch
