import PermanssonResearch.MultipleLimit.ExactSixStateConstitution
import PermanssonResearch.MultipleLimit.SharpObservedFamily
import PermanssonResearch.MultipleLimit.ExactSixStateSharpFamily
import PermanssonResearch.MultipleLimit.FiniteExactGRRecovery
import PermanssonResearch.MultipleLimit.FiniteObservedLimitUniqueness
import Mathlib.Tactic

/-!
# C6 — changed ACTUAL C5 observed-limit family under a typed intervention

The baseline and the intervened model use the SAME descriptor, basin,
and proper region. An independent intervened-chain proof shows that its
canonical empirical observed occupation converges to delta_false under
each original basin point. Thus the intervened sharp family is exactly
{delta_false}, as opposed to baseline {delta_true}. The proof does NOT
evaluate a baseline-K class selector on the intervened K.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace SharpFamilyResponseWitness

open PermanssonLean
open PermanssonLean.RegimeSpecification
open ReverseSolver.FiniteStrategicRealization
open ExactSixStateTyped
open ExactSixStateObservedGR
open ExactSixStateTargetDisruption
open ExactSixStateConstitution
open TypedEventResponse
open FrozenObservedEvent
open BasinFamily
open SharpObservedFamily
open FiniteEventuallyObserved
open FiniteOccupationRandomLaw
open FiniteObservedLimitUniqueness
open FiniteCanonicalPath

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

-- Reject misspelled or out-of-scope declarations instead of inventing implicit binders.
set_option autoImplicit false

abbrev SixY := JointState Unit (Fin 6)
private noncomputable abbrev Kd := disruptedModel.inducedKernel

/-- Use the SAME original proper region, basin, and descriptor after
changing the action-selection kernel. Region closure must be reproved. -/
def disruptedFamily : FrozenBasinFamily Kd Bool where
  region := observedSpec.region
  basin := observedSpec.basin
  basin_nonempty := observedAssumption41.1
  basin_subset_region := observedSpec.basin_subset_region
  region_closed := disrupted_region_closed
  descriptor := observedDescriptor
  descriptor_measurable := observedSpec.descriptor_measurable

/-- Finite-horizon occupation of a path which is eventually CONSTANT
at an arbitrary Boolean label. The existing C2 true-only lemma does
not require changing; this is a proof over the same original empirical
process, now specialized to either possible frozen label. -/
theorem observedEmpirical_tendsto_label_of_eventually
    (h : SixY → Bool) (w : ℕ → SixY) (b : Bool)
    (hE : ∃ N : ℕ, ∀ n ≥ N, h (w n) = b) :
    Tendsto (fun n : ℕ =>
      observedEmpirical h w (n+1) (Nat.succ_pos n))
      atTop (𝓝 (diracProba b)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  change Tendsto
    (fun n : ℕ => ∫ z, f z ∂observedEmpirical h w
      (n+1) (Nat.succ_pos n))
    atTop (𝓝 (∫ z, f z ∂(Measure.dirac b)))
  simp only [integral_dirac]
  obtain ⟨N,hN⟩ := hE
  have heq : (fun n : ℕ => f (h (w n))) =ᶠ[atTop]
      (fun _ : ℕ => f b) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [hN n hn]
  have hp : Tendsto (fun n : ℕ => f (h (w n)))
      atTop (𝓝 (f b)) :=
    tendsto_const_nhds.congr' heq.symm
  have hces := hp.cesaro
  have hidx : Tendsto (fun n : ℕ => n+1) atTop atTop := by
    apply tendsto_atTop.2
    intro t
    filter_upwards [eventually_ge_atTop t] with n hn
    omega
  have hshift := hces.comp hidx
  simpa only [observedEmpirical_integral_eq_average,
    Function.comp_def] using hshift

/-- On the authentic intervened infinite path, C2's selected observed
occupation limit equals delta_false almost surely from BOTH original
basin points. No recurrent-class identity is assumed from the baseline. -/
theorem point_observed_limit_false (i : Fin 6)
    (hi : i = 1 ∨ i = 2) :
    ∀ᵐ w ∂canonicalPathLaw Kd (Measure.dirac (decode i)),
      observedOccupationLimit Kd observedDescriptor w =
        diracProba false := by
  have hC2 := observedOccupationLimit_ae_correct Kd
    (diracProba (decode i)) observedDescriptor
  filter_upwards [eventually_false_ae i hi, hC2]
    with w hfalse hlim
  have hpath :
      Tendsto (fun n : ℕ =>
        (FiniteStateOccupation.empiricalOccupation w
          (n+1) (Nat.succ_pos n)).map observedDescriptor)
          atTop (𝓝 (diracProba false)) := by
    change Tendsto (fun n : ℕ =>
      observedEmpirical observedDescriptor w
        (n+1) (Nat.succ_pos n))
      atTop (𝓝 (diracProba false))
    exact observedEmpirical_tendsto_label_of_eventually
      observedDescriptor w false hfalse
  haveI : T2Space (ProbabilityMeasure Bool) := inferInstance
  exact tendsto_nhds_unique hlim hpath

/-- No other observed atom has positive canonical probability from
either frozen basin start of the actual perturbed model. -/
theorem disrupted_sharp_subset_false :
    sharpObservedFamily Kd disruptedFamily ⊆
      ({diracProba false} : Finset (ProbabilityMeasure Bool)) := by
  classical
  intro ν hν
  have hwitness := (mem_sharp_iff_positive_atom Kd disruptedFamily ν).mp hν
  obtain ⟨y, hy, hpositive⟩ := hwitness
  have hy' : y = decode (1 : Fin 6) ∨
      y = decode (2 : Fin 6) := by
    simpa [disruptedFamily, observedSpec, observedBasin] using hy
  obtain ⟨i, hi, hstart⟩ :
      ∃ i : Fin 6, (i = 1 ∨ i = 2) ∧ y = decode i := by
    rcases hy' with h | h
    · exact ⟨1, Or.inl rfl, h⟩
    · exact ⟨2, Or.inr rfl, h⟩
  subst y
  have hAE := point_observed_limit_false i hi
  rw [ae_iff] at hAE
  have hnull :
      canonicalPathLaw Kd (Measure.dirac (decode i))
        {w : ℕ → SixY |
          observedOccupationLimit Kd observedDescriptor w ≠
            diracProba false} = 0 := by
    change canonicalPathLaw Kd (Measure.dirac (decode i))
      {w : ℕ → SixY |
        observedOccupationLimit Kd observedDescriptor w ≠
          diracProba false} = 0 at hAE
    exact hAE
  by_contra hnot
  have hne : ν ≠ diracProba false := by
    simpa only [Finset.mem_singleton] using hnot
  have hsubset :
      observedAtomEvent Kd disruptedFamily ν ⊆
        {w : ℕ → SixY |
          observedOccupationLimit Kd observedDescriptor w ≠
            diracProba false} := by
    intro w hw
    change ClassDescriptorSelectionLaw.observedStationaryForClass Kd observedDescriptor
      (CanonicalClassSelector.selectedRepresentative Kd w) = ν at hw
    change observedOccupationLimit Kd observedDescriptor w ≠
      diracProba false
    rw [show observedOccupationLimit Kd observedDescriptor w =
        ClassDescriptorSelectionLaw.observedStationaryForClass Kd observedDescriptor
          (CanonicalClassSelector.selectedRepresentative Kd w) from rfl, hw]
    exact hne
  exact hpositive (measure_mono_null hsubset hnull)

/-- The actual intervened C5 positive-atom family is exactly the singleton
delta_false, not the baseline's delta_true. -/
theorem disrupted_sharp_eq_false :
    sharpObservedFamily Kd disruptedFamily =
      ({diracProba false} : Finset (ProbabilityMeasure Bool)) := by
  classical
  have hsubset := disrupted_sharp_subset_false
  obtain ⟨ν,hν⟩ := sharpObservedFamily_nonempty Kd disruptedFamily
  have heq : ν = diracProba false :=
    Finset.mem_singleton.mp (hsubset hν)
  have hfalse : diracProba false ∈
      sharpObservedFamily Kd disruptedFamily := by
    rwa [heq] at hν
  apply Finset.ext
  intro ξ
  constructor
  · exact fun h => hsubset h
  · intro h
    have hξ : ξ = diracProba false := Finset.mem_singleton.mp h
    simpa [hξ] using hfalse

/-- C5's previously verified baseline sharp observed family. -/
theorem baseline_sharp_eq_true :
    sharpObservedFamily typedModel.inducedKernel
      (FiniteExactGRRecovery.frozenFamilyOfExactSpec typedModel observedSpec observedReference
        observedAssumption41 observedExactlyInvariant) =
        ({diracProba true} : Finset (ProbabilityMeasure Bool)) :=
  ExactSixStateSharpFamily.booleanSharp_eq_singleton

/-- Actual typed strategic control causes a provable observed-regime
family change, unlike the physically different but observationally
equivalent class-A-versus-class-B selection from C5. -/
theorem sharp_observed_family_changes :
    sharpObservedFamily Kd disruptedFamily ≠
      sharpObservedFamily typedModel.inducedKernel
        (FiniteExactGRRecovery.frozenFamilyOfExactSpec typedModel observedSpec observedReference
          observedAssumption41 observedExactlyInvariant) := by
  rw [disrupted_sharp_eq_false, baseline_sharp_eq_true]
  intro heq
  have hmem :
      diracProba false ∈ ({diracProba true} :
        Finset (ProbabilityMeasure Bool)) := by
    rw [← heq]
    simp
  have hneq : diracProba false ≠
      (diracProba true : ProbabilityMeasure Bool) := by
    intro h
    have hm : (Measure.dirac false : Measure Bool) =
      Measure.dirac true :=
      congrArg (fun ν : ProbabilityMeasure Bool => ν.toMeasure) h
    have hneq : (false : Bool) ≠ true := by decide
    exact hneq (MeasureTheory.dirac_eq_dirac_iff.mp hm)
  exact hneq (Finset.mem_singleton.mp hmem)

/-- Under the unchanged target delta_true, the intervened model fails
the original Exact GR occupation requirement from its original u basin.
This is stronger than merely changing some strategic effect score. -/
theorem intervened_not_original_exactGR :
    ¬ IsExactGeneratedRegime disruptedModel observedSpec observedReference := by
  intro hGR
  have hbasin :
      u ∈ observedSpec.basin := by
    simp [observedSpec, observedBasin, u, decode]
  have hadmiss :
      IsAdmissibleInitialLaw observedSpec (diracProba u) :=
    (dirac_admissible_iff observedSpec u).2 hbasin
  have hlim := exactGR_observedOccupationLimit_ae
    disruptedModel observedSpec observedReference hGR rfl
    (diracProba u) hadmiss
  have hfalse :
      ∀ᵐ w ∂canonicalPathLaw Kd (Measure.dirac u),
        observedOccupationLimit Kd observedDescriptor w =
          diracProba false := by
    simpa only [u] using
      (point_observed_limit_false (1 : Fin 6) (Or.inl rfl))
  change ∀ᵐ w ∂canonicalPathLaw Kd (Measure.dirac u),
    observedOccupationLimit Kd observedDescriptor w =
      diracProba true at hlim
  obtain ⟨w, htrue, hfalse⟩ := (hlim.and hfalse).exists
  have hneq : diracProba false ≠
      (diracProba true : ProbabilityMeasure Bool) := by
    intro h
    have hm : (Measure.dirac false : Measure Bool) =
      Measure.dirac true :=
      congrArg (fun ν : ProbabilityMeasure Bool => ν.toMeasure) h
    have hneq : (false : Bool) ≠ true := by decide
    exact hneq (MeasureTheory.dirac_eq_dirac_iff.mp hm)
  exact hneq (hfalse.symm.trans htrue)

end
end SharpFamilyResponseWitness
end MultipleLimit
end PermanssonResearch
