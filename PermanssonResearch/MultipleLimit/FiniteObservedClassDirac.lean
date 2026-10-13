import PermanssonResearch.MultipleLimit.FiniteObservedClassSupport
import PermanssonResearch.MultipleLimit.ClassDescriptorSelectionLaw
import Mathlib.Tactic

/-!
# C8-03 — strict stationary class support and Boolean Dirac observation

For a genuine closed irreducible recurrent class, every class point has
positive actual stationary probability. Hence the observed stationary
law is exactly delta_true if and only if ALL class members have the
predeclared Boolean label true. Mixed observed class laws are allowed;
they are not silently replaced by a Dirac measure.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteObservedClassDirac

set_option autoImplicit false

open KernelCommunication
open RecurrentClassDecomposition
open CanonicalClassSelector
open ClassStationarySelectionLaw
open ClassDescriptorSelectionLaw
open FiniteObservedClassSupport
open FiniteKernelInvariantUniqueness

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [Nonempty Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- A finite recurrent class is all-true precisely when its genuine
stationary descriptor pushforward is the TRUE Dirac law. Strict point
support is essential for the forward direction. -/
theorem observed_stationary_trueDirac_iff_allTrue
    (h : Y → Bool) (i : Y)
    (hi : i ∈ recurrentRepresentatives K) :
    observedStationaryForClass K h i = diracProba true ↔
      AllTrueClass K h i := by
  classical
  have hrec : i ∈ RecurrentStates K := by
    have hf :
        i ∈ Finset.univ.filter
          (fun z => z ∈ RecurrentStates K ∧
            classRepresentative K z = z) := hi
    exact (Finset.mem_filter.mp hf).2.1
  let C : Set Y := CommunicatingClass K i
  let π : ProbabilityMeasure Y := stationaryForSet K C
  have hC : C ∈ RecurrentClasses K :=
    (recurrentClasses_mem_iff K _).mpr ⟨i, hrec, rfl⟩
  have hπC : π.toMeasure C = 1 :=
    (stationaryForSet_spec K hC).2
  have hh : Measurable h := measurable_of_finite h
  constructor
  · intro hdirac z hz
    by_contra hnot
    have hzFalse : h z = false := by
      cases hzLab : h z with
      | false => rfl
      | true => exact (hnot hzLab).elim
    have hnull : π.toMeasure (h ⁻¹' ({false} : Set Bool)) = 0 := by
      have hmass := congrArg
        (fun ν : ProbabilityMeasure Bool => ν.toMeasure ({false} : Set Bool))
        hdirac
      change (Measure.map h π.toMeasure) ({false} : Set Bool) =
        (Measure.dirac true : Measure Bool) ({false} : Set Bool) at hmass
      rw [Measure.map_apply hh (measurableSet_singleton false)] at hmass
      simpa using hmass
    have hsub : ({z} : Set Y) ⊆ h ⁻¹' ({false} : Set Bool) := by
      intro w hw
      have heq : w = z := by simpa using hw
      subst w
      simpa [hzFalse]
    have hzero : π.toMeasure ({z} : Set Y) = 0 :=
      measure_mono_null hsub hnull
    have hpositive := stationary_point_positive K i z hrec hz
    have hzeroReal :
        realPointMass (stationaryForSet K (CommunicatingClass K i)) z = 0 := by
      change (π.toMeasure ({z} : Set Y)).toReal = 0
      rw [hzero]
      rfl
    exact (ne_of_gt hpositive) hzeroReal
  · intro hgood
    have hsub : C ⊆ h ⁻¹' ({true} : Set Bool) := by
      intro z hz
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
        hgood z hz
    have htrue : π.toMeasure (h ⁻¹' ({true} : Set Bool)) = 1 := by
      apply le_antisymm
      · calc
          π.toMeasure (h ⁻¹' ({true} : Set Bool)) ≤
              π.toMeasure Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      · calc
          (1 : ℝ≥0∞) = π.toMeasure C := hπC.symm
          _ ≤ π.toMeasure (h ⁻¹' ({true} : Set Bool)) :=
            measure_mono hsub
    have htrueMap :
        (observedStationaryForClass K h i).toMeasure
          ({true} : Set Bool) = 1 := by
      change (Measure.map h π.toMeasure) ({true} : Set Bool) = 1
      rw [Measure.map_apply hh (measurableSet_singleton true)]
      exact htrue
    have hcomplement :
        (observedStationaryForClass K h i).toMeasure
          ({false} : Set Bool) = 0 := by
      have hc := prob_compl_eq_one_sub
        (μ := (observedStationaryForClass K h i).toMeasure)
        (measurableSet_singleton true)
      have hs : ({true} : Set Bool)ᶜ = ({false} : Set Bool) := by
        ext b
        cases b <;> decide
      rw [hs, htrueMap] at hc
      simpa using hc
    apply ProbabilityMeasure.toMeasure_injective
    apply Measure.ext_of_singleton
    intro b
    cases b with
    | false =>
      change (observedStationaryForClass K h i).toMeasure
        ({false} : Set Bool) =
          (Measure.dirac true : Measure Bool) ({false} : Set Bool)
      simpa using hcomplement
    | true =>
      change (observedStationaryForClass K h i).toMeasure
        ({true} : Set Bool) =
          (Measure.dirac true : Measure Bool) ({true} : Set Bool)
      simpa using htrueMap

end FiniteObservedClassDirac
end MultipleLimit
end PermanssonResearch
