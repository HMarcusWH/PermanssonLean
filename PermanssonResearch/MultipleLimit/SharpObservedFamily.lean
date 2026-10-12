import PermanssonResearch.MultipleLimit.FiniteBasinClassification
import Mathlib.Tactic

/-!
# C56-01/02 — sharp positive-atom families of observed finite-chain limits

C2 already proves that the *canonical* observed occupation limit is the
almost-sure limit of the actual empirical occupations and computes its
complete measure-valued law. This module does NOT reprove ergodicity.

The new claim is that the ex-ante basin-reachable stationary-descriptor
image is EXACTLY the family of atoms with positive canonical path
probability from at least one point in the basin. This also provides a
sharp/nonvacuous finite-family coverage criterion.

The atom event is defined on the original canonical path space through
the finite-valued recurrent-class selector. Its measurability does NOT
assume arbitrary singletons in ProbabilityMeasure H are measurable.
It does not assert uniqueness of every possible weak limit in a
non-Hausdorff topology.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace SharpObservedFamily

open FiniteCanonicalPath
open KernelCommunication
open RecurrentClassDecomposition
open CanonicalClassSelector
open CanonicalClassWeights
open BasinFamily
open FiniteBasinClassification
open ClassDescriptorSelectionLaw
open FiniteOccupationRandomLaw

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [Nonempty Y] [DecidableEq Y]
variable [TopologicalSpace Y] [DiscreteTopology Y]
variable [OpensMeasurableSpace Y] [StandardBorelSpace Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]
variable {H : Type*} [MeasurableSpace H] [TopologicalSpace H]
variable [BorelSpace H]
variable (F : FrozenBasinFamily K H)

/-- The exact finite family of observed stationary laws from recurrent
classes with positive ACTUAL probability of basin selection. Duplicate
observed class laws occur only once in this finite image. -/
noncomputable def sharpObservedFamily : Finset (ProbabilityMeasure H) := by
  classical
  exact (reachableRepresentatives K H F).image
    (observedStationaryForClass K F.descriptor)

/-- Every nonempty registered basin has at least one attainable
observed limit. It is a statement about actual canonical selection. -/
theorem sharpObservedFamily_nonempty :
    (sharpObservedFamily K F).Nonempty := by
  classical
  obtain ⟨i, hi⟩ := reachableRepresentatives_nonempty K H F
  exact ⟨observedStationaryForClass K F.descriptor i,
    Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩

/-- This is the canonical measured path event, not a post-hoc topological
support assertion about a probability-measure space. -/
def observedFamilyEvent (V : Set (ProbabilityMeasure H)) :
    Set (ℕ → Y) :=
  {w | observedStationaryForClass K F.descriptor
    (selectedRepresentative K w) ∈ V}

def observedAtomEvent (ν : ProbabilityMeasure H) : Set (ℕ → Y) :=
  observedFamilyEvent K F {ν}

/-- Even when the measurable structure on ProbabilityMeasure H does NOT
have measurable singletons, these events are measurable: they are
preimages of finite subsets of Y under the genuine measurable selector. -/
theorem observedFamilyEvent_measurable
    (V : Set (ProbabilityMeasure H)) :
    MeasurableSet (observedFamilyEvent K F V) := by
  change MeasurableSet ((selectedRepresentative K) ⁻¹'
    {i : Y | observedStationaryForClass K F.descriptor i ∈ V})
  exact ((Set.toFinite
    {i : Y | observedStationaryForClass K F.descriptor i ∈ V}).measurableSet).preimage
      (selectedRepresentative_measurable K)

theorem observedAtomEvent_measurable (ν : ProbabilityMeasure H) :
    MeasurableSet (observedAtomEvent K F ν) :=
  observedFamilyEvent_measurable K F {ν}

/-- Every basin point gives a supported Dirac probability measure,
without assuming the whole basin is a singleton or has two elements. -/
private theorem point_basin_mass
    (y : Y) (hy : y ∈ F.basin) :
    (diracProba y).toMeasure F.basin = 1 := by
  have hmeas : MeasurableSet F.basin :=
    (Set.toFinite F.basin).measurableSet
  rw [diracProba_toMeasure_apply' y hmeas]
  simp [hy]

/-- Every prescribed member of a candidate family must cover the
actual canonical selected observed law, for ALL basin-supported
initial laws. No statement is made about every exceptional null path. -/
def Covers (V : Finset (ProbabilityMeasure H)) : Prop :=
  ∀ μ : ProbabilityMeasure Y, μ.toMeasure F.basin = 1 →
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      observedStationaryForClass K F.descriptor
        (selectedRepresentative K w) ∈ V

/-- A finite family covers all canonical observed limits for every
basin-supported initial distribution IFF it contains every sharp
positive-probability atom. This uses actual class selection, not
finite-horizon graph sampling or a uniform minimum weight. -/
theorem covers_iff_sharp_subset
    (V : Finset (ProbabilityMeasure H)) :
    Covers K F V ↔ sharpObservedFamily K F ⊆ V := by
  classical
  constructor
  · intro hcover ν hν
    obtain ⟨i, hi, hiν⟩ := Finset.mem_image.mp hν
    obtain ⟨_, y, hy, hpos⟩ := Finset.mem_filter.mp hi
    have hAE := hcover (diracProba y) (point_basin_mass K F y hy)
    rw [ae_iff] at hAE
    by_contra hnot
    have hsubset :
        (selectedRepresentative K) ⁻¹' ({i} : Set Y) ⊆
          {w : ℕ → Y | ¬ observedStationaryForClass K F.descriptor
            (selectedRepresentative K w) ∈ V} := by
      intro w hw
      have hs : selectedRepresentative K w = i := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hw
      change ¬ observedStationaryForClass K F.descriptor
        (selectedRepresentative K w) ∈ V
      rw [hs, hiν]
      exact hnot
    exact hpos (measure_mono_null hsubset hAE)
  · intro hsubset μ hμ
    filter_upwards [selected_reachable_family_ae K F μ hμ] with w hw
    apply hsubset
    exact Finset.mem_image.mpr
      ⟨selectedRepresentative K w, hw, rfl⟩

/-- The headline sharpness theorem: a canonical observed limiting law
belongs to the frozen family exactly when it occurs with NONZERO
probability from some registered basin point. Class probabilities may
be arbitrarily small; there is no cutoff. -/
theorem mem_sharp_iff_positive_atom
    (ν : ProbabilityMeasure H) :
    ν ∈ sharpObservedFamily K F ↔
      ∃ y ∈ F.basin,
        canonicalPathLaw K (Measure.dirac y)
          (observedAtomEvent K F ν) ≠ 0 := by
  classical
  constructor
  · intro hν
    obtain ⟨i, hi, hiν⟩ := Finset.mem_image.mp hν
    obtain ⟨_, y, hy, hpos⟩ := Finset.mem_filter.mp hi
    refine ⟨y, hy, ?_⟩
    intro hzero
    have hsubset :
        (selectedRepresentative K) ⁻¹' ({i} : Set Y) ⊆
          observedAtomEvent K F ν := by
      intro w hw
      have hs : selectedRepresentative K w = i := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hw
      change observedStationaryForClass K F.descriptor
        (selectedRepresentative K w) = ν
      rw [hs]
      exact hiν
    exact hpos (measure_mono_null hsubset hzero)
  · rintro ⟨y, hy, hpos⟩
    have hcover : Covers K F (sharpObservedFamily K F) :=
      (covers_iff_sharp_subset K F (sharpObservedFamily K F)).mpr
        (by intro ξ hξ; exact hξ)
    have hAE := hcover (diracProba y) (point_basin_mass K F y hy)
    rw [ae_iff] at hAE
    by_contra hnot
    have hsubset :
        observedAtomEvent K F ν ⊆
          {w : ℕ → Y | ¬ observedStationaryForClass K F.descriptor
            (selectedRepresentative K w) ∈ sharpObservedFamily K F} := by
      intro w hw
      change observedStationaryForClass K F.descriptor
        (selectedRepresentative K w) = ν at hw
      change ¬ observedStationaryForClass K F.descriptor
        (selectedRepresentative K w) ∈ sharpObservedFamily K F
      rw [hw]
      exact hnot
    exact hpos (measure_mono_null hsubset hAE)

/-- A finite family is sharp only if each of its own claimed atoms has
a positive-probability canonical witness from the frozen basin. -/
def NoSpuriousAtoms (V : Finset (ProbabilityMeasure H)) : Prop :=
  ∀ ν ∈ V, ∃ y ∈ F.basin,
    canonicalPathLaw K (Measure.dirac y)
      (observedAtomEvent K F ν) ≠ 0

/-- Main C5 certificate. Mere coverage accepts arbitrary supersets.
Coverage PLUS no-spurious-atoms is exactly the unique sharp family. -/
theorem covers_and_noSpurious_iff_eq_sharp
    (V : Finset (ProbabilityMeasure H)) :
    (Covers K F V ∧ NoSpuriousAtoms K F V) ↔
      V = sharpObservedFamily K F := by
  classical
  constructor
  · rintro ⟨hcover, hpositive⟩
    apply Finset.ext
    intro ν
    constructor
    · intro hν
      exact (mem_sharp_iff_positive_atom K F ν).mpr
        (hpositive ν hν)
    · intro hν
      exact (covers_iff_sharp_subset K F V).mp hcover hν
  · intro heq
    subst V
    constructor
    · exact (covers_iff_sharp_subset K F (sharpObservedFamily K F)).mpr
        (by intro ν hν; exact hν)
    · intro ν hν
      exact (mem_sharp_iff_positive_atom K F ν).mp hν

end SharpObservedFamily
end MultipleLimit
end PermanssonResearch
