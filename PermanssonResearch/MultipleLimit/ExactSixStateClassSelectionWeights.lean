import PermanssonResearch.MultipleLimit.ExactSixStateInfiniteWeights
import PermanssonResearch.MultipleLimit.ExactSixStateRecurrentGeometry
import PermanssonResearch.MultipleLimit.CanonicalClassWeights
import Mathlib.Tactic

/-!
# C53-15 — identify genuine class selection, not merely class hitting

The exact infinite-horizon 1/3–2/3 class-hitting laws become class
DESTINATION probabilities only after a genuine canonical-a.s. proof:
visits to closed classes cannot subsequently exit, and the selector
is proved to represent the unique eventual recurrent class.

Here the two six-state physical recurrent blocks are proved
graph-closed using the original typed kernel's nonzero atoms.
No assumption of IID trials or of class occupation ergodicity is used.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactSixStateClassSelectionWeights

open PermanssonLean
open ReverseSolver.FiniteStrategicRealization
open ExactSixState
open ExactSixStateTyped
open ExactSixStateRecurrentGeometry
open ExactSixStateEndpointEvents
open ExactSixStateInfiniteWeights
open KernelCommunication
open RecurrentClassDecomposition
open CanonicalClassSelector
open CanonicalClassWeights
open CanonicalClassContinuation
open FiniteCanonicalPath

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

abbrev SixY := JointState Unit (Fin 6)

def classASet : Set SixY := encode ⁻¹' classA
def classBSet : Set SixY := encode ⁻¹' classB

theorem classASet_closed :
    ClosedSubset typedModel.inducedKernel classASet := by
  intro y hy z hed
  rcases y with ⟨u, i⟩
  rcases z with ⟨v, j⟩
  cases u
  cases v
  change 0 < typedModel.inducedKernel (decode i)
    ({decode j} : Set SixY) at hed
  rw [typed_six_state_atom] at hed
  fin_cases i <;> fin_cases j <;>
    norm_num [classASet, classA, encode, transition] at *

theorem classBSet_closed :
    ClosedSubset typedModel.inducedKernel classBSet := by
  intro y hy z hed
  rcases y with ⟨u, i⟩
  rcases z with ⟨v, j⟩
  cases u
  cases v
  change 0 < typedModel.inducedKernel (decode i)
    ({decode j} : Set SixY) at hed
  rw [typed_six_state_atom] at hed
  fin_cases i <;> fin_cases j <;>
    norm_num [classBSet, classB, encode, transition] at *

/-- A generic closed recurrent target can be visited at any random time
iff the CANONICAL eventual class selector belongs to that closed target,
almost surely. Both directions use true Markov path results. -/
theorem selected_in_closed_iff_ever_hit_ae
    (C : Set SixY)
    (hclosed : ClosedSubset typedModel.inducedKernel C)
    (μ : ProbabilityMeasure SixY) :
    ∀ᵐ w ∂canonicalPathLaw typedModel.inducedKernel μ.toMeasure,
      ((selectedRepresentative typedModel.inducedKernel w ∈ C) ↔
        ∃ n : ℕ, w n ∈ C) := by
  filter_upwards
    [selected_class_eventual_ae typedModel.inducedKernel μ,
     closed_stay_after_entry_ae typedModel.inducedKernel μ C hclosed]
    with w hsel hstay
  constructor
  · intro hs
    obtain ⟨N,hN⟩ := hsel
    have hreach : Reachable typedModel.inducedKernel
      (selectedRepresentative typedModel.inducedKernel w) (w N) :=
      (hN N le_rfl).1
    exact ⟨N, closed_reachable typedModel.inducedKernel hclosed hs hreach⟩
  · rintro ⟨n,hn⟩
    obtain ⟨N,hN⟩ := hsel
    let m := max n N
    have hA : w m ∈ C := hstay n hn m (Nat.le_max_left _ _)
    have hback : Reachable typedModel.inducedKernel
        (w m) (selectedRepresentative typedModel.inducedKernel w) :=
      (hN m (Nat.le_max_right _ _)).2
    exact closed_reachable typedModel.inducedKernel hclosed hA hback

/-- Under a point start at u the canonical selected recurrent class is
physically A with probability EXACTLY 1/3, not merely 1/3 as a
reference-matrix harmonic candidate. -/
theorem selected_A_weight_u :
    typedModel.pathLaw (Measure.dirac (decode (1 : Fin 6)))
      ((selectedRepresentative typedModel.inducedKernel) ⁻¹' classASet) =
        ENNReal.ofReal (1/3 : ℝ) := by
  let P := typedModel.pathLaw (Measure.dirac (decode (1 : Fin 6)))
  have hsel :
      {w : ℕ → SixY |
        selectedRepresentative typedModel.inducedKernel w ∈ classASet}
        =ᵐ[P]
      {w : ℕ → SixY | ∃ n : ℕ, w n ∈ classASet} := by
    change
      _ =ᵐ[canonicalPathLaw typedModel.inducedKernel
        (Measure.dirac (decode (1 : Fin 6)))] _
    filter_upwards [selected_in_closed_iff_ever_hit_ae
      classASet classASet_closed (diracProba (decode (1 : Fin 6)))]
      with w hw
    exact propext hw
  have hhit :
      {w : ℕ → SixY | ∃ n : ℕ, w n ∈ classASet} =
        ⋃ T : ℕ, hitA T := by
    rw [union_hitA]
    rfl
  calc
    P ((selectedRepresentative typedModel.inducedKernel) ⁻¹' classASet) =
      P {w : ℕ → SixY | ∃ n : ℕ, w n ∈ classASet} :=
        measure_congr hsel
    _ = P (⋃ T : ℕ, hitA T) := congrArg P hhit
    _ = ENNReal.ofReal (1/3 : ℝ) := ever_hit_A_u

theorem selected_B_weight_u :
    typedModel.pathLaw (Measure.dirac (decode (1 : Fin 6)))
      ((selectedRepresentative typedModel.inducedKernel) ⁻¹' classBSet) =
        ENNReal.ofReal (2/3 : ℝ) := by
  let P := typedModel.pathLaw (Measure.dirac (decode (1 : Fin 6)))
  have hsel :
      {w : ℕ → SixY |
        selectedRepresentative typedModel.inducedKernel w ∈ classBSet}
        =ᵐ[P]
      {w : ℕ → SixY | ∃ n : ℕ, w n ∈ classBSet} := by
    change
      _ =ᵐ[canonicalPathLaw typedModel.inducedKernel
        (Measure.dirac (decode (1 : Fin 6)))] _
    filter_upwards [selected_in_closed_iff_ever_hit_ae
      classBSet classBSet_closed (diracProba (decode (1 : Fin 6)))]
      with w hw
    exact propext hw
  have hhit :
      {w : ℕ → SixY | ∃ n : ℕ, w n ∈ classBSet} =
        ⋃ T : ℕ, hitB T := by
    rw [union_hitB]
    rfl
  calc
    P ((selectedRepresentative typedModel.inducedKernel) ⁻¹' classBSet) =
      P {w : ℕ → SixY | ∃ n : ℕ, w n ∈ classBSet} :=
        measure_congr hsel
    _ = P (⋃ T : ℕ, hitB T) := congrArg P hhit
    _ = ENNReal.ofReal (2/3 : ℝ) := ever_hit_B_u

theorem selected_A_weight_t :
    typedModel.pathLaw (Measure.dirac (decode (0 : Fin 6)))
      ((selectedRepresentative typedModel.inducedKernel) ⁻¹' classASet) =
        ENNReal.ofReal (1/3 : ℝ) := by
  let P := typedModel.pathLaw (Measure.dirac (decode (0 : Fin 6)))
  have hsel :
      {w : ℕ → SixY |
        selectedRepresentative typedModel.inducedKernel w ∈ classASet}
        =ᵐ[P]
      {w : ℕ → SixY | ∃ n : ℕ, w n ∈ classASet} := by
    change
      _ =ᵐ[canonicalPathLaw typedModel.inducedKernel
        (Measure.dirac (decode (0 : Fin 6)))] _
    filter_upwards [selected_in_closed_iff_ever_hit_ae
      classASet classASet_closed (diracProba (decode (0 : Fin 6)))]
      with w hw
    exact propext hw
  have hhit :
      {w : ℕ → SixY | ∃ n : ℕ, w n ∈ classASet} =
        ⋃ T : ℕ, hitA T := by
    rw [union_hitA]
    rfl
  calc
    P ((selectedRepresentative typedModel.inducedKernel) ⁻¹' classASet) =
      P {w : ℕ → SixY | ∃ n : ℕ, w n ∈ classASet} :=
        measure_congr hsel
    _ = P (⋃ T : ℕ, hitA T) := congrArg P hhit
    _ = ENNReal.ofReal (1/3 : ℝ) := ever_hit_A_t

theorem selected_B_weight_t :
    typedModel.pathLaw (Measure.dirac (decode (0 : Fin 6)))
      ((selectedRepresentative typedModel.inducedKernel) ⁻¹' classBSet) =
        ENNReal.ofReal (2/3 : ℝ) := by
  let P := typedModel.pathLaw (Measure.dirac (decode (0 : Fin 6)))
  have hsel :
      {w : ℕ → SixY |
        selectedRepresentative typedModel.inducedKernel w ∈ classBSet}
        =ᵐ[P]
      {w : ℕ → SixY | ∃ n : ℕ, w n ∈ classBSet} := by
    change
      _ =ᵐ[canonicalPathLaw typedModel.inducedKernel
        (Measure.dirac (decode (0 : Fin 6)))] _
    filter_upwards [selected_in_closed_iff_ever_hit_ae
      classBSet classBSet_closed (diracProba (decode (0 : Fin 6)))]
      with w hw
    exact propext hw
  have hhit :
      {w : ℕ → SixY | ∃ n : ℕ, w n ∈ classBSet} =
        ⋃ T : ℕ, hitB T := by
    rw [union_hitB]
    rfl
  calc
    P ((selectedRepresentative typedModel.inducedKernel) ⁻¹' classBSet) =
      P {w : ℕ → SixY | ∃ n : ℕ, w n ∈ classBSet} :=
        measure_congr hsel
    _ = P (⋃ T : ℕ, hitB T) := congrArg P hhit
    _ = ENNReal.ofReal (2/3 : ℝ) := ever_hit_B_t

/-- All canonical selected class representatives live in exactly one
of the two physical recurrent blocks, EVEN on null exceptional paths:
the selector's fallback was chosen recurrent, and t/u are not recurrent. -/
theorem selected_in_A_or_B (w : ℕ → SixY) :
    selectedRepresentative typedModel.inducedKernel w ∈ classASet ∨
      selectedRepresentative typedModel.inducedKernel w ∈ classBSet := by
  let z := selectedRepresentative typedModel.inducedKernel w
  have hrec : z ∈ RecurrentStates typedModel.inducedKernel :=
    selectedRepresentative_recurrent typedModel.inducedKernel w
  have hnonzero : encode z ≠ (0 : Fin 6) := by
    intro h
    have hz : z = decode (0 : Fin 6) := by
      calc
        z = decode (encode z) := (decode_encode z).symm
        _ = decode 0 := congrArg decode h
    exact t_is_not_recurrent (hz ▸ hrec)
  have hnonone : encode z ≠ (1 : Fin 6) := by
    intro h
    have hz : z = decode (1 : Fin 6) := by
      calc
        z = decode (encode z) := (decode_encode z).symm
        _ = decode 1 := congrArg decode h
    exact u_is_not_recurrent (hz ▸ hrec)
  change (encode z = (2 : Fin 6) ∨ encode z = 3) ∨
    (encode z = 4 ∨ encode z = 5)
  have hpartition :
      ∀ i : Fin 6, i ≠ 0 → i ≠ 1 →
        (i = 2 ∨ i = 3) ∨ (i = 4 ∨ i = 5) := by
    intro i h0 h1
    fin_cases i <;> norm_num at *
  exact hpartition (encode z) hnonzero hnonone

end ExactSixStateClassSelectionWeights
end MultipleLimit
end PermanssonResearch
