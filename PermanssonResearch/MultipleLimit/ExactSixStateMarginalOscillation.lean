import PermanssonResearch.MultipleLimit.ExactSixStateStationaryCoordinates
import PermanssonResearch.MultipleLimit.CanonicalKernelMarginals
import PermanssonResearch.MultipleLimit.ExactSixStateClassSelectionWeights
import PermanssonResearch.MultipleLimit.ExactSixStateFullRandomLaw
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic

/-!
# C55-02/03 — true typed six-state periodic marginals versus occupation

From an a0 point start the genuine typed alpha/P/U path law has
one-time marginals exactly dirac a0 at every even time and dirac a1 at
every odd time. No weak limit exists for that full marginal sequence.
Nonetheless the SAME actual point-started path law has a.s. weak
empirical occupation limit πA, the unique period-two class stationary
measure, without requiring aperiodicity.

Do not extrapolate marginal nonconvergence to stationary initial laws.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactSixStateMarginalOscillation

open PermanssonLean
open ReverseSolver.FiniteStrategicRealization
open ExactSixState
open ExactSixStateTyped
open ExactSixStateRecurrentGeometry
open ExactSixStateClassSelectionWeights
open ExactSixStateClassLaws
open ExactSixStateStationaryCoordinates
open ExactSixStateFullRandomLaw
open FiniteCanonicalPath
open CanonicalKernelMarginals
open CanonicalClassSelector
open FiniteOccupationRandomLaw
open FiniteStateOccupation

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

abbrev SixY := JointState Unit (Fin 6)
private noncomputable abbrev K := typedModel.inducedKernel
private def a0 : SixY := decode (2 : Fin 6)
private def a1 : SixY := decode (3 : Fin 6)

theorem a0_ne_a1 : a0 ≠ a1 := by
  norm_num [a0, a1, decode]

/-- Whole-measure deterministic a0 → a1 transition under the genuine
induced typed alpha/P/U kernel, proved on all six measurable atoms. -/
theorem typed_row_a0 : K a0 = Measure.dirac a1 := by
  apply Measure.ext_of_singleton
  intro z
  rcases z with ⟨u, j⟩
  cases u
  change K (decode (2 : Fin 6)) ({decode j} : Set SixY) =
    Measure.dirac (decode (3 : Fin 6)) {decode j}
  rw [typed_six_state_atom]
  fin_cases j <;> norm_num [transition]

theorem typed_row_a1 : K a1 = Measure.dirac a0 := by
  apply Measure.ext_of_singleton
  intro z
  rcases z with ⟨u, j⟩
  cases u
  change K (decode (3 : Fin 6)) ({decode j} : Set SixY) =
    Measure.dirac (decode (2 : Fin 6)) {decode j}
  rw [typed_six_state_atom]
  fin_cases j <;> norm_num [transition]

/-- The real typed infinite path law projected to its time-n state,
before wrapping it as a probability measure. -/
noncomputable def marginalMeasure (n : ℕ) : Measure SixY :=
  (typedModel.pathLaw (Measure.dirac a0)).map
    (fun w : ℕ → SixY => w n)

theorem marginalMeasure_zero : marginalMeasure 0 = Measure.dirac a0 := by
  unfold marginalMeasure
  rw [typed_pathLaw_eq_canonical typedModel (Measure.dirac a0)]
  exact canonical_eval_zero_dirac K a0

theorem marginalMeasure_succ (n : ℕ) :
    marginalMeasure (n + 1) = K ∘ₘ marginalMeasure n := by
  unfold marginalMeasure
  rw [typed_pathLaw_eq_canonical typedModel (Measure.dirac a0)]
  exact canonical_eval_succ K (Measure.dirac a0) n

private theorem kernel_comp_dirac (y : SixY) :
    K ∘ₘ Measure.dirac y = K y := by
  change Measure.bind (Measure.dirac y) K = K y
  exact Measure.dirac_bind (Kernel.measurable K) y

/-- Simultaneous even/odd induction under the actual infinite law.
The base is the true time-zero Dirac; successors use the derived
canonical Chapman–Kolmogorov identity, not independent observations. -/
theorem marginalMeasure_even_odd (n : ℕ) :
    marginalMeasure (2*n) = Measure.dirac a0 ∧
      marginalMeasure (2*n+1) = Measure.dirac a1 := by
  induction n with
  | zero =>
      constructor
      · simpa using marginalMeasure_zero
      · calc
          marginalMeasure (2*0+1) = K ∘ₘ marginalMeasure 0 := by
            simpa using marginalMeasure_succ 0
          _ = K ∘ₘ Measure.dirac a0 := by rw [marginalMeasure_zero]
          _ = K a0 := kernel_comp_dirac a0
          _ = Measure.dirac a1 := typed_row_a0
  | succ n ih =>
      constructor
      · calc
          marginalMeasure (2*(n+1)) =
              marginalMeasure ((2*n+1)+1) := by congr 1; omega
          _ = K ∘ₘ marginalMeasure (2*n+1) := marginalMeasure_succ _
          _ = K ∘ₘ Measure.dirac a1 := by rw [ih.2]
          _ = K a1 := kernel_comp_dirac a1
          _ = Measure.dirac a0 := typed_row_a1
      · calc
          marginalMeasure (2*(n+1)+1) =
              marginalMeasure ((2*(n+1))+1) := rfl
          _ = K ∘ₘ marginalMeasure (2*(n+1)) := marginalMeasure_succ _
          _ = K ∘ₘ Measure.dirac a0 := by
            rw [show marginalMeasure (2*(n+1)) = Measure.dirac a0
              from (marginalMeasure_even_odd (n+1)).1]
          _ = K a0 := kernel_comp_dirac a0
          _ = Measure.dirac a1 := typed_row_a0

/-- Direct statement for all even times of the true typed path law. -/
theorem typed_even_marginal (n : ℕ) :
    (typedModel.pathLaw (Measure.dirac a0)).map
      (fun w : ℕ → SixY => w (2*n)) = Measure.dirac a0 :=
  (marginalMeasure_even_odd n).1

theorem typed_odd_marginal (n : ℕ) :
    (typedModel.pathLaw (Measure.dirac a0)).map
      (fun w : ℕ → SixY => w (2*n+1)) = Measure.dirac a1 :=
  (marginalMeasure_even_odd n).2

/-- The already proved canonical marginal-power theorem identifies each
of these genuine typed path marginals with the actual kernel powers. -/
theorem typed_even_kernel_power (n : ℕ) :
    (K ^ (2*n)) a0 = Measure.dirac a0 := by
  calc
    (K ^ (2*n)) a0 =
        (canonicalPathLaw K (Measure.dirac a0)).map
          (fun w : ℕ → SixY => w (2*n)) :=
      (canonical_eval_eq_kernel_pow K a0 (2*n)).symm
    _ = (typedModel.pathLaw (Measure.dirac a0)).map
          (fun w : ℕ → SixY => w (2*n)) := by
      rw [typed_pathLaw_eq_canonical typedModel (Measure.dirac a0)]
    _ = Measure.dirac a0 := typed_even_marginal n

theorem typed_odd_kernel_power (n : ℕ) :
    (K ^ (2*n+1)) a0 = Measure.dirac a1 := by
  calc
    (K ^ (2*n+1)) a0 =
        (canonicalPathLaw K (Measure.dirac a0)).map
          (fun w : ℕ → SixY => w (2*n+1)) :=
      (canonical_eval_eq_kernel_pow K a0 (2*n+1)).symm
    _ = (typedModel.pathLaw (Measure.dirac a0)).map
          (fun w : ℕ → SixY => w (2*n+1)) := by
      rw [typed_pathLaw_eq_canonical typedModel (Measure.dirac a0)]
    _ = Measure.dirac a1 := typed_odd_marginal n

/-- Package the actual pushforward of the real infinite typed path law
as a probability measure at every symbolic natural-number time. -/
noncomputable def timeMarginalA0 (n : ℕ) : ProbabilityMeasure SixY :=
  ⟨marginalMeasure n, by
    unfold marginalMeasure
    infer_instance⟩

theorem timeMarginalA0_eq_typed_path (n : ℕ) :
    (timeMarginalA0 n).toMeasure =
      (typedModel.pathLaw (Measure.dirac a0)).map
        (fun w : ℕ → SixY => w n) := rfl

theorem timeMarginalA0_even (n : ℕ) :
    timeMarginalA0 (2*n) = diracProba a0 := by
  apply ProbabilityMeasure.toMeasure_injective
  exact typed_even_marginal n

theorem timeMarginalA0_odd (n : ℕ) :
    timeMarginalA0 (2*n+1) = diracProba a1 := by
  apply ProbabilityMeasure.toMeasure_injective
  exact typed_odd_marginal n

private theorem even_cofinal :
    Tendsto (fun n : ℕ => 2*n) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with n hn
  omega

private theorem odd_cofinal :
    Tendsto (fun n : ℕ => 2*n+1) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with n hn
  omega

private theorem dirac_a0_ne_dirac_a1 :
    diracProba a0 ≠ diracProba a1 := by
  intro h
  have hm : (Measure.dirac a0 : Measure SixY) =
      Measure.dirac a1 :=
    congrArg (fun μ : ProbabilityMeasure SixY => μ.toMeasure) h
  exact a0_ne_a1 (MeasureTheory.dirac_eq_dirac_iff.mp hm)

/-- Strong nonconvergence: NO weak probability-measure limit exists.
The even and odd subsequences are both cofinal yet have unequal
Dirac limits under the Hausdorff weak probability-measure topology. -/
theorem timeMarginalA0_not_weakly_convergent :
    ¬ ∃ ν : ProbabilityMeasure SixY,
      Tendsto timeMarginalA0 atTop (𝓝 ν) := by
  rintro ⟨ν, hν⟩
  haveI : T2Space (ProbabilityMeasure SixY) := inferInstance
  have hEven : Tendsto
      (fun n : ℕ => timeMarginalA0 (2*n))
      atTop (𝓝 ν) := hν.comp even_cofinal
  have hOdd : Tendsto
      (fun n : ℕ => timeMarginalA0 (2*n+1))
      atTop (𝓝 ν) := hν.comp odd_cofinal
  have hEqA : diracProba a0 = ν := by
    have h : Tendsto (fun _ : ℕ => diracProba a0)
        atTop (𝓝 ν) := by
      simpa only [timeMarginalA0_even] using hEven
    exact tendsto_nhds_unique tendsto_const_nhds h
  have hEqB : diracProba a1 = ν := by
    have h : Tendsto (fun _ : ℕ => diracProba a1)
        atTop (𝓝 ν) := by
      simpa only [timeMarginalA0_odd] using hOdd
    exact tendsto_nhds_unique tendsto_const_nhds h
  exact dirac_a0_ne_dirac_a1 (hEqA.trans hEqB.symm)

/-- A genuine Dirac start enforces the physical initial coordinate
almost surely; this is not a universal claim over every sample path. -/
theorem a0_initial_ae :
    ∀ᵐ w ∂typedModel.pathLaw (Measure.dirac a0),
      w 0 = a0 := by
  rw [ae_iff]
  have h := congrArg
    (fun μ : Measure SixY => μ ({a0}ᶜ : Set SixY))
    marginalMeasure_zero
  rw [Measure.map_apply (measurable_pi_apply 0)
    (measurableSet_singleton a0).compl] at h
  simpa [marginalMeasure] using h

private theorem a0_mem_classA : a0 ∈ classASet := by
  norm_num [a0, classASet, classA, encode, decode]

/-- Under the ACTUAL a0-started infinite path law, the C2 canonical
class selector lies in the closed period-two class almost surely. -/
theorem a0_selected_classA_ae :
    ∀ᵐ w ∂typedModel.pathLaw (Measure.dirac a0),
      selectedRepresentative K w ∈ classASet := by
  have hclosed := selected_in_closed_iff_ever_hit_ae
    classASet classASet_closed (diracProba a0)
  rw [← typed_pathLaw_eq_canonical typedModel (Measure.dirac a0)]
    at hclosed
  filter_upwards [a0_initial_ae, hclosed] with w h0 hclass
  apply hclass.mpr
  refine ⟨0, ?_⟩
  rw [h0]
  exact a0_mem_classA

/-- The same a0-started infinite typed path has almost-sure
empirical-occupation weak convergence to the unique stationary πA. -/
theorem a0_empirical_converges_piA :
    ∀ᵐ w ∂typedModel.pathLaw (Measure.dirac a0),
      Tendsto
        (fun n : ℕ =>
          FiniteStateOccupation.empiricalOccupation w (n+1)
            (Nat.succ_pos n))
        atTop (𝓝 ExactSixStateClassLaws.πA) := by
  have hlimit := physicalOccupationLimit_ae_correct K (diracProba a0)
  rw [← typed_pathLaw_eq_canonical typedModel (Measure.dirac a0)]
    at hlimit
  filter_upwards [a0_selected_classA_ae, hlimit] with w hclass hw
  rw [actualPhysicalLimit_eq_piA_of_selected_A w hclass] at hw
  exact hw

end ExactSixStateMarginalOscillation
end MultipleLimit
end PermanssonResearch
