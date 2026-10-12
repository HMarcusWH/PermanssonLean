import PermanssonResearch.MultipleLimit.FiniteStateOccupation
import PermanssonResearch.MultipleLimit.CanonicalRecurrentResidence
import PermanssonResearch.MultipleLimit.FiniteUniformAverage
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Tactic

/-!
# Lane C2 — observed finite occupation after a recurrent class becomes invisible

An arbitrary finite-state Markov process can have random physical
occupation limits, but its frozen descriptor can become constant as soon
as the path enters a recurrent class. The result here proves that such
EVENTUALLY CONSTANT observed paths have a deterministic Dirac
occupation limit in the original weak topology.

This theorem is pathwise and does NOT require physical occupation
ergodicity or assume an a.s. martingale strong law.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteEventuallyObserved

open FiniteStateOccupation
open RecurrentClassDecomposition
open CanonicalRecurrentResidence
open FiniteCanonicalPath

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [Nonempty Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- All class members are recurrent; the actual Markov path therefore
eventually takes its values in a recurrent state almost surely. -/
theorem canonical_eventually_recurrent (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      ∃ N : ℕ, ∀ n ≥ N, w n ∈ RecurrentStates K := by
  filter_upwards [canonical_ae_eventual_recurrent_class K μ] with w hw
  obtain ⟨C,hC,⟨N,hN⟩⟩ := hw
  refine ⟨N, ?_⟩
  intro n hn
  exact (recurrentStates_iff_mem_recurrentClass K (w n)).mpr
    ⟨C,hC,hN n hn⟩

/-- Frozen Boolean observations that label all recurrent states true
must eventually be true on the genuine canonical infinite Markov
trajectory, regardless of which class is selected. -/
theorem canonical_descriptor_eventually_true
    (h : Y → Bool)
    (hrec : ∀ y ∈ RecurrentStates K, h y = true)
    (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      ∃ N : ℕ, ∀ n ≥ N, h (w n) = true := by
  filter_upwards [canonical_eventually_recurrent K μ] with w hE
  obtain ⟨N,hN⟩ := hE
  exact ⟨N, fun n hn => hrec (w n) (hN n hn)⟩

/-- The entire observed empirical law is a true pushforward from the
frozen positive-horizon physical occupation process. -/
noncomputable def observedEmpirical (h : Y → Bool)
    (w : ℕ → Y) (T : ℕ) (hT : 0 < T) :
    ProbabilityMeasure Bool :=
  (empiricalOccupation w T hT).map h

/-- Exact finite average of any bounded real Boolean observable under
the frozen empirical law, including time zero and horizon one. -/
theorem observedEmpirical_integral_eq_average
    (h : Y → Bool) (w : ℕ → Y)
    (T : ℕ) (hT : 0 < T) (f : Bool → ℝ) :
    (∫ b, f b ∂observedEmpirical h w T hT) =
      ((T : ℝ)⁻¹) * ∑ t ∈ Finset.range T, f (h (w t)) := by
  have hh : Measurable h := Measurable.of_discrete
  have hmeasure :
      (observedEmpirical h w T hT).toMeasure =
        Measure.map (fun i : Fin T => h (w (i : ℕ)))
          (PermanssonLean.RegimeSpecification.uniformFinProbability T hT).toMeasure := by
    unfold observedEmpirical FiniteStateOccupation.empiricalOccupation
    simp only [ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hmeasure]
  rw [integral_map (by fun_prop) (by fun_prop)]
  rw [FiniteUniformAverage.integral_uniformFin_eq_average T hT]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => f (h (w i)))]

/-- A deterministic eventual true observation yields the true
probability-measure-valued empirical limit δ_true; the transient
prefix is allowed to be arbitrarily long. -/
theorem observedEmpirical_tendsto_true_of_eventually
    (h : Y → Bool) (w : ℕ → Y)
    (hE : ∃ N : ℕ, ∀ n ≥ N, h (w n) = true) :
    Tendsto (fun n : ℕ => observedEmpirical h w (n+1)
      (Nat.succ_pos n)) atTop (𝓝 (diracProba true)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  change Tendsto
    (fun n : ℕ => ∫ b, f b ∂observedEmpirical h w
      (n+1) (Nat.succ_pos n))
    atTop (𝓝 (∫ b, f b ∂(Measure.dirac true)))
  simp only [integral_dirac]
  obtain ⟨N,hN⟩ := hE
  have heq : (fun n : ℕ => f (h (w n))) =ᶠ[atTop]
      (fun _ : ℕ => f true) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [hN n hn]
  have hp : Tendsto (fun n : ℕ => f (h (w n)))
      atTop (𝓝 (f true)) :=
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

/-- Unconditional deterministic observed occupation from ANY
initial probability law for an arbitrary finite homogeneous Markov
chain whose recurrent states share the frozen descriptor label true.
This is not a theorem about physical classwise occupation limits. -/
theorem canonical_observed_occupation_ae_true
    (h : Y → Bool)
    (hrec : ∀ y ∈ RecurrentStates K, h y = true)
    (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n : ℕ =>
        observedEmpirical h w (n+1) (Nat.succ_pos n))
        atTop (𝓝 (diracProba true)) := by
  filter_upwards [canonical_descriptor_eventually_true K h hrec μ]
    with w hE
  exact observedEmpirical_tendsto_true_of_eventually h w hE

end FiniteEventuallyObserved
end MultipleLimit
end PermanssonResearch
