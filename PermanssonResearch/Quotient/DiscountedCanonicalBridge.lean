import PermanssonResearch.MultipleLimit.StationaryCanonicalShift
import PermanssonResearch.MultipleLimit.FiniteCanonicalPath
import PermanssonResearch.Probability.DependentHistoryCommonMass
import PermanssonLean.StrategicWorld.PathLaw
import Mathlib.Tactic

/-!
# NEXT-04.1 — Real canonical path-law marginals and dependent evolution

This is the *source identification* missing from the existing conditional
discounted projected-output bound. The original alpha -> P -> U induced
kernel and original Ionescu-Tulcea path law are used, not a synthetic
independent-coordinate law or an assumed Markov projection.

There is no constitutive-margin/Exact-GR promotion in this module.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.Quotient.DiscountedCanonicalBridge

open PermanssonResearch.MultipleLimit.FiniteCanonicalPath
open PermanssonResearch.MultipleLimit.CanonicalKernelMarginals
open PermanssonResearch.MultipleLimit.StationaryCanonical
open PermanssonResearch.Probability.DependentHistory
open PermanssonLean

set_option autoImplicit false

/-- An actual homogeneous canonical Markov trajectory has precisely the
dependent-history evolution marginals at every time for any initial law. -/
theorem canonical_measure_marginal_evolution
    {Y : Type*} [MeasurableSpace Y]
    (K : Kernel Y Y) [IsMarkovKernel K]
    (μ : Measure Y) [IsProbabilityMeasure μ] :
    ∀ n : ℕ,
      (canonicalPathLaw K μ).map (fun w : ℕ → Y => w n) =
      evolution μ (fun _ => K) n := by
  intro n
  induction n with
  | zero =>
      simpa [evolution] using canonical_eval_zero K μ
  | succ n ih =>
      rw [canonical_eval_succ K μ n, ih]
      change K ∘ₘ evolution μ (fun _ => K) n =
        ((evolution μ (fun _ => K) n ⊗ₘ K).map Prod.snd)
      apply Measure.ext
      intro E hE
      haveI : IsProbabilityMeasure (evolution μ (fun _ => K) n) :=
        evolution_probability μ (fun _ => K) n
      rw [Measure.bind_apply hE (Kernel.aemeasurable _)]
      rw [Measure.map_apply measurable_snd hE]
      rw [Measure.compProd_apply (hE.preimage measurable_snd)]
      rfl

/-- The identity is bound to the ORIGINAL canonical typed model, including
its induced kernel, for arbitrary initial probability distributions. -/
theorem canonical_nth_marginal_eq_evolution
    {S X A : Type*} [MeasurableSpace S] [MeasurableSpace X]
    [MeasurableSpace A]
    (M : StrategicWorldModel S X A)
    (μ : Measure (JointState S X)) [IsProbabilityMeasure μ] (n : ℕ) :
    (M.pathLaw μ).map (fun w : ℕ → JointState S X => w n) =
    evolution μ (fun _ => M.inducedKernel) n := by
  letI : IsMarkovKernel M.inducedKernel :=
    StrategicWorldModel.inducedKernel_isMarkov M
  rw [typed_pathLaw_eq_canonical M μ]
  exact canonical_measure_marginal_evolution M.inducedKernel μ n

/-- In the original constitutive setup, each starting state is a point
start, hence no fictitious mismatch may be charged at time zero. -/
theorem canonical_point_start_zero
    {S X A : Type*} [MeasurableSpace S] [MeasurableSpace X]
    [MeasurableSpace A] [MeasurableSingletonClass (JointState S X)]
    (M : StrategicWorldModel S X A) (y : JointState S X) :
    (M.pathLaw (Measure.dirac y)).map
      (fun w : ℕ → JointState S X => w 0) = Measure.dirac y := by
  simpa [evolution] using
    canonical_nth_marginal_eq_evolution M (Measure.dirac y) 0

end PermanssonResearch.Quotient.DiscountedCanonicalBridge
