import PermanssonResearch.Quotient.DiscountedCanonicalBridge
import PermanssonLean.Quotient.PathLaw
import PermanssonResearch.Quotient.DiscountedProjectedOutputs
import Mathlib.Tactic

/-!
# Actual-source canonical discounted-output transport

The source/target path laws here are not freely supplied measures. They are
the existing *typed* strategic-world canonical laws. All common-subkernel
premises, retention bounds and legal primitive correspondence remain visible.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.Quotient.DiscountedCanonicalSourceWitness
open PermanssonLean
open PermanssonLean.RegimeSpecification
open PermanssonResearch.Probability
open PermanssonResearch.Probability.DependentHistory
open PermanssonResearch.Quotient.DiscountedCanonicalBridge
open PermanssonResearch.Quotient.DiscountedProjected

set_option autoImplicit false
variable {S X A Sb Xb Ab : Type*}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace Sb] [MeasurableSpace Xb] [MeasurableSpace Ab]

/-- Baseline or treatment, with source and target both the *original*
canonical Markov law. Retention witnesses are assumptions on ACTUAL kernels,
not a fabricated TV bound, and are charged separately for each protocol. -/
theorem canonical_discounted_output_error
    (Qc : TypeRespectingStateCompression S X Sb Xb)
    (M : StrategicWorldModel S X A)
    (Mbar : StrategicWorldModel Sb Xb Ab)
    (μ ξ : Measure (JointState S X)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ξ]
    (ν : Measure (JointState Sb Xb)) [IsProbabilityMeasure ν]
    (R : Kernel (JointState S X) (JointState S X)) [IsFiniteKernel R]
    (hξμ : ξ ≤ μ)
    (hξν : ξ.map Qc.stateMap ≤ ν)
    (hRK : R ≤ M.inducedKernel)
    (hproj : R.map Qc.stateMap ≤
      Mbar.inducedKernel.comap Qc.stateMap Qc.stateMap_measurable)
    (η : ℕ → ℝ) (hη0 : ∀ n, 0 ≤ η n) (hη1 : ∀ n, η n ≤ 1)
    (hmass : ∀ n y, ENNReal.ofReal (1-η n) ≤ R y Set.univ)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hξmass : ENNReal.ofReal (1-ε) ≤ ξ Set.univ)
    (g : ℕ → JointState Sb Xb → ℝ)
    (hg : ∀ n, Measurable (g n))
    (hg0 : ∀ n y, 0 ≤ g n y)
    (hg1 : ∀ n y, g n y ≤ 1)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    |(∫ w, summablePathScore (fun n => (1-β)*β^n)
           (fun n w => g n (w n)) w
           ∂((M.pathLaw μ).map Qc.pathMap)) -
      ∫ w, summablePathScore (fun n => (1-β)*β^n)
           (fun n w => g n (w n)) w ∂(Mbar.pathLaw ν)| ≤
      ∑' n, (1-β)*β^n*(1-(1-ε)*retained η n) := by
  letI : IsMarkovKernel M.inducedKernel :=
    StrategicWorldModel.inducedKernel_isMarkov M
  letI : IsMarkovKernel Mbar.inducedKernel :=
    StrategicWorldModel.inducedKernel_isMarkov Mbar
  have hbase (n : ℕ) :
      (M.pathLaw μ).map (fun w => w n) =
      evolution μ (fun _ => M.inducedKernel) n :=
    canonical_nth_marginal_eq_evolution M μ n
  have htarget (n : ℕ) :
      (Mbar.pathLaw ν).map (fun w => w n) =
      evolution ν (fun _ => Mbar.inducedKernel) n :=
    canonical_nth_marginal_eq_evolution Mbar ν n
  have h := discounted_projected_output_error
    (M.pathLaw μ) (Mbar.pathLaw ν) μ ξ ν
    (fun _ => M.inducedKernel) (fun _ => R)
    (fun _ => Mbar.inducedKernel)
    (fun _ => Qc.stateMap) (fun _ => Qc.stateMap_measurable)
    hξμ hξν (fun _ => hRK) (fun _ => hproj)
    η hη0 hη1 hmass hε0 hε1 hξmass
    hbase htarget g hg hg0 hg1 hβ0 hβ1
  simpa only [DiscountedProjected.projectedPath, TypeRespectingStateCompression.pathMap] using h

end PermanssonResearch.Quotient.DiscountedCanonicalSourceWitness
