import PermanssonResearch.MultipleLimit.FiniteBasinClassification
import PermanssonLean.Regime.GeneratedRegime
import Mathlib.Tactic

/-!
# C53-09 — conservative original Exact GR recovery from finite class laws

The multiple-class random physical limit is NOT automatically an Exact GR:
the frozen v0.1.8 specification has ONE ex-ante descriptor target.
This theorem recovers its ORIGINAL four gates only when a genuinely
nonempty frozen basin-family exists, its positive-probability reachable
classes have the SAME observed law, all Assumption 4.1 gates hold, and
the original induced strategic-world region is exactly invariant.

No original semantics are edited. No generalized Permansson / constitutive
PR result is inferred without a separate typed intervention witness.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteExactGRRecovery

open PermanssonLean
open PermanssonLean.RegimeSpecification
open FiniteCanonicalPath
open FiniteStateOccupation
open BasinFamily
open FiniteBasinClassification
open ClassDescriptorSelectionLaw

variable {S X A H : Type*}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]
variable [TopologicalSpace S] [TopologicalSpace X]
variable [TopologicalSpace H] [BorelSpace H]
variable [Fintype (JointState S X)] [Nonempty (JointState S X)]
variable [DecidableEq (JointState S X)]
variable [MeasurableSingletonClass (JointState S X)]
variable [DiscreteTopology (JointState S X)]
variable [OpensMeasurableSpace (JointState S X)]
variable [StandardBorelSpace (JointState S X)]

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- Explicit equality at every finite horizon between the ORIGINAL
frozen descriptor occupation and the pushforward of the generic finite
physical occupation. This is not a limit argument. -/
theorem original_empirical_eq_physical_map
    (spec : RegimeSpecification (JointState S X) H)
    (w : ℕ → JointState S X) (T : ℕ) (hT : 0 < T) :
    RegimeSpecification.empiricalOccupation spec w T hT =
      (FiniteStateOccupation.empiricalOccupation w T hT).map
        spec.descriptor := by
  apply ProbabilityMeasure.toMeasure_injective
  change
    Measure.map (fun i : Fin T =>
      spec.descriptor (w (i : ℕ)))
      (ProbabilityTheory.uniformOn (Set.univ : Set (Fin T))) =
    Measure.map spec.descriptor
      (Measure.map (fun i : Fin T => w (i : ℕ))
        (ProbabilityTheory.uniformOn (Set.univ : Set (Fin T))))
  rw [Measure.map_map spec.descriptor_measurable (by fun_prop)]
  rfl

/-- Return a genuine graph-closed basin family from the ORIGINAL
one-step invariance and Assumption 4.1, without introducing a competing
interpretation of the regime region or ex-ante basin. -/
noncomputable def frozenFamilyOfExactSpec
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (h41 : Assumption41 M spec m)
    (hinv : IsExactlyInvariant M spec) :
    FrozenBasinFamily M.inducedKernel H where
  region := spec.region
  basin := spec.basin
  basin_nonempty := h41.1
  basin_subset_region := spec.basin_subset_region
  region_closed := by
    intro y hy z hpos
    by_contra hz
    have hcomplete : M.inducedKernel y spec.region = 1 :=
      hinv y hy
    have hcomplement : M.inducedKernel y spec.regionᶜ = 0 := by
      rw [prob_compl_eq_one_sub spec.region_measurable, hcomplete]
      simp
    have hsubset : ({z} : Set (JointState S X)) ⊆ spec.regionᶜ := by
      intro q hq
      have hqz : q = z := Set.mem_singleton_iff.mp hq
      subst q
      exact hz
    have hzero : M.inducedKernel y {z} = 0 :=
      measure_mono_null hsubset hcomplement
    exact (ne_of_gt hpos) hzero
  descriptor := spec.descriptor
  descriptor_measurable := spec.descriptor_measurable

/-- Full recovery of the frozen original Exact GR predicate, including
the true typed alpha/P/U path law for arbitrary admissible initial laws.
The only special finite-chain substantive premise is equality of the
independently PROVED stationary descriptor laws across basin-reachable
classes. No empirical occupation convergence is hypothesized. -/
theorem recover_original_exactGR_of_common_class_target
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (h41 : Assumption41 M spec m)
    (hinv : IsExactlyInvariant M spec)
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) H)
    (hcommon :
      ∀ i ∈ reachableRepresentatives M.inducedKernel H
        (frozenFamilyOfExactSpec M spec m h41 hinv),
          observedStationaryForClass M.inducedKernel spec.descriptor i =
            spec.target) :
    IsExactGeneratedRegime M spec m := by
  let F := frozenFamilyOfExactSpec M spec m h41 hinv
  let C : CommonObservedCertificate M.inducedKernel F := {
    target := spec.target
    common := by
      intro i hi
      exact hcommon i hi
  }
  refine ⟨canonicalProcessWellPosed M, h41, hinv, ?_⟩
  intro μ hμ
  have hb : μ.toMeasure F.basin = 1 := by
    exact hμ
  have hcanon :=
    canonical_family_observed_ae_limit M.inducedKernel F C μ hb
  unfold IsLimitingOccupationLaw
  rw [hmode]
  change ∀ᵐ w ∂M.pathLaw μ.toMeasure,
    Tendsto
      (fun n : ℕ =>
        RegimeSpecification.empiricalOccupation spec w
          (n+1) (Nat.succ_pos n))
      atTop (𝓝 spec.target)
  rw [typed_pathLaw_eq_canonical M μ.toMeasure]
  filter_upwards [hcanon] with w hw
  convert hw using 1
  ext n
  exact original_empirical_eq_physical_map spec w (n+1)
    (Nat.succ_pos n)

end FiniteExactGRRecovery
end MultipleLimit
end PermanssonResearch
