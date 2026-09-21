import PermanssonLean.Quotient.PathLaw
import PermanssonLean.Regime.GeneratedRegime

open MeasureTheory ProbabilityTheory Set

namespace PermanssonLean

universe uS uX uA uSbar uXbar uAbar uH

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {Sbar : Type uSbar} {Xbar : Type uXbar} {Abar : Type uAbar}
variable {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace Sbar] [MeasurableSpace Xbar] [MeasurableSpace Abar]
variable [MeasurableSpace H]
variable [TopologicalSpace S] [TopologicalSpace X]
variable [TopologicalSpace Sbar] [TopologicalSpace Xbar]

/-- Frozen regime objects are compatible with q when region, basin, descriptor,
and target law descend exactly as declared in Theorem 7.4b. -/
structure QuotientCompatibleRegimeSpecifications
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (spec : RegimeSpecification (JointState S X) H)
    (specbar : RegimeSpecification (JointState Sbar Xbar) H) where
  region_preimage :
    spec.region = Q.stateMap ⁻¹' specbar.region
  basin_preimage :
    spec.basin = Q.stateMap ⁻¹' specbar.basin
  descriptor_factor :
    spec.descriptor = specbar.descriptor ∘ Q.stateMap
  target_eq :
    spec.target = specbar.target

/-- The convergence predicate is an ex-ante semantic object in this repository
and may be an arbitrary custom predicate.  Quotient preservation therefore
requires its naturality under path pushforward explicitly rather than assuming
it for every possible custom mode. -/
def ConvergenceModesCompatibleUnderCompression
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (spec : RegimeSpecification (JointState S X) H)
    (specbar : RegimeSpecification (JointState Sbar Xbar) H) : Prop :=
  ∀ μ : Measure (ℕ → JointState S X),
    spec.convergenceMode.holds
        μ (RegimeSpecification.empiricalOccupation spec) spec.target ↔
      specbar.convergenceMode.holds
        (μ.map Q.pathMap)
        (RegimeSpecification.empiricalOccupation specbar)
        specbar.target

/-- Every admissible compressed initial law has an admissible lift. -/
def HasAdmissibleInitialLifts
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (spec : RegimeSpecification (JointState S X) H)
    (specbar : RegimeSpecification (JointState Sbar Xbar) H) : Prop :=
  ∀ μbar : ProbabilityMeasure (JointState Sbar Xbar),
    IsAdmissibleInitialLaw specbar μbar →
      ∃ μ : ProbabilityMeasure (JointState S X),
        IsAdmissibleInitialLaw spec μ ∧
          Q.pushInitial μ = μbar

namespace RegimeSpecification

theorem pushInitial_admissible
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (spec : RegimeSpecification (JointState S X) H)
    (specbar : RegimeSpecification (JointState Sbar Xbar) H)
    (C : QuotientCompatibleRegimeSpecifications Q spec specbar)
    (μ : ProbabilityMeasure (JointState S X))
    (hμ : IsAdmissibleInitialLaw spec μ) :
    IsAdmissibleInitialLaw specbar (Q.pushInitial μ) := by
  unfold IsAdmissibleInitialLaw TypeRespectingStateCompression.pushInitial
  rw [ProbabilityMeasure.toMeasure_map,
      Measure.map_apply Q.stateMap_measurable specbar.basin_measurable,
      ← C.basin_preimage]
  exact hμ

theorem exactInvariant_iff_of_kernelIntertwines
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (M : StrategicWorldModel S X A)
    (Mbar : StrategicWorldModel Sbar Xbar Abar)
    (hK : KernelIntertwines Q M.inducedKernel Mbar.inducedKernel)
    (spec : RegimeSpecification (JointState S X) H)
    (specbar : RegimeSpecification (JointState Sbar Xbar) H)
    (C : QuotientCompatibleRegimeSpecifications Q spec specbar) :
    IsExactlyInvariant M spec ↔ IsExactlyInvariant Mbar specbar := by
  constructor
  · intro h ybar hybar
    rcases Q.stateMap_surjective ybar with ⟨y, hy⟩
    have hyreg : y ∈ spec.region := by
      rw [C.region_preimage]
      simpa [hy] using hybar
    have hbase := h y hyreg
    have hinter := kernelIntertwines_apply_preimage
      Q M.inducedKernel Mbar.inducedKernel hK
      y specbar.region specbar.region_measurable
    rw [← C.region_preimage] at hinter
    simpa [hy] using hinter.symm.trans hbase
  · intro h y hy
    have hybar : Q.stateMap y ∈ specbar.region := by
      rw [C.region_preimage] at hy
      exact hy
    have hbar := h (Q.stateMap y) hybar
    have hinter := kernelIntertwines_apply_preimage
      Q M.inducedKernel Mbar.inducedKernel hK
      y specbar.region specbar.region_measurable
    rw [← C.region_preimage] at hinter
    exact hinter.trans hbar

theorem limitingOccupation_push_iff
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (M : StrategicWorldModel S X A)
    (Mbar : StrategicWorldModel Sbar Xbar Abar)
    (hK : KernelIntertwines Q M.inducedKernel Mbar.inducedKernel)
    (spec : RegimeSpecification (JointState S X) H)
    (specbar : RegimeSpecification (JointState Sbar Xbar) H)
    (hconv : ConvergenceModesCompatibleUnderCompression Q spec specbar)
    (μ : ProbabilityMeasure (JointState S X)) :
    IsLimitingOccupationLaw M spec μ ↔
      IsLimitingOccupationLaw Mbar specbar (Q.pushInitial μ) := by
  unfold IsLimitingOccupationLaw
  have hc := hconv (M.pathLaw μ.toMeasure)
  simpa [TypeRespectingStateCompression.pushInitial,
    ProbabilityMeasure.toMeasure_map,
    StrategicWorldModel.pathLaw_map_eq_of_kernelIntertwines
      Q M Mbar hK μ.toMeasure] using hc

/-- Exact-GR preservation under the regime-semantic part of an
intervention-compatible quotient.  Assumption 4.1 is supplied independently
on each state representation, matching the paper's warning that nontriviality
need not be inherited by arbitrary compression. -/
theorem exactGR_iff_of_quotient
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (M : StrategicWorldModel S X A)
    (Mbar : StrategicWorldModel Sbar Xbar Abar)
    (hK : KernelIntertwines Q M.inducedKernel Mbar.inducedKernel)
    (spec : RegimeSpecification (JointState S X) H)
    (specbar : RegimeSpecification (JointState Sbar Xbar) H)
    (C : QuotientCompatibleRegimeSpecifications Q spec specbar)
    (hconv : ConvergenceModesCompatibleUnderCompression Q spec specbar)
    (hlifts : HasAdmissibleInitialLifts Q spec specbar)
    (m : Measure (JointState S X))
    (mbar : Measure (JointState Sbar Xbar))
    (hA : Assumption41 M spec m)
    (hAbar : Assumption41 Mbar specbar mbar) :
    IsExactGeneratedRegime M spec m ↔
      IsExactGeneratedRegime Mbar specbar mbar := by
  constructor
  · intro h
    refine ⟨canonicalProcessWellPosed Mbar, hAbar, ?_, ?_⟩
    · exact (exactInvariant_iff_of_kernelIntertwines
        Q M Mbar hK spec specbar C).1 h.2.2.1
    · intro μbar hμbar
      rcases hlifts μbar hμbar with ⟨μ, hμ, hpush⟩
      have hlim : IsLimitingOccupationLaw M spec μ :=
        h.2.2.2 μ hμ
      have hlimbar :=
        (limitingOccupation_push_iff
          Q M Mbar hK spec specbar hconv μ).1 hlim
      simpa [hpush] using hlimbar
  · intro h
    refine ⟨canonicalProcessWellPosed M, hA, ?_, ?_⟩
    · exact (exactInvariant_iff_of_kernelIntertwines
        Q M Mbar hK spec specbar C).2 h.2.2.1
    · intro μ hμ
      have hpush :
          IsAdmissibleInitialLaw specbar (Q.pushInitial μ) :=
        pushInitial_admissible Q spec specbar C μ hμ
      have hlimbar :
          IsLimitingOccupationLaw Mbar specbar (Q.pushInitial μ) :=
        h.2.2.2 (Q.pushInitial μ) hpush
      exact (limitingOccupation_push_iff
        Q M Mbar hK spec specbar hconv μ).2 hlimbar

end RegimeSpecification

end PermanssonLean
