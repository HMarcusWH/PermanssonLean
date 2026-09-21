import PermanssonLean.Regime.Invariance
import PermanssonLean.Regime.Occupation

open MeasureTheory

namespace PermanssonLean

universe uS uX uA uH

variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]
variable [TopologicalSpace (JointState S X)]

namespace RegimeSpecification

/-- The canonical strategic-world process is well posed for every initial
probability law.  This is a named model-level gate so Definition 4.3 can
mirror the paper literally instead of silently dropping clause (i). -/
def CanonicalProcessWellPosed
    (M : StrategicWorldModel S X A) : Prop :=
  ∀ λ : ProbabilityMeasure (JointState S X),
    ∃! μ : Measure (ℕ → JointState S X),
      StrategicWorldModel.MarkovPathLawSpec M λ.toMeasure μ

theorem canonicalProcessWellPosed
    (M : StrategicWorldModel S X A) :
    CanonicalProcessWellPosed M := by
  intro λ
  exact StrategicWorldModel.pathLaw_existsUnique M λ.toMeasure

/-- Definition 4.3: Exact Generated Regime.

The reference measure is an explicit frozen input for Assumption 4.1(ii).
The convergence-mode field is part of Σ and may encode any precisely
declared ex-ante mode meaningful for every admissible initial law.
-/
def IsExactGeneratedRegime
    (M : StrategicWorldModel S X A)
    (Σ : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X)) : Prop :=
  CanonicalProcessWellPosed M ∧
  Assumption41 M Σ m ∧
  IsExactlyInvariant M Σ ∧
  ∀ λ : ProbabilityMeasure (JointState S X),
    IsAdmissibleInitialLaw Σ λ →
      IsLimitingOccupationLaw M Σ λ

/-- Confirmatory GR certificate used in the paper: Exact GR plus
basin-reachable descriptor nondegeneracy.  Forward descriptor richness is
intentionally not made a universal gate. -/
def IsConfirmatoryGeneratedRegime
    (M : StrategicWorldModel S X A)
    (Σ : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X)) : Prop :=
  IsExactGeneratedRegime M Σ m ∧
  IsDescriptorNondegenerate M Σ

theorem exactGR_wellPosed
    (M : StrategicWorldModel S X A)
    (Σ : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (h : IsExactGeneratedRegime M Σ m) :
    CanonicalProcessWellPosed M :=
  h.1

theorem exactGR_assumption41
    (M : StrategicWorldModel S X A)
    (Σ : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (h : IsExactGeneratedRegime M Σ m) :
    Assumption41 M Σ m :=
  h.2.1

theorem exactGR_exactlyInvariant
    (M : StrategicWorldModel S X A)
    (Σ : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (h : IsExactGeneratedRegime M Σ m) :
    IsExactlyInvariant M Σ :=
  h.2.2.1

theorem exactGR_limitingOccupation
    (M : StrategicWorldModel S X A)
    (Σ : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (h : IsExactGeneratedRegime M Σ m)
    (λ : ProbabilityMeasure (JointState S X))
    (hλ : IsAdmissibleInitialLaw Σ λ) :
    IsLimitingOccupationLaw M Σ λ :=
  h.2.2.2 λ hλ

theorem confirmatoryGR_exact
    (M : StrategicWorldModel S X A)
    (Σ : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (h : IsConfirmatoryGeneratedRegime M Σ m) :
    IsExactGeneratedRegime M Σ m :=
  h.1

theorem confirmatoryGR_descriptorNondegenerate
    (M : StrategicWorldModel S X A)
    (Σ : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (h : IsConfirmatoryGeneratedRegime M Σ m) :
    IsDescriptorNondegenerate M Σ :=
  h.2

end RegimeSpecification

end PermanssonLean
