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
  ∀ initLaw : ProbabilityMeasure (JointState S X),
    ∃! μ : Measure (ℕ → JointState S X),
      StrategicWorldModel.MarkovPathLawSpec M initLaw.toMeasure μ

theorem canonicalProcessWellPosed
    (M : StrategicWorldModel S X A) :
    CanonicalProcessWellPosed M := by
  intro initLaw
  exact StrategicWorldModel.pathLaw_existsUnique M initLaw.toMeasure

/-- Definition 4.3: Exact Generated Regime.

The reference measure is an explicit frozen input for Assumption 4.1(ii).
The convergence-mode field is part of spec and may encode any precisely
declared ex-ante mode meaningful for every admissible initial law.
-/
def IsExactGeneratedRegime
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X)) : Prop :=
  CanonicalProcessWellPosed M ∧
  Assumption41 M spec m ∧
  IsExactlyInvariant M spec ∧
  ∀ initLaw : ProbabilityMeasure (JointState S X),
    IsAdmissibleInitialLaw spec initLaw →
      IsLimitingOccupationLaw M spec initLaw

/-- Confirmatory GR certificate used in the paper: Exact GR plus
basin-reachable descriptor nondegeneracy.  Forward descriptor richness is
intentionally not made a universal gate. -/
def IsConfirmatoryGeneratedRegime
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X)) : Prop :=
  IsExactGeneratedRegime M spec m ∧
  IsDescriptorNondegenerate M spec

theorem exactGR_wellPosed
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (h : IsExactGeneratedRegime M spec m) :
    CanonicalProcessWellPosed M :=
  h.1

theorem exactGR_assumption41
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (h : IsExactGeneratedRegime M spec m) :
    Assumption41 M spec m :=
  h.2.1

theorem exactGR_exactlyInvariant
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (h : IsExactGeneratedRegime M spec m) :
    IsExactlyInvariant M spec :=
  h.2.2.1

theorem exactGR_limitingOccupation
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (h : IsExactGeneratedRegime M spec m)
    (initLaw : ProbabilityMeasure (JointState S X))
    (hinitLaw : IsAdmissibleInitialLaw spec initLaw) :
    IsLimitingOccupationLaw M spec initLaw :=
  h.2.2.2 initLaw hinitLaw

theorem confirmatoryGR_exact
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (h : IsConfirmatoryGeneratedRegime M spec m) :
    IsExactGeneratedRegime M spec m :=
  h.1

theorem confirmatoryGR_descriptorNondegenerate
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (h : IsConfirmatoryGeneratedRegime M spec m) :
    IsDescriptorNondegenerate M spec :=
  h.2

end RegimeSpecification

end PermanssonLean
