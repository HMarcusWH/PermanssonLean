import PermanssonResearch.RegimeExit.ExitConservation
import PermanssonLean.Regime.GeneratedRegime
import PermanssonLean.Regime.Constitution
import PermanssonLean.Regime.Persistence
import Mathlib.Tactic

/-!
# C-Exit B — typed source/target certificates and actual routing

The destination is an *independently* certified Exact GR for the actual
strategically intervened canonical model. No stopping-time law, occupancy
transfer, or strategic constitution is installed as an assumption.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace PermanssonResearch.RegimeExit

set_option autoImplicit false

open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA uH uT uK

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {H : Type uH} {T : Type uT}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H] [MeasurableSpace T]
variable [TopologicalSpace S] [TopologicalSpace X]

/-- The actual baseline and intervened canonical models each carry their
own Exact-GR evidence. The reference measures and descriptors may differ.
The comparison set and strategic intervention are the ORIGINAL typed ones. -/
structure CertifiedSwitchData
    (M : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    (mSource mTarget : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M source)
    (J : AdmissibleStrategicIntervention F) : Prop where
  sourceExact : IsExactGeneratedRegime M source mSource
  targetExact : IsExactGeneratedRegime J.intervention.apply target mTarget
  disjointRegions : Disjoint source.region target.region

/-- A predeclared infinite-horizon first-exit routing certificate.
An eta of one is allowed but does not establish positive constitution. -/
def SwitchRoutingBound
    (M : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M source)
    (J : AdmissibleStrategicIntervention F)
    (eta : ℝ≥0∞) : Prop :=
  eta ≤ 1 ∧
    ∀ y ∈ B₁.states,
      1 - eta ≤
        exitRoutingInfinite J.intervention.apply source y target.basin

/-- The PR66 routing result really is a statement about canonical first-exit
path events; it cannot be replaced with an arbitrary externally supplied
matrix or a finite-hit surrogate. -/
theorem switch_first_exit_event_lower_bound
    (M : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M source)
    (J : AdmissibleStrategicIntervention F)
    (eta : ℝ≥0∞)
    (hBound : SwitchRoutingBound M source target F B₁ J eta)
    {y : JointState S X} (hy : y ∈ B₁.states) :
    1 - eta ≤
      J.intervention.apply.pathLaw (Measure.dirac y)
        (firstExitEverDestination source target.basin) := by
  calc
    1 - eta ≤
        exitRoutingInfinite J.intervention.apply source y target.basin :=
      hBound.2 y hy
    _ = J.intervention.apply.pathLaw (Measure.dirac y)
          (firstExitEverDestination source target.basin) :=
      exitRoutingInfinite_eq_prob_exit_in J.intervention.apply source
        (B₁.states_subset_region hy) target.basin
        target.basin_measurable

/-- The source regime remains invariant under the ORIGINAL model. -/
theorem switch_source_baseline_survival_one
    (M : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    (mSource mTarget : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M source)
    (J : AdmissibleStrategicIntervention F)
    (cert : CertifiedSwitchData M source target mSource mTarget F B₁ J)
    {y : JointState S X} (hy : y ∈ B₁.states) :
    survivalForeverProbability M source y = 1 := by
  exact exactInvariant_survivalForever M source
    (exactGR_exactlyInvariant M source mSource cert.sourceExact)
    (B₁.states_subset_region hy)

/-- Arrival in the certified target basin grants probability-one survival
from that arrival state under the SAME permanently intervened model. -/
theorem switch_target_point_survival_one
    (M : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    (mSource mTarget : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M source)
    (J : AdmissibleStrategicIntervention F)
    (cert : CertifiedSwitchData M source target mSource mTarget F B₁ J)
    {z : JointState S X} (hz : z ∈ target.basin) :
    survivalForeverProbability J.intervention.apply target z = 1 := by
  exact exactInvariant_survivalForever J.intervention.apply target
    (exactGR_exactlyInvariant J.intervention.apply target mTarget
      cert.targetExact)
    (target.basin_subset_region hz)

/-- The intervention remains strategic: the world-transition primitive P
is identical to the baseline, independently of both regime certificates. -/
theorem switch_world_primitive_fixed
    (M : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M source)
    (J : AdmissibleStrategicIntervention F) :
    J.intervention.apply.world = M.world := J.world_eq

end PermanssonResearch.RegimeExit
