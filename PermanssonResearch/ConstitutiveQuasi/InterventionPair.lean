import PermanssonLean.Intervention.Apply

/-!
# CQ-1 paired admissible strategic interventions

A comparison of two admissible strategic interventions is not a comparison of
arbitrary Markov kernels. Both strategic replacements preserve their own world
primitive, and the approximate baseline is required to share the original P.
-/

namespace PermanssonResearch
namespace ConstitutiveQuasi

universe uS uX uA uC
variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

/-- Typed baseline/intervention pairs for a common state and action space,
and a single fixed structural world primitive. -/
structure StrategicApproximationPair
    (M : PermanssonLean.StrategicWorldModel S X A)
    {Component : Type uC}
    (F : PermanssonLean.InterventionFamily M Component)
    (J : PermanssonLean.AdmissibleStrategicIntervention F) where
  approx : PermanssonLean.StrategicWorldModel S X A
  approxFamily : PermanssonLean.InterventionFamily approx Component
  approxIntervention : PermanssonLean.AdmissibleStrategicIntervention approxFamily
  approx_world_eq : approx.world = M.world

/-- The approximate strategic intervention preserves exactly the original P. -/
theorem StrategicApproximationPair.approxIntervened_world_eq_original
    {M : PermanssonLean.StrategicWorldModel S X A}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    (pair : StrategicApproximationPair M F J) :
    pair.approxIntervention.intervention.apply.world = M.world := by
  calc
    pair.approxIntervention.intervention.apply.world =
        pair.approx.world := pair.approxIntervention.world_eq
    _ = M.world := pair.approx_world_eq

end ConstitutiveQuasi
end PermanssonResearch
