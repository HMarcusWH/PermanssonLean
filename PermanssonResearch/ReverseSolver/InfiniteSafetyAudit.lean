import PermanssonResearch.ReverseSolver.InfiniteSafetyLeakage
import PermanssonResearch.ReverseSolver.GreatestControlledInvariant

/-! Reproducible public signatures, transitive axiom reports, and the exact
finite invariant-region regression for the leaking physical system. -/

namespace PermanssonResearch.ReverseSolver.InfiniteSafety

example : invariantCore leakageSystem leakageTarget=∅ := by decide +kernel

#check horizonValue_antitone
#check horizonValue_tendsto
#check limitValue_fixed_point
#check stationaryChoice_fixed_point
#check pathLaw_ae_chronological
#check pathLaw_safeThrough
#check pathLaw_safeForever_eq_iInf
#check infiniteSafety_mass_upper
#check deterministic_stationary_infinite_optimum
#check infiniteSafety_isGreatest
#check invariantIterates_stable
#check invariantCore_eq_valueOneSet
#check invariantCore_iff_almostSureSafety
#check fixed_leakage_tends_to_zero
#check high_actual_finite_survival_zero_infinite

#print axioms horizonValue_antitone
#print axioms horizonValue_tendsto
#print axioms limitValue_fixed_point
#print axioms stationaryChoice_fixed_point
#print axioms pathLaw_ae_chronological
#print axioms pathLaw_safeThrough
#print axioms pathLaw_safeForever_eq_iInf
#print axioms infiniteSafety_mass_upper
#print axioms deterministic_stationary_infinite_optimum
#print axioms infiniteSafety_isGreatest
#print axioms invariantIterates_stable
#print axioms invariantCore_eq_valueOneSet
#print axioms invariantCore_iff_almostSureSafety
#print axioms fixed_leakage_tends_to_zero
#print axioms high_actual_finite_survival_zero_infinite

end PermanssonResearch.ReverseSolver.InfiniteSafety
