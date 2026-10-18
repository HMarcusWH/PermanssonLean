import PermanssonResearch.ReverseSolver.C11ReferenceStationaryFamily
import PermanssonResearch.ReverseSolver.C11TypedStationaryBridge

/-! The total Cramer producer recovers the existing genuine typed C2 class law. -/

namespace PermanssonResearch.ReverseSolver.C11

open C10 FiniteStrategicRealization
open PermanssonResearch.MultipleLimit.ClassStationarySelectionLaw

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

theorem referenceClassCandidate_eq_native {n : ℕ} [NeZero n]
    (K₀ K : RationalMarkovMatrix n) (C : Finset (Fin n)) (hC : C ∈ bottomClasses K) :
    certifiedProbability K (referenceClassCandidate K C) (referenceClassCandidate_check K C hC) =
      stationaryForSet (rationalStrategicIntervention K₀ K).intervention.apply.inducedKernel
        (decodedClass C) :=
  checked_stationary_eq_native K₀ K (referenceClassCandidate K C)
    (referenceClassCandidate_check K C hC)

theorem referenceClassCandidate_positive {n : ℕ} [NeZero n]
    (K₀ K : RationalMarkovMatrix n) (C : Finset (Fin n)) (hC : C ∈ bottomClasses K)
    (x : Fin n) (hx : x ∈ C) : 0<(referenceClassCandidate K C).weights x :=
  checked_stationary_positive_on_class K₀ K (referenceClassCandidate K C)
    (referenceClassCandidate_check K C hC) x hx

end PermanssonResearch.ReverseSolver.C11
