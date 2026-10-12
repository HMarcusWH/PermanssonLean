import PermanssonResearch.MultipleLimit.FiniteOccupationOutside
import PermanssonResearch.MultipleLimit.FiniteOccupationLimitFromResidual
import PermanssonResearch.MultipleLimit.ClassStationarySelectionLaw
import Mathlib.Tactic

/-!
# Lane C2 — classwise empirical convergence from a genuine residual strong law

The invariant probability π_C is CONSTRUCTED unconditionally by the
separate finite class invariant-measure theorem. The present bridge proves
that whenever the actual normalized empirical stationarity residual vanishes
and the true path eventually resides in a recurrent class, the whole
finite-state empirical vector converges to its UNIQUE π_C.

Its canonical a.e. corollary explicitly exposes the remaining Markov
martingale strong law hypothesis; that hypothesis must be discharged
separately before claiming unconditional occupation ergodicity.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteClassOccupation

open KernelCommunication
open RecurrentClassDecomposition
open FiniteCanonicalPath
open CanonicalClassWeights
open CanonicalClassSelector
open CanonicalRecurrentResidence
open ClassStationarySelectionLaw
open FiniteOccupationOutside
open FiniteOccupationVector
open FiniteCesaroAlgebra
open FiniteOccupationLimitFromResidual
open FiniteKernelRealBridge
open FiniteKernelInvariantUniqueness
open FiniteClassInvariantMeasure

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y] [DecidableEq Y]
variable [MeasurableSingletonClass Y] [Nonempty Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- The compactness/unique-stationary theorem instantiated on the
TRUE invariant probability of a given closed recurrent communicating
class. The only analytic input is the residual limit, not a presumed
occupation limit or stationary starting distribution. -/
theorem class_empirical_vector_limit_of_residual
    (c : Y) (hc : IsRecurrentState K c)
    (w : ℕ → Y)
    (hE : EventuallyInClass w (CommunicatingClass K c))
    (hres : ∀ z : Y,
      Tendsto
        (fun n : ℕ =>
          pushVector (realTransition K) (empiricalVector w n) z -
            empiricalVector w n z) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => empiricalVector w n) atTop
      (𝓝 (realPointMass
        (stationaryForSet K (CommunicatingClass K c)))) := by
  classical
  have hC : CommunicatingClass K c ∈ RecurrentClasses K :=
    (recurrentClasses_mem_iff K _).mpr ⟨c, hc, rfl⟩
  let π := stationaryForSet K (CommunicatingClass K c)
  have hπ : Kernel.Invariant K π.toMeasure ∧
      π.toMeasure (CommunicatingClass K c) = 1 :=
    stationaryForSet_spec K hC
  exact tendsto_unique_stationary_of_residual
    (realTransition K) (realTransition_nonneg K)
    (CommunicatingClass K c)
    (class_real_irreducible K c)
    (realPointMass π)
    (realPointMass_nonneg π)
    (realPointMass_total π)
    (realPointMass_stationary K π hπ.1)
    (realPointMass_supported_of_class π _ hπ.2)
    (fun n => empiricalVector w n)
    (fun n z => empiricalVector_nonneg w n z)
    (fun n => empiricalVector_total w n)
    hres
    (fun z hz =>
      empiricalVector_tendsto_zero_of_eventuallyInClass
        w (CommunicatingClass K c) hE z hz)

/-- All-chain CANONICAL bridge, conditional solely on the actual
finite-state martingale/residual strong law. Earlier C2 theorems
already establish the almost-sure correct recurrent-class selector,
its actual stationary law, and eventual residence in that class. -/
theorem canonical_empirical_vector_limit_of_residual
    (μ : ProbabilityMeasure Y)
    (hres : ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      ∀ z : Y,
        Tendsto (fun n : ℕ =>
          pushVector (realTransition K) (empiricalVector w n) z -
            empiricalVector w n z) atTop (𝓝 0)) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n : ℕ => empiricalVector w n) atTop
        (𝓝 (realPointMass
          (stationaryForSet K (CommunicatingClass K
            (selectedRepresentative K w))))) := by
  filter_upwards [selected_class_eventual_ae K μ, hres]
    with w hw hr
  exact class_empirical_vector_limit_of_residual K
    (selectedRepresentative K w)
    (selectedRepresentative_recurrent K w)
    w hw hr

end FiniteClassOccupation
end MultipleLimit
end PermanssonResearch
