import PermanssonResearch.MultipleLimit.FiniteOccupationRandomLaw
import PermanssonResearch.MultipleLimit.TypedRandomOccupation
import Mathlib.Tactic

/-!
# Lane C2 — explicit C1 specialization of the finite recurrent-class theorem

The C1 four-state Bool×Bool strategic-world witness is a particular
finite-state model. This module applies the NEW GENERAL theorem to its
original typed alpha/P/U infinite path law, independently of C1's
absorbing-specific occupation proof.

The limit is expressed as the class-selected stationary law: the C1
absorbing cases can then be identified using their existing terminal
selector, but this theorem does not assume absorption to obtain
empirical convergence.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteC1Specialization

open PermanssonLean
open TypedStrategicWitness
open FiniteCanonicalPath
open FiniteOccupationRandomLaw

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- The previously built C1 strategic-world model is covered, without
new assumptions on its initial law, by the generic C2 Markov occupation
limit theorem. It uses the actual original model.pathLaw measure. -/
theorem c1_physical_occupation_from_general_c2
    (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂model.pathLaw μ.toMeasure,
      Tendsto (fun n : ℕ =>
        FiniteStateOccupation.empiricalOccupation
          w (n+1) (Nat.succ_pos n))
        atTop (𝓝 (physicalOccupationLimit model.inducedKernel w)) := by
  rw [typed_pathLaw_eq_canonical model μ.toMeasure]
  exact physicalOccupationLimit_ae_correct model.inducedKernel μ

end FiniteC1Specialization
end MultipleLimit
end PermanssonResearch
