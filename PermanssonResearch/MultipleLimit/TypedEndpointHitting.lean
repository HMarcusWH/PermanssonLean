import PermanssonResearch.MultipleLimit.ExactEndpointRecurrences
import PermanssonResearch.MultipleLimit.TypedCanonicalHitting
import Mathlib.Tactic

/-!
# Lane C1 — actual typed canonical probabilities for each endpoint

These are finite-horizon cylinder events of the literal infinite
alpha/P/U canonical process. Their exact destination-specific values
are transported from the independently certified rational recurrences.
The eventual terminal endpoint law requires an additional passage to
the infinite union and absorbing-continuation theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace TypedEndpointHitting

open TypedStrategicWitness TypedCanonicalHitting
open ExactEndpointRecurrences

noncomputable section

def hitA (T : ℕ) : Set (ℕ → Y) :=
  (Preorder.frestrictLe T) ⁻¹'
    ReverseSolver.successPrefixEvent (typedTarget aTarget) T

def hitB (T : ℕ) : Set (ℕ → Y) :=
  (Preorder.frestrictLe T) ⁻¹'
    ReverseSolver.successPrefixEvent (typedTarget bTarget) T

theorem hitA_measurable (T : ℕ) : MeasurableSet (hitA T) :=
  (ReverseSolver.measurableSet_successPrefixEvent (typedTarget aTarget) T).preimage
    (Preorder.measurable_frestrictLe T)

theorem hitB_measurable (T : ℕ) : MeasurableSet (hitB T) :=
  (ReverseSolver.measurableSet_successPrefixEvent (typedTarget bTarget) T).preimage
    (Preorder.measurable_frestrictLe T)

theorem canonical_hitA_u (T : ℕ) :
    (model.pathLaw (Measure.dirac u)).real (hitA T) =
      ((1/3 : ℚ) * (1 - (1/2 : ℚ)^T) : ℝ) := by
  unfold hitA
  rw [typed_pathLaw_hitting_real]
  have h := congrArg (fun q : ℚ => (q : ℝ)) (hit_a_from_u_closed T)
  simpa [u, codeState] using h

theorem canonical_hitB_u (T : ℕ) :
    (model.pathLaw (Measure.dirac u)).real (hitB T) =
      ((2/3 : ℚ) * (1 - (1/2 : ℚ)^T) : ℝ) := by
  unfold hitB
  rw [typed_pathLaw_hitting_real]
  have h := congrArg (fun q : ℚ => (q : ℝ)) (hit_b_from_u_closed T)
  simpa [u, codeState] using h

theorem canonical_hitA_t (T : ℕ) :
    (model.pathLaw (Measure.dirac t)).real (hitA (T+1)) =
      ((1/3 : ℚ) * (1 - (1/2 : ℚ)^T) : ℝ) := by
  unfold hitA
  rw [typed_pathLaw_hitting_real]
  have h := congrArg (fun q : ℚ => (q : ℝ)) (hit_a_from_t_closed T)
  simpa [t, codeState] using h

theorem canonical_hitB_t (T : ℕ) :
    (model.pathLaw (Measure.dirac t)).real (hitB (T+1)) =
      ((2/3 : ℚ) * (1 - (1/2 : ℚ)^T) : ℝ) := by
  unfold hitB
  rw [typed_pathLaw_hitting_real]
  have h := congrArg (fun q : ℚ => (q : ℝ)) (hit_b_from_t_closed T)
  simpa [t, codeState] using h

end
end TypedEndpointHitting
end MultipleLimit
end PermanssonResearch
