import PermanssonResearch.RegimeExit.StopHistoryEndpoint
import PermanssonResearch.RegimeExit.StoppedFutureSubmeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic

/-!
# C-Exit C — conditional integration bridge for the endpoint-only restart

This is an implication theorem with an EXPLICIT, outstanding homogeneous
last-state future-law hypothesis. No such hypothesis is installed as an
axiom, no artificial normalization is performed, and this source is NOT
the completed strong Markov proof. The generic stationary-last-state
lemma remains to be constructed independently.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit

set_option autoImplicit false
open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA uH
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X]
variable [MeasurableSpace A] [MeasurableSpace H]

/-- The explicit remaining stationary Markov proof obligation:
the shift of an infinite future law conditioned on a complete
finite history is the original point-started canonical path law
from the last state. This predicate is NOT a proof or certificate. -/
def HasCanonicalLastStateRestart
    (N : StrategicWorldModel S X A) : Prop :=
  ∀ (m : ℕ) (h : (i : Finset.Iic m) → JointState S X),
    canonicalShiftedHistoryKernel N m h =
      canonicalFutureKernel N (h ⟨m, Finset.mem_Iic.mpr le_rfl⟩)

/-- Once the independent last-state property is proved, the exact
whole-future first-exit restart identity follows for EVERY measurable
future event and the original PR66 first-exit submeasure. This bridge
is proved, but its premise is deliberately not claimed. -/
theorem stoppedFuture_measure_restart_of_lastState
    (N : StrategicWorldModel S X A)
    (hLast : HasCanonicalLastStateRestart N)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) {y : JointState S X} (hy : y ∈ spec.region)
    (D : Set (JointState S X)) (hD : MeasurableSet D)
    (F : Set (ℕ → JointState S X)) (hF : MeasurableSet F) :
    finiteStoppedFutureMeasure N spec n y D F =
      ∫⁻ z, (canonicalFutureKernel N z) F
        ∂((firstExitStepMeasure N spec n y).restrict D) := by
  let P := N.pathLaw (Measure.dirac y)
  let μ := P.map (Preorder.frestrictLe (n+1))
  let G := firstExitHistoryAt spec n D
  let last : ((i : Finset.Iic (n+1)) → JointState S X) →
      JointState S X :=
    fun h => h ⟨n+1, Finset.mem_Iic.mpr le_rfl⟩
  have hLastMeas : Measurable last := by fun_prop
  have hFunMeas : Measurable (fun z => (canonicalFutureKernel N z) F) :=
    Kernel.measurable_coe (canonicalFutureKernel N) hF
  have hEndpoint :
      ((μ.restrict G).map last) =
        (firstExitStepMeasure N spec n y).restrict D :=
    firstExitHistory_endpointMeasure_eq_step N spec n hy D hD
  calc
    finiteStoppedFutureMeasure N spec n y D F =
        ∫⁻ h in G,
          (canonicalShiftedHistoryKernel N (n+1) h) F
          ∂μ := by
      exact finiteStoppedFutureMeasure_eq_history N spec n y D hD F hF
    _ = ∫⁻ h in G, (canonicalFutureKernel N (last h)) F ∂μ := by
      simp_rw [hLast (n+1)]
    _ = ∫⁻ z, (canonicalFutureKernel N z) F
          ∂((μ.restrict G).map last) := by
      rw [lintegral_map hFunMeas hLastMeas]
    _ = ∫⁻ z, (canonicalFutureKernel N z) F
          ∂((firstExitStepMeasure N spec n y).restrict D) := by
      rw [hEndpoint]

end PermanssonResearch.RegimeExit
