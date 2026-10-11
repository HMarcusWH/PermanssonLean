import PermanssonResearch.MultipleLimit.TypedInitialMixture
import PermanssonResearch.ReverseSolver.CanonicalAllHorizonCorrespondence
import Mathlib.Tactic

/-!
# Lane C1 — genuine typed finite-horizon hitting events

The rational reference first-hitting objectives are pulled back through
the already-certified Boolean-to-Fin4 state bijection and the genuine
canonical prefix marginals of the infinite alpha/P/U process.
This is an exact all-horizon identity; it does not assert infinite-horizon
absorption without the separate geometric-tail theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace TypedCanonicalHitting

open TypedStrategicWitness TypedPrefixEncoding TypedPrefixTransport
open TypedCanonicalPathBridge
open PermanssonResearch.ReverseSolver
open PermanssonLean.ProbabilitySupport

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

/-- The rational first-hitting objective interpreted on the genuine typed
four-state physical space. -/
def typedTarget (rt : RationalHittingTarget 4) : FrozenHittingTarget Y where
  goal := codeState ⁻¹' (rationalTargetAsFrozen rt).goal
  forbidden := codeState ⁻¹' (rationalTargetAsFrozen rt).forbidden
  goal_measurable := MeasurableSet.of_discrete
  forbidden_measurable := MeasurableSet.of_discrete
  disjoint := by
    exact Set.disjoint_left.mpr (by
      intro y hy hz
      exact Set.disjoint_left.mp (rationalTargetAsFrozen rt).disjoint hy hz)

/-- Exact pointwise event equivalence under prefix coding, including the
time-zero success case and the strict-before-forbidden convention. -/
theorem prefixCode_success_preimage (rt : RationalHittingTarget 4) (T : ℕ) :
    prefixCode T ⁻¹'
      successPrefixEvent (rationalTargetAsFrozen rt) T =
      successPrefixEvent (typedTarget rt) T := by
  ext w
  simp [successPrefixEvent, typedTarget, prefixCode]

/-- All finite-prefix hitting values agree with exact rational arithmetic
for the actual alpha/P/U induced kernel, at every state and horizon. -/
theorem typed_hittingValue_eq_rational_all_horizons
    (rt : RationalHittingTarget 4) (y : Y) (T : ℕ) :
    hittingValue (typedTarget rt) model.inducedKernel y T =
      (rationalHittingValue ExactRationalAbsorption.fourStateMatrix rt
        T (codeState y) : ℝ) := by
  unfold hittingValue
  have hmap := typed_prefixLaw_map y T
  have htarget := prefixCode_success_preimage rt T
  have hv :
      (finitePrefixLaw model.inducedKernel y T).real
        (successPrefixEvent (typedTarget rt) T) =
      (finitePrefixLaw
        (rationalFiniteKernel ExactRationalAbsorption.fourStateMatrix)
        (codeState y) T).real
        (successPrefixEvent (rationalTargetAsFrozen rt) T) := by
    unfold Measure.real
    rw [← hmap]
    rw [Measure.map_apply (measurable_prefixCode T)
      (measurableSet_successPrefixEvent (rationalTargetAsFrozen rt) T)]
    rw [htarget]
  rw [hv]
  exact (rationalHittingValue_eq_canonical_all_horizons
    ExactRationalAbsorption.fourStateMatrix rt T (codeState y)).symm

/-- The same exact reachability probability under the actual INFINITE
canonical strategic-world trajectory distribution, restricted to the
prefix through T. -/
theorem typed_pathLaw_hitting_real
    (rt : RationalHittingTarget 4) (y : Y) (T : ℕ) :
    (model.pathLaw (Measure.dirac y)).real
      ((Preorder.frestrictLe T) ⁻¹'
        successPrefixEvent (typedTarget rt) T) =
      (rationalHittingValue ExactRationalAbsorption.fourStateMatrix rt
        T (codeState y) : ℝ) := by
  have hE := measurableSet_successPrefixEvent (typedTarget rt) T
  have hm :
      (model.pathLaw (Measure.dirac y))
        ((Preorder.frestrictLe T) ⁻¹'
          successPrefixEvent (typedTarget rt) T) =
      finitePrefixLaw model.inducedKernel y T
        (successPrefixEvent (typedTarget rt) T) := by
    rw [← typed_pathLaw_prefix_dirac y T]
    exact (Measure.map_apply (Preorder.measurable_frestrictLe T) hE).symm
  unfold Measure.real
  rw [hm]
  exact typed_hittingValue_eq_rational_all_horizons rt y T

/-- Literal t/u finite-horizon absorption event under the true infinite
typed path law: the transient branching state has geometric survival. -/
theorem typed_u_absorption_hitting_all_horizons (T : ℕ) :
    (model.pathLaw (Measure.dirac u)).real
      ((Preorder.frestrictLe T) ⁻¹'
        successPrefixEvent (typedTarget ExactRationalAbsorption.absorbingTarget) T) =
      ((1 - (1/2 : ℚ)^T : ℚ) : ℝ) := by
  rw [typed_pathLaw_hitting_real]
  have h := congrArg (fun q : ℚ => (q : ℝ))
    (ExactRationalAbsorption.hitting_u_closed T)
  simpa [u, codeState] using h

theorem typed_t_absorption_hitting_all_horizons (T : ℕ) :
    (model.pathLaw (Measure.dirac t)).real
      ((Preorder.frestrictLe (T+1)) ⁻¹'
        successPrefixEvent (typedTarget ExactRationalAbsorption.absorbingTarget)
          (T+1)) =
      ((1 - (1/2 : ℚ)^T : ℚ) : ℝ) := by
  rw [typed_pathLaw_hitting_real]
  have h := congrArg (fun q : ℚ => (q : ℝ))
    (ExactRationalAbsorption.hitting_t_closed T)
  simpa [t, codeState] using h

end
end TypedCanonicalHitting
end MultipleLimit
end PermanssonResearch
