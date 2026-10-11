import PermanssonResearch.MultipleLimit.TypedCanonicalPathBridge
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Tactic

/-!
# Lane C1 — canonical path-law mixture for arbitrary initial distributions

This theorem identifies the actual infinite alpha/P/U path law for every
initial probability measure on the four physical Boolean states, not only
for point starts. Linearity follows directly from Mathlib's Ionescu–Tulcea
measure/bind definition and finite-state Lebesgue integration.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace TypedInitialMixture

open TypedStrategicWitness TypedCanonicalPathBridge
open PermanssonLean.ProbabilitySupport

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

/-- Literal canonical path-event mixture formula, with no assumed affine
dependence on the initial law. This works for every measurable event on
the INFINITE typed trajectory space. -/
theorem typed_pathLaw_event_initial_mixture
    (μ : ProbabilityMeasure Y)
    (E : Set (ℕ → Y)) (hE : MeasurableSet E) :
    model.pathLaw μ.toMeasure E =
      ∑ y : Y, μ.toMeasure {y} *
        (model.pathLaw (Measure.dirac y)) E := by
  classical
  simp_rw [typed_pathLaw_dirac_eq_traj]
  unfold PermanssonLean.StrategicWorldModel.pathLaw
  unfold Kernel.trajMeasure
  rw [Measure.bind_apply hE (Kernel.aemeasurable _)]
  rw [lintegral_map (Kernel.measurable_coe _ hE)
    ((MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Y)).symm.measurable)]
  rw [lintegral_fintype]
  apply Finset.sum_congr rfl
  intro y _
  rw [mul_comm]
  rfl

/-- Exact identity of the actual infinite canonical trajectory measure as
the initial-state mixture of the four genuine point-started path laws. -/
theorem typed_pathLaw_initial_mixture (μ : ProbabilityMeasure Y) :
    model.pathLaw μ.toMeasure =
      ∑ y : Y, μ.toMeasure {y} •
        model.pathLaw (Measure.dirac y) := by
  classical
  ext E hE
  simp only [Measure.finsetSum_apply, Measure.smul_apply]
  exact typed_pathLaw_event_initial_mixture μ E hE

end
end TypedInitialMixture
end MultipleLimit
end PermanssonResearch
