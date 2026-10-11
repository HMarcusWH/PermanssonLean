import PermanssonResearch.MultipleLimit.TypedPrefixTransport
import PermanssonLean.StrategicWorld.PathLaw
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Tactic

/-!
# Lane C1 — point-started infinite path law to finite-prefix marginals

The actual infinite `StrategicWorldModel.pathLaw` is a `trajMeasure`
started from a state-space measure, whereas the independently verified
`finitePrefixLaw` starts at a deterministic length-zero history.
This file proves their precise equality for Dirac starting states.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace TypedCanonicalPathBridge

open TypedStrategicWitness TypedPrefixEncoding TypedPrefixTransport
open PermanssonResearch.ReverseSolver
open PermanssonLean.ProbabilitySupport

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

/-- A Dirac-started canonical path law is the genuine infinite trajectory
kernel evaluated at the corresponding deterministic time-zero history. -/
theorem typed_pathLaw_dirac_eq_traj (y : Y) :
    model.pathLaw (Measure.dirac y) =
      Kernel.traj
        (fun n => PermanssonLean.StrategicWorldModel.stationaryHistoryKernel
          model.inducedKernel n)
        0 (singletonPrefix y) := by
  -- Rewrite only the outer trajectory constructors; do not let
  -- definitional equality recursively unfold the large alpha/P/U kernel.
  unfold PermanssonLean.StrategicWorldModel.pathLaw
  unfold Kernel.trajMeasure
  rw [Measure.map_dirac y]
  change (Measure.dirac
    ((MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Y)).symm y)).bind
      (Kernel.traj
        (fun n => PermanssonLean.StrategicWorldModel.stationaryHistoryKernel
          model.inducedKernel n) 0) = _
  rw [Measure.dirac_bind (Kernel.measurable _)]
  rfl

/-- At every horizon, the actual canonical infinite typed path law has
exactly the independently certified finite-prefix marginal. -/
theorem typed_pathLaw_prefix_dirac (y : Y) (T : ℕ) :
    (model.pathLaw (Measure.dirac y)).map
      (Preorder.frestrictLe T) =
    finitePrefixLaw model.inducedKernel y T := by
  rw [typed_pathLaw_dirac_eq_traj]
  have h := Kernel.traj_map_frestrictLe_apply
    (X := fun _ : ℕ => Y)
    (κ := fun n => PermanssonLean.StrategicWorldModel.stationaryHistoryKernel
      model.inducedKernel n)
    0 T (singletonPrefix y)
  simpa only [finitePrefixLaw,
    PermanssonLean.StrategicWorldModel.stationaryHistoryKernel,
    stationaryPrefixKernel] using h

/-- Full physical-to-rational finite-prefix transport, now applied to
the genuine INFINITE typed canonical path law at a point start. -/
theorem typed_pathLaw_prefix_map (y : Y) (T : ℕ) :
    ((model.pathLaw (Measure.dirac y)).map
      (Preorder.frestrictLe T)).map (prefixCode T) =
    finitePrefixLaw
      (rationalFiniteKernel ExactRationalAbsorption.fourStateMatrix)
      (codeState y) T := by
  rw [typed_pathLaw_prefix_dirac]
  exact typed_prefixLaw_map y T

end
end TypedCanonicalPathBridge
end MultipleLimit
end PermanssonResearch
