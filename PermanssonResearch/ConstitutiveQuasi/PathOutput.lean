import PermanssonResearch.ConstitutiveQuasi.Definition
import PermanssonLean.Regime.Occupation
import PermanssonLean.StrategicWorld.WellPosedness

/-!
# CQ-1: canonical path laws and finite-prefix evaluation

The first theorem is the main compatibility bridge between the canonical
infinite Ionescu--Tulcea law and the existing finite-prefix law.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch
namespace ConstitutiveQuasi

universe uS uX uA

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

/-- For a point start, the first L+1 coordinates of the canonical infinite
joint path have exactly the core's finite-prefix law through L transitions. -/
theorem pathLaw_finitePrefix_eq
    (M : PermanssonLean.StrategicWorldModel S X A)
    (y : PermanssonLean.JointState S X) (L : ℕ) :
    (M.pathLaw (Measure.dirac y)).map (Preorder.frestrictLe L) =
      PermanssonLean.ProbabilitySupport.finitePrefixLaw M.inducedKernel y L := by
  let κ : (n : ℕ) →
      Kernel ((i : Finset.Iic n) → PermanssonLean.JointState S X)
        (PermanssonLean.JointState S X) :=
    fun n => PermanssonLean.StrategicWorldModel.stationaryHistoryKernel
      M.inducedKernel n
  have hstart :
      (Measure.dirac y).map
          (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 =>
            PermanssonLean.JointState S X)).symm =
        Measure.dirac (PermanssonLean.ProbabilitySupport.singletonPrefix y) := by
    rw [Measure.map_dirac' (by fun_prop)]
    congr 1
    funext i
    simp [PermanssonLean.ProbabilitySupport.singletonPrefix]
  calc
    (M.pathLaw (Measure.dirac y)).map (Preorder.frestrictLe L) =
        ((Kernel.traj κ 0)
          (PermanssonLean.ProbabilitySupport.singletonPrefix y)).map
          (Preorder.frestrictLe L) := by
      change (Kernel.trajMeasure (X := fun _ : ℕ =>
        PermanssonLean.JointState S X) (Measure.dirac y) κ).map
          (Preorder.frestrictLe L) = _
      rw [Kernel.trajMeasure, hstart]
      change (Measure.bind
        (Measure.dirac (PermanssonLean.ProbabilitySupport.singletonPrefix y))
        (Kernel.traj κ 0)).map (Preorder.frestrictLe L) = _
      rw [Measure.dirac_bind (Kernel.measurable _) _]
    _ = PermanssonLean.ProbabilitySupport.finitePrefixLaw M.inducedKernel y L := by
      simpa [PermanssonLean.ProbabilitySupport.finitePrefixLaw,
        PermanssonLean.ProbabilitySupport.stationaryPrefixKernel,
        κ, PermanssonLean.StrategicWorldModel.stationaryHistoryKernel] using
        (Kernel.traj_map_frestrictLe_apply
          (κ := κ) 0 L (PermanssonLean.ProbabilitySupport.singletonPrefix y))

/-- A bounded property evaluated through the infinite canonical path law is
identical to its evaluation through the corresponding finite prefix law. -/
theorem finitePathExpectation_eq_pathLaw
    (M : PermanssonLean.StrategicWorldModel S X A)
    (y : PermanssonLean.JointState S X) (L : ℕ)
    (f : FinitePathProperty (PermanssonLean.JointState S X) L) :
    f.fromKernel L M.inducedKernel y =
      f.expected L
        ((M.pathLaw (Measure.dirac y)).map (Preorder.frestrictLe L)) := by
  letI : IsMarkovKernel M.inducedKernel :=
    PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov M
  rw [pathLaw_finitePrefix_eq]

end ConstitutiveQuasi
end PermanssonResearch
