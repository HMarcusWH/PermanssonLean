import PermanssonResearch.ConstitutiveQuasi.Definition
import PermanssonLean.Regime.Occupation
import PermanssonLean.Regime.Property
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

universe uS uX uA uY

variable {Y : Type uY} [MeasurableSpace Y]

/-- View a finite-prefix score as an ordinary whole-path RegimePropertyMap.
This does not change the frozen definition or introduce a new causal claim. -/
noncomputable def FinitePathProperty.toRegimeProperty
    (L : ℕ) (f : FinitePathProperty Y L) :
    PermanssonLean.RegimePropertyMap Y ℝ :=
  fun law => ∫ w, f.score (Preorder.frestrictLe L w) ∂law.toMeasure

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

-- An established core theorem used as a file-local typeclass instance.
attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

-- The kernel/prefix bridge is proof-engineering intensive on Lean 4.34.0.
set_option maxHeartbeats 800000

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
    rfl
  have hk :
      (fun n : ℕ =>
        PermanssonLean.ProbabilitySupport.stationaryPrefixKernel M.inducedKernel n) =
        κ := by
    funext n
    rfl
  have hpath :
      M.pathLaw (Measure.dirac y) =
        (Kernel.traj κ 0)
          (PermanssonLean.ProbabilitySupport.singletonPrefix y) := by
    change (Kernel.trajMeasure (X := fun _ : ℕ =>
      PermanssonLean.JointState S X) (Measure.dirac y) κ) = _
    rw [Kernel.trajMeasure, hstart]
    exact Measure.dirac_bind (Kernel.measurable (Kernel.traj κ 0))
      (PermanssonLean.ProbabilitySupport.singletonPrefix y)
  have hprefix :
      Kernel.partialTraj κ 0 L
        (PermanssonLean.ProbabilitySupport.singletonPrefix y) =
      PermanssonLean.ProbabilitySupport.finitePrefixLaw M.inducedKernel y L := by
    change Kernel.partialTraj κ 0 L
        (PermanssonLean.ProbabilitySupport.singletonPrefix y) =
      Kernel.partialTraj
        (fun n => PermanssonLean.ProbabilitySupport.stationaryPrefixKernel
          M.inducedKernel n) 0 L
        (PermanssonLean.ProbabilitySupport.singletonPrefix y)
    exact congrArg
      (fun f => Kernel.partialTraj f 0 L
        (PermanssonLean.ProbabilitySupport.singletonPrefix y)) hk.symm
  calc
    (M.pathLaw (Measure.dirac y)).map (Preorder.frestrictLe L) =
        ((Kernel.traj κ 0)
          (PermanssonLean.ProbabilitySupport.singletonPrefix y)).map
            (Preorder.frestrictLe L) := congrArg _ hpath
    _ = Kernel.partialTraj κ 0 L
          (PermanssonLean.ProbabilitySupport.singletonPrefix y) :=
        Kernel.traj_map_frestrictLe_apply
          (κ := κ) 0 L (PermanssonLean.ProbabilitySupport.singletonPrefix y)
    _ = _ := hprefix

/-- A bounded property evaluated through the infinite canonical path law is
identical to its evaluation through the corresponding finite prefix law. -/
theorem finitePathExpectation_eq_pathLaw
    (M : PermanssonLean.StrategicWorldModel S X A)
    (y : PermanssonLean.JointState S X) (L : ℕ)
    (f : FinitePathProperty (PermanssonLean.JointState S X) L) :
    f.fromKernel L M.inducedKernel y =
      f.expected L
        ((M.pathLaw (Measure.dirac y)).map (Preorder.frestrictLe L)) := by
  rw [pathLaw_finitePrefix_eq]
  rfl

/-- Finite-prefix expectations are the baseline values of an existing
RegimePropertyMap, so future CQ-1 constitution uses the frozen property API. -/
theorem finitePathExpectation_eq_baselineProperty
    (M : PermanssonLean.StrategicWorldModel S X A)
    (y : PermanssonLean.JointState S X) (L : ℕ)
    (f : FinitePathProperty (PermanssonLean.JointState S X) L) :
    f.fromKernel L M.inducedKernel y =
      PermanssonLean.RegimeSpecification.baselinePropertyValue
        (f.toRegimeProperty L) M y := by
  calc
    f.fromKernel L M.inducedKernel y =
        ∫ z, f.score z ∂(M.pathLaw (Measure.dirac y)).map
          (Preorder.frestrictLe L) := finitePathExpectation_eq_pathLaw M y L f
    _ = ∫ w, f.score (Preorder.frestrictLe L w) ∂M.pathLaw (Measure.dirac y) := by
      exact integral_map (by fun_prop) f.measurable_score.aestronglyMeasurable
    _ = _ := rfl

end ConstitutiveQuasi
end PermanssonResearch
