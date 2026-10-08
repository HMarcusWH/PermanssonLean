import PermanssonResearch.ConstitutiveQuasi.TrajectoryHelpers
import PermanssonResearch.ConstitutiveQuasi.Definition
import PermanssonLean.Regime.Property

/-!
# CQ-1: canonical path laws and finite-prefix evaluation

The trajectory/Dirac reduction lives in a generic lemma so no proof needs
to unfold the Ionescu--Tulcea kernel inside a strategic-world equality.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace PermanssonResearch
namespace ConstitutiveQuasi

universe uS uX uA uY

variable {Y : Type uY} [MeasurableSpace Y]

/-- Lift a finite-prefix score to the original whole-path property interface. -/
noncomputable def FinitePathProperty.toRegimeProperty
    (L : ℕ) (f : FinitePathProperty Y L) :
    PermanssonLean.RegimePropertyMap Y ℝ :=
  fun law => ∫ w, f.score (Preorder.frestrictLe L w) ∂law.toMeasure

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- The canonical infinite point-started path has exactly the core finite-prefix law.
L transitions record coordinates 0 through L. -/
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
  have hkernel :
      (fun n : ℕ =>
        PermanssonLean.ProbabilitySupport.stationaryPrefixKernel M.inducedKernel n) =
        κ := by
    funext n
    rfl
  have hsource :
      M.pathLaw (Measure.dirac y) =
        Kernel.trajMeasure (X := fun _ : ℕ => PermanssonLean.JointState S X) (Measure.dirac y) κ := by
    rfl
  have hfinite :
      Kernel.partialTraj (X := fun _ : ℕ => PermanssonLean.JointState S X) κ 0 L
          (PermanssonLean.ProbabilitySupport.singletonPrefix y) =
        PermanssonLean.ProbabilitySupport.finitePrefixLaw
          M.inducedKernel y L := by
    change Kernel.partialTraj (X := fun _ : ℕ => PermanssonLean.JointState S X) κ 0 L
        (PermanssonLean.ProbabilitySupport.singletonPrefix y) =
      Kernel.partialTraj (X := fun _ : ℕ => PermanssonLean.JointState S X)
        (fun n => PermanssonLean.ProbabilitySupport.stationaryPrefixKernel
          M.inducedKernel n) 0 L
        (PermanssonLean.ProbabilitySupport.singletonPrefix y)
    rw [hkernel]
  calc
    (M.pathLaw (Measure.dirac y)).map (Preorder.frestrictLe L) =
        (Kernel.trajMeasure (X := fun _ : ℕ => PermanssonLean.JointState S X) (Measure.dirac y) κ).map
          (Preorder.frestrictLe L) :=
      congrArg (fun μ : Measure (ℕ → PermanssonLean.JointState S X) =>
        μ.map (Preorder.frestrictLe L)) hsource
    _ = Kernel.partialTraj (X := fun _ : ℕ => PermanssonLean.JointState S X) κ 0 L
        (PermanssonLean.ProbabilitySupport.singletonPrefix y) :=
      trajMeasure_dirac_prefix κ y L
    _ = _ := hfinite

/-- Finite-horizon evaluation agrees between the canonical path and prefix law. -/
theorem finitePathExpectation_eq_pathLaw
    (M : PermanssonLean.StrategicWorldModel S X A)
    (y : PermanssonLean.JointState S X) (L : ℕ)
    (f : FinitePathProperty (PermanssonLean.JointState S X) L) :
    f.fromKernel L M.inducedKernel y =
      f.expected L
        ((M.pathLaw (Measure.dirac y)).map (Preorder.frestrictLe L)) := by
  rw [pathLaw_finitePrefix_eq]
  rfl

/-- The finite-prefix expectation is the frozen regime-property baseline value. -/
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
