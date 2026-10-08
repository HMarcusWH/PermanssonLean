import PermanssonLean.StrategicWorld.PathLaw
import PermanssonLean.Probability.FinitePrefixTV

/-!
# Generic Dirac-start finite trajectory bridge

Keep measurable kernel composition and finite-dimensional trajectory projection
separate from the strategic-world model. No new axioms or assumptions.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace PermanssonResearch
namespace ConstitutiveQuasi

universe uα uβ uY

variable {α : Type uα} {β : Type uβ}
variable [MeasurableSpace α] [MeasurableSpace β]

/-- A general measurable kernel composed with a point mass evaluates at that point. -/
theorem kernel_comp_dirac (η : Kernel α β) (a : α) :
    η ∘ₘ Measure.dirac a = η a := by
  exact Measure.dirac_bind (Kernel.measurable η) a

variable {Y : Type uY} [MeasurableSpace Y]

/-- The finite-prefix marginal of a point-started infinite trajectory
coincides with the associated partial trajectory kernel. -/
theorem trajMeasure_dirac_prefix
    (κ : (n : ℕ) → Kernel ((i : Finset.Iic n) → Y) Y)
    [∀ n, IsMarkovKernel (κ n)]
    (y : Y) (L : ℕ) :
    (Kernel.trajMeasure (Measure.dirac y) κ).map
      (Preorder.frestrictLe L) =
      Kernel.partialTraj κ 0 L (fun _ : Finset.Iic 0 => y) := by
  have hstart :
      (Measure.dirac y).map
        (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Y)).symm =
        Measure.dirac (fun _ : Finset.Iic 0 => y) := by
    rw [Measure.map_dirac' (by fun_prop)]
    rfl
  have heval :
      (Kernel.traj κ 0) ∘ₘ
          Measure.dirac (fun _ : Finset.Iic 0 => y) =
        (Kernel.traj κ 0) (fun _ : Finset.Iic 0 => y) :=
    kernel_comp_dirac (Kernel.traj κ 0) (fun _ => y)
  calc
    (Kernel.trajMeasure (Measure.dirac y) κ).map
        (Preorder.frestrictLe L) =
        ((Kernel.traj κ 0) ∘ₘ
          ((Measure.dirac y).map
            (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Y)).symm)).map
          (Preorder.frestrictLe L) := rfl
    _ = ((Kernel.traj κ 0)
          (fun _ : Finset.Iic 0 => y)).map
          (Preorder.frestrictLe L) := by
      rw [hstart, heval]
    _ = Kernel.partialTraj κ 0 L
        (fun _ : Finset.Iic 0 => y) :=
      Kernel.traj_map_frestrictLe_apply κ 0 L (fun _ => y)

end ConstitutiveQuasi
end PermanssonResearch
