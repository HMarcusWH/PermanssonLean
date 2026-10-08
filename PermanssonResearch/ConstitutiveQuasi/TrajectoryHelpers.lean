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

/-- A measurable kernel composed with a Dirac measure evaluates at its point. -/
theorem kernel_comp_dirac (η : Kernel α β) (a : α) :
    η ∘ₘ Measure.dirac a = η a := by
  exact Measure.dirac_bind (Kernel.measurable η) a

variable {Y : Type uY} [MeasurableSpace Y]

/-- Projecting a point-started infinite trajectory to times 0..L gives
the finite trajectory through L transitions, for a constant state space. -/
theorem trajMeasure_dirac_prefix
    (κ : (n : ℕ) → Kernel ((i : Finset.Iic n) → Y) Y)
    [∀ n, IsMarkovKernel (κ n)]
    (y : Y) (L : ℕ) :
    (Kernel.trajMeasure (X := fun _ : ℕ => Y) (Measure.dirac y) κ).map
      (Preorder.frestrictLe L) =
      Kernel.partialTraj (X := fun _ : ℕ => Y) κ 0 L
        (fun _ : Finset.Iic 0 => y) := by
  let w₀ : ((i : Finset.Iic 0) → Y) := fun _ => y
  have hstart :
      (Measure.dirac y).map
        (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Y)).symm =
        Measure.dirac w₀ := by
    rw [Measure.map_dirac' (by fun_prop)]
    rfl
  have heval :
      (Kernel.traj (X := fun _ : ℕ => Y) κ 0) ∘ₘ Measure.dirac w₀ =
        (Kernel.traj (X := fun _ : ℕ => Y) κ 0) w₀ :=
    kernel_comp_dirac (Kernel.traj (X := fun _ : ℕ => Y) κ 0) w₀
  change (Kernel.trajMeasure (X := fun _ : ℕ => Y) (Measure.dirac y) κ).map
    (Preorder.frestrictLe L) =
    Kernel.partialTraj (X := fun _ : ℕ => Y) κ 0 L w₀
  calc
    (Kernel.trajMeasure (X := fun _ : ℕ => Y) (Measure.dirac y) κ).map
        (Preorder.frestrictLe L) =
        ((Kernel.traj (X := fun _ : ℕ => Y) κ 0) ∘ₘ
          ((Measure.dirac y).map
            (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Y)).symm)).map
          (Preorder.frestrictLe L) := rfl
    _ = ((Kernel.traj (X := fun _ : ℕ => Y) κ 0) w₀).map
          (Preorder.frestrictLe L) := by
      rw [hstart, heval]
    _ = Kernel.partialTraj (X := fun _ : ℕ => Y) κ 0 L w₀ := by
      rw [← Kernel.map_apply (Kernel.traj (X := fun _ : ℕ => Y) κ 0)
        (Preorder.measurable_frestrictLe L) w₀]
      exact congrArg
        (fun η : Kernel ((i : Finset.Iic 0) → Y) ((i : Finset.Iic L) → Y) =>
          η w₀)
        (Kernel.traj_map_frestrictLe (κ := κ) 0 L)

end ConstitutiveQuasi
end PermanssonResearch
