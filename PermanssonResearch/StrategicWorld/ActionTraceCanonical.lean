import PermanssonResearch.StrategicWorld.ActionTrace
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Exact finite-dimensional expectations of the canonical action-trace law. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch.ActionTrace

set_option autoImplicit false
universe u
variable {Y A : Type u} [Fintype Y] [Fintype A]
  [MeasurableSpace Y] [MeasurableSpace A]
  [DiscreteMeasurableSpace Y] [DiscreteMeasurableSpace A]

noncomputable def canonicalHistoryKernel (G : Game Y A) (σ : BehavioralPolicy Y A) (n : ℕ) :
    Kernel ((j : Finset.Iic n) → History Y (A × A) j) (History Y (A × A) (n+1)) :=
  (nextKernel G σ n).comap (fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
    Measurable.of_discrete

instance canonicalHistoryKernel_markov (G : Game Y A) (σ : BehavioralPolicy Y A) (n : ℕ) :
    IsMarkovKernel (canonicalHistoryKernel G σ n) := by
  unfold canonicalHistoryKernel
  infer_instance

@[simp] theorem canonicalLaw_eq (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y) :
    canonicalLaw G σ μ = Kernel.trajMeasure μ.measure (canonicalHistoryKernel G σ) := rfl

theorem canonical_prefix_zero (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y) :
    (canonicalLaw G σ μ).map (Preorder.frestrictLe 0) =
      μ.measure.map (MeasurableEquiv.piUnique
        (fun j : Finset.Iic 0 => History Y (A × A) j)).symm := by
  rw [canonicalLaw_eq]
  unfold Kernel.trajMeasure
  rw [Measure.map_comp _ _ (by fun_prop)]
  rw [Kernel.traj_map_frestrictLe]
  simp

theorem canonical_step_pair (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y) (n : ℕ) :
    (canonicalLaw G σ μ).map (Preorder.frestrictLe n) ⊗ₘ canonicalHistoryKernel G σ n =
      (canonicalLaw G σ μ).map
        (fun w => (Preorder.frestrictLe n w, w (n+1))) := by
  rw [canonicalLaw_eq]
  exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

/-- The canonical infinite law has exactly the previously constructed finite
trace expectations, for every complete-history observable and every time.
The reward need not be reconstructed from a state path with missing actions. -/
theorem canonical_expect (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y)
    (n : ℕ) (f : History Y (A × A) n → ℝ) :
    (∫ w, f (w n) ∂canonicalLaw G σ μ) = (law G σ μ n).expect f := by
  induction n with
  | zero =>
      have hh := congrArg (fun ν => ∫ h, f (h ⟨0, by simp⟩) ∂ν)
        (canonical_prefix_zero G σ μ)
      rw [integral_map_of_stronglyMeasurable (by fun_prop) (.of_discrete),
        integral_map_of_stronglyMeasurable (by fun_prop) (.of_discrete)] at hh
      change (∫ w, f (w 0) ∂canonicalLaw G σ μ) = ∫ y, f y ∂μ.measure at hh
      exact hh.trans (Row.expect_eq_integral μ f).symm
  | succ n ih =>
      have hh := congrArg (fun ν => ∫ z, f z.2 ∂ν) (canonical_step_pair G σ μ n)
      rw [Measure.integral_compProd (Integrable.of_finite),
        integral_map_of_stronglyMeasurable (by fun_prop) (.of_discrete)] at hh
      rw [integral_map_of_stronglyMeasurable (by fun_prop) (.of_discrete)] at hh
      change (∫ w, ∫ z, f z ∂(next G σ n (w n)).measure
        ∂canonicalLaw G σ μ) = ∫ w, f (w (n+1)) ∂canonicalLaw G σ μ at hh
      simp_rw [← Row.expect_eq_integral] at hh
      have hi := ih (fun h => (next G σ n h).expect f)
      rw [hi] at hh
      simpa only [law, Row.expect_bind] using hh.symm

end PermanssonResearch.ActionTrace
