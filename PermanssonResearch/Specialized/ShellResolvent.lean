import PermanssonResearch.Specialized.SingularCompatibility
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-! The one-dimensional shell secular function with an arbitrary finite core.
The inverse is genuine at every negative shift. Its derivative is obtained
from Banach-algebra inversion, rather than an assumed resolvent derivative. -/

open scoped InnerProductSpace

namespace PermanssonResearch.Specialized

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def shiftedContinuous (H : E →ₗ[ℝ] E) (ell : ℝ) : E →L[ℝ] E :=
  H.toContinuousLinearMap - ell • ContinuousLinearMap.id ℝ E

noncomputable def negativeShiftUnit (H : E →ₗ[ℝ] E)
    (hpos : ∀ v, 0 ≤ ⟪v, H v⟫_ℝ) {ell : ℝ} (hell : ell < 0) : (E →L[ℝ] E)ˣ where
  val := shiftedContinuous H ell
  inv := (negativeResolventEquiv H hpos hell).symm.toContinuousLinearEquiv.toContinuousLinearMap
  val_inv := by
    ext v
    exact (negativeResolventEquiv H hpos hell).apply_symm_apply v
  inv_val := by
    ext v
    exact (negativeResolventEquiv H hpos hell).symm_apply_apply v

noncomputable def shellResolvent (H : E →ₗ[ℝ] E) (ell : ℝ) : E →L[ℝ] E :=
  Ring.inverse (shiftedContinuous H ell)

theorem shellResolvent_eq_genuine_inverse (H : E →ₗ[ℝ] E)
    (hpos : ∀ v, 0 ≤ ⟪v, H v⟫_ℝ) {ell : ℝ} (hell : ell < 0) (b : E) :
    shellResolvent H ell b = (negativeResolventEquiv H hpos hell).symm b := by
  have he : shiftedContinuous H ell = (negativeShiftUnit H hpos hell : E →L[ℝ] E) := rfl
  unfold shellResolvent
  rw [he, Ring.inverse_unit]
  rfl

theorem shiftedContinuous_symmetric (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    (ell : ℝ) (x y : E) :
    ⟪shiftedContinuous H ell x, y⟫_ℝ = ⟪x, shiftedContinuous H ell y⟫_ℝ := by
  simp only [shiftedContinuous, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    LinearMap.coe_toContinuousLinearMap, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  change ⟪H x, y⟫_ℝ - ell * ⟪x, y⟫_ℝ = ⟪x, H y⟫_ℝ - ell * ⟪x, y⟫_ℝ
  rw [hH]

theorem shellResolvent_solve (H : E →ₗ[ℝ] E)
    (hpos : ∀ v, 0 ≤ ⟪v, H v⟫_ℝ) {ell : ℝ} (hell : ell < 0) (b : E) :
    shiftedContinuous H ell (shellResolvent H ell b) = b := by
  rw [shellResolvent_eq_genuine_inverse H hpos hell]
  exact (negativeResolventEquiv H hpos hell).apply_symm_apply b

theorem shellResolvent_quadratic (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    (hpos : ∀ v, 0 ≤ ⟪v, H v⟫_ℝ) {ell : ℝ} (hell : ell < 0) (b : E) :
    ⟪b, shellResolvent H ell (shellResolvent H ell b)⟫_ℝ =
      ‖shellResolvent H ell b‖ ^ 2 := by
  calc
    _ = ⟪shiftedContinuous H ell (shellResolvent H ell b),
        shellResolvent H ell (shellResolvent H ell b)⟫_ℝ := by
      rw [shellResolvent_solve H hpos hell]
    _ = ⟪shellResolvent H ell b,
        shiftedContinuous H ell (shellResolvent H ell (shellResolvent H ell b))⟫_ℝ :=
      shiftedContinuous_symmetric H hH ell _ _
    _ = _ := by rw [shellResolvent_solve H hpos hell, real_inner_self_eq_norm_sq]

theorem shellResolvent_hasDerivAt (H : E →ₗ[ℝ] E)
    (hpos : ∀ v, 0 ≤ ⟪v, H v⟫_ℝ) {ell : ℝ} (hell : ell < 0) :
    HasDerivAt (shellResolvent H) (shellResolvent H ell * shellResolvent H ell) ell := by
  have hd : HasDerivAt (shiftedContinuous H) (-ContinuousLinearMap.id ℝ E) ell := by
    convert! HasDerivAt.sub (hasDerivAt_const ell H.toContinuousLinearMap)
      ((hasDerivAt_id ell).smul_const (ContinuousLinearMap.id ℝ E)) using 1 <;>
      simp [shiftedContinuous]
  have hi := (hasFDerivAt_ringInverse (𝕜 := ℝ) (negativeShiftUnit H hpos hell)).comp_hasDerivAt ell hd
  have hr : shellResolvent H ell = ((negativeShiftUnit H hpos hell)⁻¹ : (E →L[ℝ] E)ˣ) :=
    Ring.inverse_unit (negativeShiftUnit H hpos hell)
  have hi' : HasDerivAt (shellResolvent H)
      ((↑(negativeShiftUnit H hpos hell)⁻¹ : E →L[ℝ] E) *
        (↑(negativeShiftUnit H hpos hell)⁻¹ : E →L[ℝ] E)) ell := by
    apply hi.congr_deriv
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply,
      neg_mul, mul_neg, neg_neg]
    change _ * (1 : E →L[ℝ] E) * _ = _
    rw [mul_one]
  simpa only [← hr] using hi'

noncomputable def shellResponse (H : E →ₗ[ℝ] E) (b : E) (ell : ℝ) : ℝ :=
  ⟪b, shellResolvent H ell b⟫_ℝ

theorem shellResponse_hasDerivAt (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    (hpos : ∀ v, 0 ≤ ⟪v, H v⟫_ℝ) {ell : ℝ} (hell : ell < 0) (b : E) :
    HasDerivAt (shellResponse H b) (‖shellResolvent H ell b‖ ^ 2) ell := by
  have hv := (shellResolvent_hasDerivAt H hpos hell).clm_apply (hasDerivAt_const ell b)
  have hi := (hasDerivAt_const ell b).inner ℝ hv
  convert! hi using 1 <;>
    simp [shellResponse, ContinuousLinearMap.mul_apply,
      shellResolvent_quadratic H hH hpos hell]

noncomputable def scalarShellSecular (H : E →ₗ[ℝ] E) (b : E) (c ell : ℝ) : ℝ :=
  c - ell - shellResponse H b ell

theorem scalarShellSecular_hasDerivAt (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    (hpos : ∀ v, 0 ≤ ⟪v, H v⟫_ℝ) {ell : ℝ} (hell : ell < 0) (b : E) (c : ℝ) :
    HasDerivAt (scalarShellSecular H b c) (-1 - ‖shellResolvent H ell b‖ ^ 2) ell := by
  convert! HasDerivAt.sub (HasDerivAt.sub (hasDerivAt_const ell c) (hasDerivAt_id ell))
    (shellResponse_hasDerivAt H hH hpos hell b) using 1 <;> simp [scalarShellSecular]

theorem scalarShellSecular_derivative_negative (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    (hpos : ∀ v, 0 ≤ ⟪v, H v⟫_ℝ) {ell : ℝ} (hell : ell < 0) (b : E) (c : ℝ) :
    deriv (scalarShellSecular H b c) ell < 0 := by
  rw [(scalarShellSecular_hasDerivAt H hH hpos hell b c).deriv]
  nlinarith [sq_nonneg ‖shellResolvent H ell b‖]

end PermanssonResearch.Specialized
