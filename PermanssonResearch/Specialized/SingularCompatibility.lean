import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-! E-SINGULAR and E-SOURCE in the finite real inner-product profile.
Preimages and source identities are explicit data. The exceptional zero
coefficient branch is preserved; no inverse of a singular operator is used. -/

open scoped InnerProductSpace

namespace PermanssonResearch.Specialized

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem symmetric_range_eq_kernel_orthogonal [FiniteDimensional ℝ E]
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) :
    LinearMap.range H = (LinearMap.ker H)ᗮ := by
  rw [← hH.orthogonal_range, Submodule.orthogonal_orthogonal]

theorem symmetric_preimage_iff [FiniteDimensional ℝ E]
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) (b : E) :
    (∃ x, H x = b) ↔ ∀ z, H z = 0 → ⟪z, b⟫_ℝ = 0 := by
  change b ∈ LinearMap.range H ↔ _
  rw [symmetric_range_eq_kernel_orthogonal H hH]
  simp [Submodule.mem_orthogonal, LinearMap.mem_ker]

theorem preimages_differ_by_kernel (H : E →ₗ[ℝ] E) {x y b : E}
    (hx : H x = b) (hy : H y = b) : x - y ∈ LinearMap.ker H := by
  simp [LinearMap.mem_ker, map_sub, hx, hy]

theorem compatible_response_independent (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    {x y b : E} (hx : H x = b) (hy : H y = b) :
    ⟪b, x⟫_ℝ = ⟪b, y⟫_ℝ := by
  have hz : H (x - y) = 0 := by simp [hx, hy]
  have hi : ⟪b, x - y⟫_ℝ = 0 := by rw [← hx, hH, hz, inner_zero_right]
  rw [inner_sub_right] at hi
  linarith

def singularBlockForm (H : E →ₗ[ℝ] E) (b : E) (c : ℝ) (v : E) (t : ℝ) : ℝ :=
  ⟪v, H v⟫_ℝ + 2 * t * ⟪b, v⟫_ℝ + c * t ^ 2

theorem singular_complete_square (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    {b x : E} (hx : H x = b) (c : ℝ) (v : E) (t : ℝ) :
    singularBlockForm H b c v t =
      ⟪v + t • x, H (v + t • x)⟫_ℝ + (c - ⟪b, x⟫_ℝ) * t ^ 2 := by
  have hi : ⟪x, H v⟫_ℝ = ⟪b, v⟫_ℝ := by rw [← hx, hH]
  have hv : ⟪v, b⟫_ℝ = ⟪b, v⟫_ℝ := real_inner_comm _ _
  have hxx : ⟪x, b⟫_ℝ = ⟪b, x⟫_ℝ := real_inner_comm _ _
  simp only [singularBlockForm, map_add, map_smul, hx, inner_add_left,
    inner_add_right, real_inner_smul_left, real_inner_smul_right, hi, hv, hxx]
  ring

theorem singular_block_nonnegative_iff (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    (hpos : ∀ v, 0 ≤ ⟪v, H v⟫_ℝ) {b x : E} (hx : H x = b) (c : ℝ) :
    (∀ v t, 0 ≤ singularBlockForm H b c v t) ↔ 0 ≤ c - ⟪b, x⟫_ℝ := by
  constructor
  · intro h
    have hh := h (-x) 1
    rw [singular_complete_square H hH hx] at hh
    simpa using hh
  · intro hc v t
    rw [singular_complete_square H hH hx]
    exact add_nonneg (hpos _) (mul_nonneg hc (sq_nonneg t))

/-- A source-visible null direction creates a genuine negative block vector. -/
theorem incompatible_kernel_negative (H : E →ₗ[ℝ] E) (b : E) (c : ℝ)
    {z : E} (hz : H z = 0) (hb : ⟪b, z⟫_ℝ ≠ 0) :
    ∃ v, singularBlockForm H b c v 1 < 0 := by
  let s : ℝ := (-c - 1) / (2 * ⟪b, z⟫_ℝ)
  refine ⟨s • z, ?_⟩
  have hs : 2 * s * ⟪b, z⟫_ℝ = -c - 1 := by
    dsimp [s]
    field_simp
    <;> ring
  simp only [singularBlockForm, map_smul, hz, smul_zero, inner_zero_right,
    real_inner_smul_right, one_pow, mul_one, zero_add]
  nlinarith

def shiftedOperator (H : E →ₗ[ℝ] E) (ell : ℝ) : E →ₗ[ℝ] E := H - ell • LinearMap.id

theorem shiftedOperator_injective (H : E →ₗ[ℝ] E)
    (hpos : ∀ v, 0 ≤ ⟪v, H v⟫_ℝ) {ell : ℝ} (hell : ell < 0) :
    Function.Injective (shiftedOperator H ell) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  have heq : H z - ell • z = 0 := hz
  have hi := congrArg (fun v => ⟪z, v⟫_ℝ) heq
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    inner_zero_right] at hi
  have hle : (-ell) * ‖z‖ ^ 2 ≤ 0 := by linarith [hpos z]
  have hsqle : ‖z‖ ^ 2 ≤ 0 :=
    (mul_le_mul_iff_right₀ (neg_pos.mpr hell)).mp (by simpa using hle)
  have hsq : ‖z‖ ^ 2 = 0 := le_antisymm hsqle (sq_nonneg ‖z‖)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)

noncomputable def negativeResolventEquiv [FiniteDimensional ℝ E]
    (H : E →ₗ[ℝ] E) (hpos : ∀ v, 0 ≤ ⟪v, H v⟫_ℝ)
    {ell : ℝ} (hell : ell < 0) : E ≃ₗ[ℝ] E :=
  LinearEquiv.ofBijective (shiftedOperator H ell)
    ⟨shiftedOperator_injective H hpos hell,
      LinearMap.surjective_of_injective (shiftedOperator_injective H hpos hell)⟩

/-- The genuine negative-shift inverse retains the entire kernel obstruction.
The projection is the actual orthogonal projection onto ker H. -/
theorem negative_resolvent_kernel_projection [FiniteDimensional ℝ E]
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    (hpos : ∀ v, 0 ≤ ⟪v, H v⟫_ℝ) {ell : ℝ} (hell : ell < 0) (b : E) :
    (-ell) • (LinearMap.ker H).orthogonalProjectionOnto
      ((negativeResolventEquiv H hpos hell).symm b) =
      (LinearMap.ker H).orthogonalProjectionOnto b := by
  let R := negativeResolventEquiv H hpos hell
  have hsolve : H (R.symm b) - ell • R.symm b = b := R.apply_symm_apply b
  have hzero : (LinearMap.ker H).orthogonalProjectionOnto (H (R.symm b)) = 0 := by
    apply Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal
    rw [← symmetric_range_eq_kernel_orthogonal H hH]
    exact ⟨R.symm b, rfl⟩
  have hp := congrArg ((LinearMap.ker H).orthogonalProjectionOnto) hsolve
  simpa only [map_sub, map_smul, hzero, zero_sub, neg_smul] using hp

section Source

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem denominator_free_kernel_rigidity
    (Hp : E →ₗ[ℝ] E) (Hm : F →ₗ[ℝ] F)
    (hp : Hp.IsSymmetric) (hm : Hm.IsSymmetric)
    (D : E →ₗ[ℝ] F) (Φ β : E → ℝ) (a d bm xm : F) (bp xp : E)
    {np nm : ℝ} (hnp : 0 < np) (hnm : 0 < nm)
    (hxp : Hp xp = bp) (hxm : Hm xm = bm)
    (hβ : ∀ z, β z = ⟪bp, z⟫_ℝ / np)
    (z : E) (hz : Hp z = 0)
    (hsource : Hm (D z) = β z • d + Φ z • a)
    (hnorm : ⟪bm, D z⟫_ℝ / nm = β z + Φ z) :
    (1 - ⟪xm, a⟫_ℝ / nm) * Φ z = 0 := by
  have hβ0 : β z = 0 := by rw [hβ, ← hxp, hp, hz, inner_zero_right, zero_div]
  have hi : ⟪bm, D z⟫_ℝ = Φ z * ⟪xm, a⟫_ℝ := by
    rw [← hxm, hm, hsource, hβ0, zero_smul, zero_add, real_inner_smul_right]
  rw [hi, hβ0, zero_add] at hnorm
  have hh : (Φ z * ⟪xm, a⟫_ℝ) / nm = Φ z := hnorm
  rw [mul_div_assoc] at hh
  nlinarith

theorem source_vanishes_of_nonexceptional
    {Γ value : ℝ} (h : Γ * value = 0) (hΓ : Γ ≠ 0) : value = 0 :=
  (mul_eq_zero.mp h).resolve_left hΓ

/-- The zero-shift response formula retains its source term. -/
theorem zero_shift_source_response
    (Hm : F →ₗ[ℝ] F) (hm : Hm.IsSymmetric)
    (a d bm xm w : F) {nm σp σm φ : ℝ} (hnm : 0 < nm)
    (hxm : Hm xm = bm)
    (hsource : Hm w = σp • d + φ • a)
    (hnorm : ⟪bm, w⟫_ℝ / nm = σp + φ - σm) :
    σm = (1 - ⟪xm, d⟫_ℝ / nm) * σp + (1 - ⟪xm, a⟫_ℝ / nm) * φ := by
  have hi : ⟪bm, w⟫_ℝ = σp * ⟪xm, d⟫_ℝ + φ * ⟪xm, a⟫_ℝ := by
    rw [← hxm, hm, hsource, inner_add_right,
      real_inner_smul_right, real_inner_smul_right]
  rw [hi, add_div, mul_div_assoc, mul_div_assoc] at hnorm
  nlinarith

end Source
end PermanssonResearch.Specialized
