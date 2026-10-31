import PermanssonResearch.Specialized.SeamReduction
import PermanssonResearch.Specialized.ShellSchur
import PermanssonResearch.Specialized.SingularCompatibility
import PermanssonResearch.Specialized.GramSeparation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

/-!
# ApplicationBridge — finite rational real-algebra witnesses

Finite rational matrices and vectors are cast into real matrices and the
Euclidean space `EuclideanSpace ℝ (Fin n)`; the decidable checks below are
evaluated on the rationals, and the conclusions are Research's specialized
theorems for the cast objects:

* seam: a symmetric matrix with vanishing seam equations at a pivot has real
  rank at most two (`seam_rank_le_two`); with a constant diagonal every entry
  is that constant, the rank is at most one and the quadratic form is
  `δ (Σ v)²`;
* shell Schur: `H = L diag(d) Lᵀ` with `d ≥ 0` is positive semidefinite, and
  for `ℓ < 0` a solution `X` of `(H − ℓ) X = B` identifies the shell
  complement with the declared `S`; the block determinant factorizes and the
  shell equations reduce to `S w = 0` (`shell_determinant`,
  `shell_equations_iff`);
* singular compatibility: for positive semidefinite symmetric `H`, a declared
  preimage `x` of `b` makes nonnegativity of the bordered form equivalent to
  `0 ≤ c − ⟪b, x⟫`, and every preimage has the same response; a kernel vector
  `z` with `⟪b, z⟫ ≠ 0` rules out every preimage and gives a negative value;
* Gram: a positive Gram gap gives a nonzero witness on which the signed form
  is negative, robustly for every operator perturbation below the exact
  threshold `c · gap / ‖x‖²`.

Source-to-feature or source-to-operator identification is not part of these
checks and is not claimed; arbitrary Hilbert or complex objects are not
encoded.
-/

namespace PermanssonResearch.ApplicationBridge.RationalAlgebraReceipt

open Matrix
open scoped InnerProductSpace
open PermanssonResearch.Specialized

set_option autoImplicit false

variable {n m : ℕ}

/-- Real matrix of a rational matrix. -/
noncomputable abbrev rm {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℚ) : Matrix (Fin a) (Fin b) ℝ := A.map (Rat.castHom ℝ)

theorem rm_apply {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℚ) (i : Fin a) (j : Fin b) :
    rm A i j = (A i j : ℝ) := rfl

theorem rm_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℚ) (B : Matrix (Fin b) (Fin c) ℚ) :
    rm (A * B) = rm A * rm B := Matrix.map_mul

theorem rm_sub {a b : ℕ} (A B : Matrix (Fin a) (Fin b) ℚ) : rm (A - B) = rm A - rm B := by
  ext i j; simp

theorem rm_transpose {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℚ) : rm Aᵀ = (rm A)ᵀ := by
  ext i j; simp

/-- Euclidean vector of a rational vector. -/
noncomputable abbrev ev (v : Fin n → ℚ) : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => (v i : ℝ))

theorem inner_ev (a b : Fin n → ℚ) : ⟪ev a, ev b⟫_ℝ = ((∑ i, a i * b i : ℚ) : ℝ) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, mul_comm]

theorem norm_sq_ev (a : Fin n → ℚ) : ‖ev a‖ ^ 2 = ((∑ i, a i * a i : ℚ) : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, inner_ev]

theorem toEuclideanLin_ev (H : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ) :
    toEuclideanLin (rm H) (ev v) = ev (H *ᵥ v) := by
  ext i
  simp [Matrix.mulVec, dotProduct]

/-! ## Seam -/

/-- All seam expressions at the pivot `p`. -/
def seamMatrix (H : Matrix (Fin n) (Fin n) ℚ) (p : Fin n) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => H i j - H i p - H p j + H p p

def SeamChecks (H : Matrix (Fin n) (Fin n) ℚ) (p : Fin n) : Prop :=
  Hᵀ = H ∧ seamMatrix H p = 0

instance (H : Matrix (Fin n) (Fin n) ℚ) (p : Fin n) : Decidable (SeamChecks H p) := by
  unfold SeamChecks; infer_instance

def checkSeam (H : Matrix (Fin n) (Fin n) ℚ) (p : Fin n) : Bool := decide (SeamChecks H p)

theorem seam_cast (H : Matrix (Fin n) (Fin n) ℚ) (p : Fin n) (h : checkSeam H p = true) :
    (∀ i j, rm H i j = rm H j i) ∧ ∀ i j, seam (rm H) p i j = 0 := by
  obtain ⟨hs, hz⟩ := of_decide_eq_true h
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have hij : H i j = H j i := by
      have := congrFun (congrFun hs j) i
      simpa using this
    rw [rm_apply, rm_apply, hij]
  · have := congrFun (congrFun hz i) j
    simp only [seamMatrix, Matrix.of_apply, Matrix.zero_apply] at this
    unfold seam
    simp only [rm_apply]
    exact_mod_cast this

/-- **Seam.** Vanishing seam equations bound the real rank by two. -/
theorem checked_seam_rank (H : Matrix (Fin n) (Fin n) ℚ) (p : Fin n) (h : checkSeam H p = true) :
    (rm H).rank ≤ 2 := by
  obtain ⟨hs, hz⟩ := seam_cast H p h
  exact seam_rank_le_two (rm H) p hs hz

/-- **Common mode.** With a constant diagonal every entry is that constant,
    the rank is at most one and the quadratic form is `δ (Σ v)²`. -/
theorem checked_common_mode (H : Matrix (Fin n) (Fin n) ℚ) (p : Fin n) (δ : ℚ)
    (h : checkSeam H p = true) (hdiag : decide (Matrix.diag H = fun _ => δ) = true) :
    (∀ i j, rm H i j = δ) ∧ (rm H).rank ≤ 1 ∧
      ∀ v : Fin n → ℝ, quadratic (rm H) v = (δ : ℝ) * (∑ i, v i) ^ 2 := by
  obtain ⟨hs, hz⟩ := seam_cast H p h
  have hd : ∀ i, rm H i i = δ := fun i => by
    rw [rm_apply]; exact_mod_cast congrFun (of_decide_eq_true hdiag) i
  have hc := seam_constant_diagonal (rm H) p δ hs hz hd
  exact ⟨hc, commonMode_rank_le_one (rm H) δ hc, quadratic_commonMode (rm H) δ hc⟩

/-! ## Positive semidefinite witnesses -/

/-- `H = L diag(d) Lᵀ` with `d ≥ 0`. -/
def PSDWitness (H L : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ) : Prop :=
  H = L * Matrix.diagonal d * Lᵀ ∧ ∀ i, 0 ≤ d i

instance (H L : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ) : Decidable (PSDWitness H L d) := by
  unfold PSDWitness; infer_instance

theorem psd_of_witness (H L : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ) (h : PSDWitness H L d) :
    (rm H).PosSemidef := by
  obtain ⟨hH, hd⟩ := h
  have hD : (Matrix.diagonal (fun i => (d i : ℝ))).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (fun i => by exact_mod_cast hd i)
  have := hD.mul_mul_conjTranspose_same (rm L)
  have hcast : rm H = rm L * Matrix.diagonal (fun i => (d i : ℝ)) * (rm L)ᴴ := by
    rw [hH, rm_mul, rm_mul, rm_transpose, Matrix.conjTranspose_eq_transpose_of_trivial]
    congr 2
    exact Matrix.diagonal_map (map_zero _)
  rw [hcast]
  exact this

/-! ## Shell Schur complement -/

def SchurChecks (H L : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ) (B X : Matrix (Fin n) (Fin m) ℚ)
    (C S : Matrix (Fin m) (Fin m) ℚ) (ell : ℚ) : Prop :=
  PSDWitness H L d ∧ ell < 0 ∧ (H - ell • (1 : Matrix (Fin n) (Fin n) ℚ)) * X = B ∧
    S = (C - ell • (1 : Matrix (Fin m) (Fin m) ℚ)) - Bᵀ * X

instance (H L : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ) (B X : Matrix (Fin n) (Fin m) ℚ)
    (C S : Matrix (Fin m) (Fin m) ℚ) (ell : ℚ) : Decidable (SchurChecks H L d B X C S ell) := by
  unfold SchurChecks PSDWitness; infer_instance

def checkSchur (H L : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ) (B X : Matrix (Fin n) (Fin m) ℚ)
    (C S : Matrix (Fin m) (Fin m) ℚ) (ell : ℚ) : Bool := decide (SchurChecks H L d B X C S ell)

theorem shift_cast {a : ℕ} (H : Matrix (Fin a) (Fin a) ℚ) (ell : ℚ) :
    rm (H - ell • (1 : Matrix (Fin a) (Fin a) ℚ)) = negativeShift (rm H) (ell : ℝ) := by
  ext i j
  simp only [negativeShift, rm_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

/-- **Shell Schur.** The shell complement is the declared `S`, the block
    determinant factorizes through it and the shell equations reduce to it. -/
theorem checked_schur (H L : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ) (B X : Matrix (Fin n) (Fin m) ℚ)
    (C S : Matrix (Fin m) (Fin m) ℚ) (ell : ℚ) (h : checkSchur H L d B X C S ell = true) :
    (rm H).PosSemidef ∧ shellComplement (rm H) (rm B) (rm C) (ell : ℝ) = rm S ∧
    (Matrix.fromBlocks (negativeShift (rm H) ell) (rm B) (rm B)ᵀ (negativeShift (rm C) ell)).det =
      (negativeShift (rm H) ell).det * (rm S).det ∧
    ∀ (v : Fin n → ℝ) (w : Fin m → ℝ),
      ((negativeShift (rm H) ell) *ᵥ v + rm B *ᵥ w = 0 ∧
        (rm B)ᵀ *ᵥ v + (negativeShift (rm C) ell) *ᵥ w = 0) ↔
      (v = -((negativeShift (rm H) ell)⁻¹ *ᵥ (rm B *ᵥ w)) ∧ rm S *ᵥ w = 0) := by
  obtain ⟨hpsd, hell, hX, hS⟩ := of_decide_eq_true h
  have hH := psd_of_witness H L d hpsd
  have hellr : (ell : ℝ) < 0 := by exact_mod_cast hell
  have hunit := negativeShift_isUnit (rm H) hH hellr
  have hXr : negativeShift (rm H) ell * rm X = rm B := by
    rw [← shift_cast, ← rm_mul, hX]
  have hinv : (negativeShift (rm H) ell)⁻¹ * rm B = rm X := by
    rw [← hXr, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit),
      Matrix.one_mul]
  have hcomp : shellComplement (rm H) (rm B) (rm C) (ell : ℝ) = rm S := by
    unfold shellComplement
    rw [Matrix.mul_assoc, hinv, hS, rm_sub, rm_mul, rm_transpose, shift_cast]
  refine ⟨hH, hcomp, ?_, fun v w => ?_⟩
  · rw [shell_determinant (rm H) hH (rm B) (rm C) hellr, hcomp]
  · rw [shell_equations_iff (rm H) hH (rm B) (rm C) hellr v w, hcomp]

/-! ## Singular compatibility -/

noncomputable abbrev op (H : Matrix (Fin n) (Fin n) ℚ) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  toEuclideanLin (rm H)

theorem op_positive (H L : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ) (h : PSDWitness H L d) :
    (op H).IsSymmetric ∧ ∀ v, 0 ≤ ⟪v, op H v⟫_ℝ := by
  have hP : (op H).IsPositive := Matrix.isPositive_toEuclideanLin_iff.mpr (psd_of_witness H L d h)
  refine ⟨hP.isSymmetric, fun v => ?_⟩
  have := hP.re_inner_nonneg_right v
  simpa using this

/-- Compatible: `H x = b`, with the gap `g = c − ⟪b, x⟫`. -/
def CompatibleChecks (H L : Matrix (Fin n) (Fin n) ℚ) (d b x : Fin n → ℚ) (c g : ℚ) : Prop :=
  PSDWitness H L d ∧ H *ᵥ x = b ∧ g = c - ∑ i, b i * x i

instance (H L : Matrix (Fin n) (Fin n) ℚ) (d b x : Fin n → ℚ) (c g : ℚ) :
    Decidable (CompatibleChecks H L d b x c g) := by
  unfold CompatibleChecks PSDWitness; infer_instance

def checkCompatible (H L : Matrix (Fin n) (Fin n) ℚ) (d b x : Fin n → ℚ) (c g : ℚ) : Bool :=
  decide (CompatibleChecks H L d b x c g)

/-- **Compatible singular block.** Nonnegativity of the bordered form is
    exactly `0 ≤ g`, and every preimage of `b` has response `c − g`. -/
theorem checked_compatible (H L : Matrix (Fin n) (Fin n) ℚ) (d b x : Fin n → ℚ) (c g : ℚ)
    (h : checkCompatible H L d b x c g = true) :
    ((∀ v t, 0 ≤ singularBlockForm (op H) (ev b) c v t) ↔ 0 ≤ (g : ℝ)) ∧
    ∀ y, op H y = ev b → ⟪ev b, y⟫_ℝ = (c : ℝ) - g := by
  obtain ⟨hpsd, hx, hg⟩ := of_decide_eq_true h
  obtain ⟨hsym, hpos⟩ := op_positive H L d hpsd
  have hxr : op H (ev x) = ev b := by rw [toEuclideanLin_ev, hx]
  have hresp : ⟪ev b, ev x⟫_ℝ = (c : ℝ) - g := by
    rw [inner_ev, hg]; push_cast; ring
  refine ⟨?_, fun y hy => ?_⟩
  · rw [singular_block_nonnegative_iff (op H) hsym hpos hxr c, hresp]
    constructor <;> intro hh <;> linarith
  · rw [compatible_response_independent (op H) hsym hy hxr, hresp]

/-- Incompatible: a kernel vector `z` with `⟪b, z⟫ ≠ 0`. -/
def IncompatibleChecks (H L : Matrix (Fin n) (Fin n) ℚ) (d b z : Fin n → ℚ) : Prop :=
  PSDWitness H L d ∧ H *ᵥ z = 0 ∧ (∑ i, b i * z i) ≠ 0

instance (H L : Matrix (Fin n) (Fin n) ℚ) (d b z : Fin n → ℚ) :
    Decidable (IncompatibleChecks H L d b z) := by
  unfold IncompatibleChecks PSDWitness; infer_instance

def checkIncompatible (H L : Matrix (Fin n) (Fin n) ℚ) (d b z : Fin n → ℚ) : Bool :=
  decide (IncompatibleChecks H L d b z)

/-- **Incompatible singular block.** No preimage of `b` exists and the
    bordered form takes a negative value for every `c`. -/
theorem checked_incompatible (H L : Matrix (Fin n) (Fin n) ℚ) (d b z : Fin n → ℚ)
    (h : checkIncompatible H L d b z = true) (c : ℝ) :
    (¬ ∃ x, op H x = ev b) ∧ ∃ v, singularBlockForm (op H) (ev b) c v 1 < 0 := by
  obtain ⟨hpsd, hz, hb⟩ := of_decide_eq_true h
  obtain ⟨hsym, -⟩ := op_positive H L d hpsd
  have hzr : op H (ev z) = 0 := by
    rw [toEuclideanLin_ev, hz]; ext i; simp
  have hbz : ⟪ev b, ev z⟫_ℝ ≠ 0 := by
    rw [inner_ev]; exact_mod_cast hb
  refine ⟨fun hex => ?_, incompatible_kernel_negative (op H) (ev b) c hzr hbz⟩
  have := (symmetric_preimage_iff (op H) hsym (ev b)).mp hex (ev z) hzr
  rw [real_inner_comm] at this
  exact hbz this

/-! ## Gram separation -/

def GramChecks (x y w : Fin n → ℚ) (c gap τ : ℚ) : Prop :=
  0 < c ∧ gap = (∑ i, x i * x i) * (∑ i, y i * y i) - (∑ i, x i * y i) ^ 2 ∧ 0 < gap ∧
  (∀ i, w i = (∑ j, x j * x j) * y i - (∑ j, x j * y j) * x i) ∧
  τ * (∑ i, x i * x i) = c * gap

instance (x y w : Fin n → ℚ) (c gap τ : ℚ) : Decidable (GramChecks x y w c gap τ) := by
  unfold GramChecks; infer_instance

def checkGram (x y w : Fin n → ℚ) (c gap τ : ℚ) : Bool := decide (GramChecks x y w c gap τ)

/-- **Gram separation.** The witness `w` is the Gram witness; the signed form
    on it equals `−c · gap²` and stays negative under every operator
    perturbation of norm below `τ = c · gap / ‖x‖²`. -/
theorem checked_gram (x y w : Fin n → ℚ) (c gap τ : ℚ) (h : checkGram x y w c gap τ = true) :
    gramWitness (ev x) (ev y) = ev w ∧ gramGap (ev x) (ev y) = gap ∧
    (c : ℝ) * (⟪ev x, ev w⟫_ℝ ^ 2 - ⟪ev y, ev w⟫_ℝ ^ 2) = -(c : ℝ) * (gap : ℝ) ^ 2 ∧
    ∀ T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n), ‖T‖ < τ →
      (c : ℝ) * (⟪ev x, ev w⟫_ℝ ^ 2 - ⟪ev y, ev w⟫_ℝ ^ 2) + ⟪ev w, T (ev w)⟫_ℝ < 0 := by
  obtain ⟨hc, hgap, hpos, hw, hτ⟩ := of_decide_eq_true h
  have hgapr : gramGap (ev x) (ev y) = gap := by
    unfold gramGap
    rw [norm_sq_ev, norm_sq_ev, inner_ev, hgap]
    push_cast; ring
  have hwr : gramWitness (ev x) (ev y) = ev w := by
    unfold gramWitness
    rw [norm_sq_ev, inner_ev]
    ext i
    simp [hw i]
  have hxpos : (0 : ℝ) < ‖ev x‖ ^ 2 := gramGap_pos_norm_left (by rw [hgapr]; exact_mod_cast hpos)
  have hτr : (τ : ℝ) = c * gramGap (ev x) (ev y) / ‖ev x‖ ^ 2 := by
    rw [hgapr, eq_div_iff hxpos.ne', norm_sq_ev]
    exact_mod_cast hτ
  refine ⟨hwr, hgapr, ?_, fun T hT => ?_⟩
  · rw [← hwr, signedGram_witness_value, hgapr]
  · rw [← hwr]
    exact gram_operator_perturbation_negative (by exact_mod_cast hc) (ev x) (ev y)
      (by rw [hgapr]; exact_mod_cast hpos) T (by rw [← hτr]; exact hT)

end PermanssonResearch.ApplicationBridge.RationalAlgebraReceipt
