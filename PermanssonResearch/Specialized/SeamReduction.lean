import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import PermanssonLean.Regime.ConstitutiveMargin

/-!
# E-SCALAR: seam invisibility and the actual feature-property effect

The first profile is finite and real symmetric. Seam invisibility yields rank
at most two. Constant diagonal is an additional premise for common rank one.
The conditional application uses a feature map on actual canonical path laws;
no particular economic or specialized source model is silently identified.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch.Specialized

variable {ι : Type*} [Fintype ι]

def seam (H : Matrix ι ι ℝ) (p i j : ι) : ℝ :=
  H i j - H i p - H p j + H p p

def quadratic (H : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * H i j * v j

omit [Fintype ι] in
/-- Expanded seam equations determine every entry from a single column. -/
theorem seam_decomposition (H : Matrix ι ι ℝ) (p : ι)
    (hsym : ∀ i j, H i j = H j i)
    (hseam : ∀ i j, seam H p i j = 0) :
    ∀ i j, H i j = (H i p - H p p / 2) + (H j p - H p p / 2) := by
  intro i j
  have h := hseam i j
  dsimp [seam] at h
  rw [hsym p j] at h
  linarith

/-- A two-column factorization proves the correct rank bound. -/
theorem seam_rank_le_two (H : Matrix ι ι ℝ) (p : ι)
    (hsym : ∀ i j, H i j = H j i)
    (hseam : ∀ i j, seam H p i j = 0) : H.rank ≤ 2 := by
  classical
  let a := fun i => H i p - H p p / 2
  let L : Matrix ι (Fin 2) ℝ := fun i k => if k = 0 then 1 else a i
  let R : Matrix (Fin 2) ι ℝ := fun k j => if k = 0 then a j else 1
  have hfactor : H = L * R := by
    ext i j
    change H i j = ∑ k : Fin 2, L i k * R k j
    rw [seam_decomposition H p hsym hseam i j]
    simp [Fin.sum_univ_two, L, R, a, add_comm]
  rw [hfactor]
  exact (Matrix.rank_mul_le_left L R).trans (by simpa using L.rank_le_card_width)

omit [Fintype ι] in
/-- Constant diagonal upgrades the conclusion to a common-mode matrix. -/
theorem seam_constant_diagonal (H : Matrix ι ι ℝ) (p : ι) (δ : ℝ)
    (hsym : ∀ i j, H i j = H j i)
    (hseam : ∀ i j, seam H p i j = 0)
    (hdiag : ∀ i, H i i = δ) : ∀ i j, H i j = δ := by
  intro i j
  have hi := seam_decomposition H p hsym hseam i i
  have hj := seam_decomposition H p hsym hseam j j
  have hij := seam_decomposition H p hsym hseam i j
  rw [hdiag i] at hi
  rw [hdiag j] at hj
  linarith

theorem commonMode_rank_le_one (H : Matrix ι ι ℝ) (δ : ℝ)
    (h : ∀ i j, H i j = δ) : H.rank ≤ 1 := by
  have heq : H = Matrix.vecMulVec (fun _ => δ) (fun _ => (1 : ℝ)) := by
    ext i j
    simp [Matrix.vecMulVec, h]
  rw [heq]
  exact Matrix.rank_vecMulVec_le _ _

omit [Fintype ι] in
theorem nested_commonMode_scalar_consistent {κ : Type*}
    (G : Matrix ι ι ℝ) (H : Matrix κ κ ℝ) (j : ι → κ) (p : ι)
    (δ ε : ℝ) (hG : ∀ i k, G i k = δ) (hH : ∀ i k, H i k = ε)
    (hpreserve : ∀ i k, H (j i) (j k) = G i k) : δ = ε := by
  rw [← hG p p, ← hpreserve p p, hH]

theorem quadratic_commonMode (H : Matrix ι ι ℝ) (δ : ℝ)
    (h : ∀ i j, H i j = δ) (v : ι → ℝ) :
    quadratic H v = δ * (∑ i, v i) ^ 2 := by
  simp_rw [quadratic, h]
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem quadratic_sub (G H : Matrix ι ι ℝ) (v : ι → ℝ) :
    quadratic (G - H) v = quadratic G v - quadratic H v := by
  simp [quadratic, mul_sub, sub_mul, Finset.sum_sub_distrib]

/-- One frozen actual-law feature property for the conditional adapter. -/
def featureQuadratic {Y : Type*} [MeasurableSpace Y]
    (feature : PermanssonLean.RegimePropertyMap Y (Matrix ι ι ℝ))
    (v : ι → ℝ) : PermanssonLean.RegimePropertyMap Y ℝ :=
  fun Λ => quadratic (feature Λ) v

/-- The effect conclusion concerns the original typed intervention and its
actual path laws. The feature identification is an explicit unmet premise. -/
theorem constitutiveEffect_commonMode
    {S X A Component : Type*}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    (M : PermanssonLean.StrategicWorldModel S X A)
    {F : PermanssonLean.InterventionFamily M Component}
    (J : PermanssonLean.AdmissibleStrategicIntervention F)
    (feature : PermanssonLean.RegimePropertyMap (PermanssonLean.JointState S X)
      (Matrix ι ι ℝ))
    (v : ι → ℝ) (y : PermanssonLean.JointState S X) (δ : ℝ)
    (hfeature : ∀ i j,
      (feature (PermanssonLean.RegimeSpecification.pathProbability M (diracProba y)) -
       feature (PermanssonLean.RegimeSpecification.pathProbability J.intervention.apply
         (diracProba y))) i j = δ) :
    PermanssonLean.RegimeSpecification.constitutiveEffect M (featureQuadratic feature v) J y =
      |δ| * (∑ i, v i) ^ 2 := by
  unfold PermanssonLean.RegimeSpecification.constitutiveEffect
    PermanssonLean.RegimeSpecification.baselinePropertyValue
    PermanssonLean.RegimeSpecification.intervenedPropertyValue featureQuadratic
  rw [Real.dist_eq, ← quadratic_sub, quadratic_commonMode _ δ hfeature v,
    abs_mul, abs_of_nonneg (sq_nonneg (∑ i, v i))]

/-- The original margin scales the infimum over the entire original comparison
set, including the zero-sum-vector case. No minimizing start is postulated. -/
theorem constitutiveMargin_commonMode
    {S X A Component H : Type*}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace H]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H)
    (F : PermanssonLean.InterventionFamily M Component)
    (B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec)
    (J : PermanssonLean.AdmissibleStrategicIntervention F)
    (feature : PermanssonLean.RegimePropertyMap (PermanssonLean.JointState S X)
      (Matrix ι ι ℝ)) (v : ι → ℝ) (δ : PermanssonLean.JointState S X → ℝ)
    (hfeature : ∀ y ∈ B₁.states, ∀ i j,
      (feature (PermanssonLean.RegimeSpecification.pathProbability M (diracProba y)) -
       feature (PermanssonLean.RegimeSpecification.pathProbability J.intervention.apply
         (diracProba y))) i j = δ y) :
    PermanssonLean.RegimeSpecification.constitutiveMargin M spec F
      (featureQuadratic feature v) B₁ J =
      (∑ i, v i) ^ 2 * sInf ((fun y => |δ y|) '' B₁.states) := by
  obtain ⟨y₀, hy₀, -⟩ := B₁.pathLawNontrivial
  have hne : ((fun y => |δ y|) '' B₁.states).Nonempty :=
    ⟨|δ y₀|, y₀, hy₀, rfl⟩
  have hb : BddBelow ((fun y => |δ y|) '' B₁.states) :=
    ⟨0, by rintro _ ⟨y, _, rfl⟩; exact abs_nonneg _⟩
  have hglb := (isGLB_csInf hne hb).mul_left (sq_nonneg (∑ i, v i))
  have himage :
      (PermanssonLean.RegimeSpecification.constitutiveEffect M
        (featureQuadratic feature v) J) '' B₁.states =
      (fun r : ℝ => (∑ i, v i) ^ 2 * r) '' ((fun y => |δ y|) '' B₁.states) := by
    rw [Set.image_image]
    apply Set.image_congr
    intro y hy
    rw [constitutiveEffect_commonMode M J feature v y (δ y) (hfeature y hy)]
    simp [Function.comp_def, mul_comm]
  unfold PermanssonLean.RegimeSpecification.constitutiveMargin
  rw [himage]
  exact hglb.csInf_eq (hne.image _)

end PermanssonResearch.Specialized
