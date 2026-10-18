import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import PermanssonLean.Regime.ConstitutiveMargin
import Mathlib.Tactic

/-! E-GRAM: an explicit Gram-gap witness and its exact perturbation threshold.
The signed rank-one representation and any actual path-feature identification
remain explicit application premises. Additional PSD summands are not ignored.
-/

namespace PermanssonResearch.Specialized

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def gramGap (x y : E) : ℝ := ‖x‖ ^ 2 * ‖y‖ ^ 2 - ⟪x, y⟫_ℝ ^ 2

def gramWitness (x y : E) : E := ‖x‖ ^ 2 • y - ⟪x, y⟫_ℝ • x

theorem inner_gramWitness_left (x y : E) : ⟪x, gramWitness x y⟫_ℝ = 0 := by
  simp [gramWitness, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  ring

theorem inner_gramWitness_right (x y : E) :
    ⟪y, gramWitness x y⟫_ℝ = gramGap x y := by
  simp [gramWitness, gramGap, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm]
  ring

theorem norm_gramWitness_sq (x y : E) :
    ‖gramWitness x y‖ ^ 2 = ‖x‖ ^ 2 * gramGap x y := by
  rw [← real_inner_self_eq_norm_sq (gramWitness x y)]
  unfold gramWitness gramGap
  simp only [inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_self_eq_norm_sq x, real_inner_self_eq_norm_sq y]
  rw [real_inner_comm y x]
  ring

theorem gramGap_pos_norm_left {x y : E} (hgap : 0 < gramGap x y) : 0 < ‖x‖ ^ 2 := by
  by_contra hn
  have hz : ‖x‖ ^ 2 = 0 := le_antisymm (not_lt.mp hn) (sq_nonneg _)
  have hx : x = 0 := norm_eq_zero.mp ((sq_eq_zero_iff).mp hz)
  simp [hx, gramGap] at hgap

theorem signedGram_witness_value (c : ℝ) (x y : E) :
    c * (⟪x, gramWitness x y⟫_ℝ ^ 2 - ⟪y, gramWitness x y⟫_ℝ ^ 2) =
      -c * gramGap x y ^ 2 := by
  rw [inner_gramWitness_left, inner_gramWitness_right]
  ring

theorem signedGram_witness_negative {c : ℝ} (hc : 0 < c) (x y : E)
    (hgap : 0 < gramGap x y) :
    c * (⟪x, gramWitness x y⟫_ℝ ^ 2 - ⟪y, gramWitness x y⟫_ℝ ^ 2) < 0 := by
  rw [signedGram_witness_value]
  have hsq : 0 < gramGap x y ^ 2 := sq_pos_of_pos hgap
  nlinarith

theorem gramWitness_ne_zero {x y : E} (hgap : 0 < gramGap x y) : gramWitness x y ≠ 0 := by
  intro hz
  have h := norm_gramWitness_sq x y
  rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
  have hp := mul_pos (gramGap_pos_norm_left hgap) hgap
  linarith

noncomputable def unitGramWitness (x y : E) : E := ‖gramWitness x y‖⁻¹ • gramWitness x y

theorem norm_unitGramWitness {x y : E} (hgap : 0 < gramGap x y) :
    ‖unitGramWitness x y‖ = 1 := by
  have hp : 0 < ‖gramWitness x y‖ := norm_pos_iff.mpr (gramWitness_ne_zero hgap)
  simp [unitGramWitness, norm_smul, Real.norm_eq_abs, abs_of_pos hp, hp.ne']

theorem gram_unit_rayleigh_value (c : ℝ) (x y : E) (hgap : 0 < gramGap x y) :
    c * (⟪x, unitGramWitness x y⟫_ℝ ^ 2 - ⟪y, unitGramWitness x y⟫_ℝ ^ 2) =
      -c * gramGap x y / ‖x‖ ^ 2 := by
  have hx := gramGap_pos_norm_left hgap
  calc
    _ = -c * gramGap x y ^ 2 / ‖gramWitness x y‖ ^ 2 := by
      simp only [unitGramWitness, real_inner_smul_right,
        inner_gramWitness_left, inner_gramWitness_right, mul_zero,
        zero_pow (by decide : 2 ≠ 0), zero_sub, mul_pow, div_eq_mul_inv, inv_pow]
      ring
    _ = -c * gramGap x y / ‖x‖ ^ 2 := by
      rw [norm_gramWitness_sq]
      field_simp [hx.ne', hgap.ne']
      <;> ring

/-- Evaluation at the witness is nonnegative on the PSD cone and strictly
negative on the signed Gram operator, so it is a separating functional. -/
theorem gram_psd_evaluation_nonnegative (P : E →L[ℝ] E)
    (hP : ∀ v, 0 ≤ ⟪v, P v⟫_ℝ) (x y : E) :
    0 ≤ ⟪gramWitness x y, P (gramWitness x y)⟫_ℝ := hP _

/-- The unnormalized direction remains strictly negative under the exact
operator-norm threshold. Normalization is unnecessary for the sign test. -/
theorem gram_operator_perturbation_negative {c : ℝ} (hc : 0 < c)
    (x y : E) (hgap : 0 < gramGap x y) (L : E →L[ℝ] E)
    (hL : ‖L‖ < c * gramGap x y / ‖x‖ ^ 2) :
    c * (⟪x, gramWitness x y⟫_ℝ ^ 2 - ⟪y, gramWitness x y⟫_ℝ ^ 2) +
      ⟪gramWitness x y, L (gramWitness x y)⟫_ℝ < 0 := by
  have hx := gramGap_pos_norm_left hgap
  have hL' := (lt_div_iff₀ hx).mp hL
  have hbound : ⟪gramWitness x y, L (gramWitness x y)⟫_ℝ ≤
      ‖L‖ * ‖gramWitness x y‖ ^ 2 := by
    calc ⟪gramWitness x y, L (gramWitness x y)⟫_ℝ
        ≤ |⟪gramWitness x y, L (gramWitness x y)⟫_ℝ| := le_abs_self _
      _ ≤ ‖gramWitness x y‖ * ‖L (gramWitness x y)‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖gramWitness x y‖ * (‖L‖ * ‖gramWitness x y‖) := by
        gcongr
        exact L.le_opNorm _
      _ = ‖L‖ * ‖gramWitness x y‖ ^ 2 := by ring
  rw [norm_gramWitness_sq] at hbound
  rw [signedGram_witness_value]
  have hstrict := mul_lt_mul_of_pos_right hL' hgap
  nlinarith

/-- An additional component needs a quantitative witness-direction budget. -/
theorem gram_additional_component_negative {c P : ℝ} (x y : E)
    (hP : P < c * gramGap x y ^ 2) :
    c * (⟪x, gramWitness x y⟫_ℝ ^ 2 - ⟪y, gramWitness x y⟫_ℝ ^ 2) + P < 0 := by
  rw [signedGram_witness_value]
  linarith

def operatorFeatureProperty {Y : Type*} [MeasurableSpace Y]
    (feature : PermanssonLean.RegimePropertyMap Y (E →L[ℝ] E))
    (w : E) : PermanssonLean.RegimePropertyMap Y ℝ := fun Λ => ⟪w, feature Λ w⟫_ℝ

/-- The Gram witness tests the actual original canonical-law feature pair.
The signed representation is a model-specific hypothesis, not a PDF import. -/
theorem constitutiveEffect_gram_witness
    {S X A Component : Type*}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    (M : PermanssonLean.StrategicWorldModel S X A)
    {F : PermanssonLean.InterventionFamily M Component}
    (J : PermanssonLean.AdmissibleStrategicIntervention F)
    (feature : PermanssonLean.RegimePropertyMap (PermanssonLean.JointState S X)
      (E →L[ℝ] E)) (y₀ : PermanssonLean.JointState S X)
    {c : ℝ} (hc : 0 < c) (x y : E) (hgap : 0 < gramGap x y)
    (hrepresentation : ∀ v : E,
      ⟪v, (feature (PermanssonLean.RegimeSpecification.pathProbability M
        (MeasureTheory.diracProba y₀)) - feature
        (PermanssonLean.RegimeSpecification.pathProbability J.intervention.apply
          (MeasureTheory.diracProba y₀))) v⟫_ℝ =
        c * (⟪x, v⟫_ℝ ^ 2 - ⟪y, v⟫_ℝ ^ 2)) :
    PermanssonLean.RegimeSpecification.constitutiveEffect M
      (operatorFeatureProperty feature (gramWitness x y)) J y₀ = c * gramGap x y ^ 2 := by
  unfold PermanssonLean.RegimeSpecification.constitutiveEffect
    PermanssonLean.RegimeSpecification.baselinePropertyValue
    PermanssonLean.RegimeSpecification.intervenedPropertyValue operatorFeatureProperty
  rw [Real.dist_eq, ← inner_sub_right, ← ContinuousLinearMap.sub_apply,
    hrepresentation, signedGram_witness_value]
  have hn : -c * gramGap x y ^ 2 < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (sq_pos_of_pos hgap)
  rw [abs_of_neg hn]
  ring

end PermanssonResearch.Specialized
