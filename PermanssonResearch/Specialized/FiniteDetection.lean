import Mathlib.Analysis.Normed.Operator.Bilinear
import PermanssonLean.Regime.ConstitutiveMargin
import Mathlib.Tactic

/-! E-DETECT: quantitative legal approximation and persistent finite witnesses.
The legal carriers, approximation, and form-preserving embeddings are explicit
premises. Existence of a source negative witness is never inferred. -/

namespace PermanssonResearch.Specialized

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The exact quadratic error estimate for a bounded real bilinear form. -/
theorem quadratic_approximation_bound
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) {C ε : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ u v, |B u v| ≤ C * ‖u‖ * ‖v‖)
    (p h : E) (happrox : ‖p - h‖ ≤ ε) :
    |B p p - B h h| ≤ C * ε * (2 * ‖h‖ + ε) := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans happrox
  have hp : ‖p‖ ≤ ‖h‖ + ε := by
    have h := norm_le_norm_sub_add p h
    linarith
  have hexpand : B p p - B h h = B (p - h) h + B p (p - h) := by
    simp only [map_sub, LinearMap.sub_apply]
    ring
  rw [hexpand]
  calc |B (p - h) h + B p (p - h)|
      ≤ |B (p - h) h| + |B p (p - h)| := abs_add_le _ _
    _ ≤ C * ‖p - h‖ * ‖h‖ + C * ‖p‖ * ‖p - h‖ :=
      add_le_add (hbound _ _) (hbound _ _)
    _ ≤ C * ε * ‖h‖ + C * (‖h‖ + ε) * ε := by gcongr
    _ = C * ε * (2 * ‖h‖ + ε) := by ring

/-- A sufficiently accurate legal approximant retains strict negativity. -/
theorem negative_quadratic_of_approximation
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) {C ε γ : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ u v, |B u v| ≤ C * ‖u‖ * ‖v‖)
    (p h : E) (happrox : ‖p - h‖ ≤ ε) (hnegative : B h h = -γ)
    (hsmall : C * ε * (2 * ‖h‖ + ε) < γ) : B p p < 0 := by
  have herror := quadratic_approximation_bound B hC hbound p h happrox
  have hupper := (le_abs_self (B p p - B h h)).trans herror
  linarith

/-- Legal dense carriers detect an already-supplied strict witness. The exact
control topology is encoded by the norm in the approximation premise. -/
theorem exists_legal_negative_of_approximation
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ u v, |B u v| ≤ C * ‖u‖ * ‖v‖)
    (legal : ℕ → Set E) (h : E) (hnegative : B h h < 0)
    (hlegal : ∀ ε : ℝ, 0 < ε → ∃ N p, p ∈ legal N ∧ ‖p - h‖ ≤ ε) :
    ∃ N p, p ∈ legal N ∧ B p p < 0 := by
  let F : ℝ → ℝ := fun ε => C * ε * (2 * ‖h‖ + ε)
  have hcont : ContinuousAt F 0 := by unfold F; fun_prop
  have hF0 : F 0 < -B h h := by simp only [F, mul_zero, zero_mul]; linarith
  have hevent : ∀ᶠ ε in nhds (0 : ℝ), F ε < -B h h :=
    hcont.eventually (gt_mem_nhds hF0)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  let ε := δ / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨N, p, hp, happrox⟩ := hlegal ε hε
  refine ⟨N, p, hp, negative_quadratic_of_approximation B hC hbound p h happrox
    (γ := -B h h) (by ring) ?_⟩
  apply hball
  simp only [Real.dist_eq, sub_zero, abs_of_pos hε]
  dsimp [ε]
  linarith

/-- A certified form-preserving embedding preserves an obtained witness.
No claim of nesting or source legality is supplied by this lemma. -/
theorem negative_persists_under_embedding
    {V W : Type*} (Q : V → ℝ) (R : W → ℝ) (j : V → W)
    (hpreserve : ∀ v, R (j v) = Q v) (v : V) (hv : Q v < 0) : R (j v) < 0 := by
  rw [hpreserve]
  exact hv

/-- The exact two-control estimate keeps the source's control functions. It
does not identify them with an unrelated numerical norm. -/
theorem quadratic_two_control_bound
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (a b : E → ℝ) (C : ℝ)
    (hbound : ∀ u v, |B u v| ≤ C * a u * b v) (p h : E) :
    |B p p - B h h| ≤ C * (a (p - h) * b h + a p * b (p - h)) := by
  have heq : B p p - B h h = B (p - h) h + B p (p - h) := by
    simp only [map_sub, LinearMap.sub_apply]
    ring
  rw [heq]
  calc
    _ ≤ |B (p - h) h| + |B p (p - h)| := abs_add_le _ _
    _ ≤ C * a (p - h) * b h + C * a p * b (p - h) :=
      add_le_add (hbound _ _) (hbound _ _)
    _ = _ := by ring

def bilinearFeatureProperty {Y : Type*} [MeasurableSpace Y]
    (feature : PermanssonLean.RegimePropertyMap Y (E →ₗ[ℝ] E →ₗ[ℝ] ℝ))
    (p : E) : PermanssonLean.RegimePropertyMap Y ℝ := fun Λ => feature Λ p p

/-- A legal finite approximant detects the discrepancy of the actual original
baseline and intervened feature laws. Source legality and bounds are explicit. -/
theorem actual_effect_pos_of_legal_approximation
    {S X A Component : Type*}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    (M : PermanssonLean.StrategicWorldModel S X A)
    {F : PermanssonLean.InterventionFamily M Component}
    (J : PermanssonLean.AdmissibleStrategicIntervention F)
    (feature : PermanssonLean.RegimePropertyMap (PermanssonLean.JointState S X)
      (E →ₗ[ℝ] E →ₗ[ℝ] ℝ)) (y : PermanssonLean.JointState S X)
    (legal : Set E) (p h : E) (hp : p ∈ legal)
    {C ε γ : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ u v,
      |(feature (PermanssonLean.RegimeSpecification.pathProbability M (MeasureTheory.diracProba y)) -
        feature (PermanssonLean.RegimeSpecification.pathProbability J.intervention.apply
          (MeasureTheory.diracProba y))) u v| ≤ C * ‖u‖ * ‖v‖)
    (happrox : ‖p - h‖ ≤ ε)
    (hnegative : (feature (PermanssonLean.RegimeSpecification.pathProbability M
        (MeasureTheory.diracProba y)) - feature
        (PermanssonLean.RegimeSpecification.pathProbability J.intervention.apply
          (MeasureTheory.diracProba y))) h h = -γ)
    (hsmall : C * ε * (2 * ‖h‖ + ε) < γ) :
    0 < PermanssonLean.RegimeSpecification.constitutiveEffect M
      (bilinearFeatureProperty feature p) J y := by
  have hneg := negative_quadratic_of_approximation _ hC hbound p h happrox hnegative hsmall
  unfold PermanssonLean.RegimeSpecification.constitutiveEffect
    PermanssonLean.RegimeSpecification.baselinePropertyValue
    PermanssonLean.RegimeSpecification.intervenedPropertyValue bilinearFeatureProperty
  rw [Real.dist_eq]
  exact abs_pos.mpr (by simpa only [LinearMap.sub_apply] using ne_of_lt hneg)

end PermanssonResearch.Specialized
