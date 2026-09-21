import PermanssonLean.Regime.ConstitutiveMargin
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

open MeasureTheory ProbabilityTheory Set

namespace PermanssonLean

universe uS uX uA uH uZ uK uY

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {H : Type uH} {Z : Type uZ}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]
variable [MetricSpace Z]

namespace RegimeSpecification

/-- A frozen approximate property-output profile.  Proposition 5.2 only
requires error control on the baseline and intervention outputs; it does not
require the approximation to arise from another GR model. -/
structure PerturbedPropertyProfile
    (Y : Type uY) (Z : Type uZ) where
  baseline : Y → Z
  intervention : Y → Z

/-- Pointwise approximate constitutive effect. -/
noncomputable def perturbedConstitutiveEffect
    {Y : Type uY}
    (profile : PerturbedPropertyProfile Y Z)
    (y : Y) : ℝ :=
  dist (profile.baseline y) (profile.intervention y)

/-- Approximate constitutive margin over the same frozen B₁. -/
noncomputable def perturbedConstitutiveMargin
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (B₁ : ConstitutiveComparisonSet M spec)
    (profile : PerturbedPropertyProfile (JointState S X) Z) : ℝ :=
  sInf (perturbedConstitutiveEffect profile '' B₁.states)

theorem perturbedConstitutiveEffect_nonneg
    {Y : Type uY}
    (profile : PerturbedPropertyProfile Y Z)
    (y : Y) :
    0 ≤ perturbedConstitutiveEffect profile y := by
  unfold perturbedConstitutiveEffect
  exact dist_nonneg

theorem perturbedConstitutiveMargin_nonneg
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (B₁ : ConstitutiveComparisonSet M spec)
    (profile : PerturbedPropertyProfile (JointState S X) Z) :
    0 ≤ perturbedConstitutiveMargin M spec B₁ profile := by
  unfold perturbedConstitutiveMargin
  refine le_csInf ?_ ?_
  · rcases B₁.states_nonempty with ⟨y, hy⟩
    exact ⟨perturbedConstitutiveEffect profile y, ⟨y, hy, rfl⟩⟩
  · intro r hr
    rcases hr with ⟨y, hy, rfl⟩
    exact perturbedConstitutiveEffect_nonneg profile y

/-- Generic stability lemma for infima of two nonnegative real-valued
functions over the same nonempty set. -/
theorem abs_sInf_image_sub_sInf_image_le_of_uniform
    {Y : Type uY}
    (s : Set Y)
    (hs : s.Nonempty)
    (f g : Y → ℝ)
    (hf : ∀ y ∈ s, 0 ≤ f y)
    (hg : ∀ y ∈ s, 0 ≤ g y)
    {ε : ℝ}
    (hfg : ∀ y ∈ s, |f y - g y| ≤ ε) :
    |sInf (f '' s) - sInf (g '' s)| ≤ ε := by
  have hf_bdd : BddBelow (f '' s) := by
    refine ⟨0, ?_⟩
    rintro r ⟨y, hy, rfl⟩
    exact hf y hy
  have hg_bdd : BddBelow (g '' s) := by
    refine ⟨0, ?_⟩
    rintro r ⟨y, hy, rfl⟩
    exact hg y hy
  have hf_nonempty : (f '' s).Nonempty := hs.image f
  have hg_nonempty : (g '' s).Nonempty := hs.image g
  have hfg_le : ∀ y ∈ s, f y ≤ g y + ε := by
    intro y hy
    have hsub : f y - g y ≤ ε :=
      le_trans (le_abs_self (f y - g y)) (hfg y hy)
    have hle := (sub_le_iff_le_add).1 hsub
    simpa [add_comm] using hle
  have hgf_le : ∀ y ∈ s, g y ≤ f y + ε := by
    intro y hy
    have hsub : g y - f y ≤ ε := by
      calc
        g y - f y ≤ |g y - f y| := le_abs_self _
        _ = |f y - g y| := abs_sub_comm _ _
        _ ≤ ε := hfg y hy
    have hle := (sub_le_iff_le_add).1 hsub
    simpa [add_comm] using hle
  have hInfF : sInf (f '' s) ≤ sInf (g '' s) + ε := by
    have hsub : sInf (f '' s) - ε ≤ sInf (g '' s) := by
      refine le_csInf hg_nonempty ?_
      intro r hr
      rcases hr with ⟨y, hy, rfl⟩
      have hfy : sInf (f '' s) ≤ f y :=
        csInf_le hf_bdd ⟨y, hy, rfl⟩
      exact (sub_le_iff_le_add).2 (hfy.trans (hfg_le y hy))
    exact (sub_le_iff_le_add).1 hsub
  have hInfG : sInf (g '' s) ≤ sInf (f '' s) + ε := by
    have hsub : sInf (g '' s) - ε ≤ sInf (f '' s) := by
      refine le_csInf hf_nonempty ?_
      intro r hr
      rcases hr with ⟨y, hy, rfl⟩
      have hgy : sInf (g '' s) ≤ g y :=
        csInf_le hg_bdd ⟨y, hy, rfl⟩
      exact (sub_le_iff_le_add).2 (hgy.trans (hgf_le y hy))
    exact (sub_le_iff_le_add).1 hsub
  refine abs_sub_le_iff.2 ⟨?_, ?_⟩
  · exact (sub_le_iff_le_add).2 (by simpa [add_comm] using hInfF)
  · exact (sub_le_iff_le_add).2 (by simpa [add_comm] using hInfG)

/-- Frozen two-sided output error envelope from Proposition 5.2. -/
structure HasConstitutiveOutputErrors
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (profile : PerturbedPropertyProfile (JointState S X) Z)
    (ε₀ εJ : ℝ) : Prop where
  baseline_nonneg : 0 ≤ ε₀
  intervention_nonneg : 0 ≤ εJ
  baseline_le :
    ∀ y ∈ B₁.states,
      dist (baselinePropertyValue ψ M y) (profile.baseline y) ≤ ε₀
  intervention_le :
    ∀ y ∈ B₁.states,
      dist
        (intervenedPropertyValue ψ J.intervention y)
        (profile.intervention y) ≤ εJ

theorem HasConstitutiveOutputErrors.total_nonneg
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (profile : PerturbedPropertyProfile (JointState S X) Z)
    (ε₀ εJ : ℝ)
    (h : HasConstitutiveOutputErrors M spec F ψ B₁ J profile ε₀ εJ) :
    0 ≤ ε₀ + εJ :=
  add_nonneg h.baseline_nonneg h.intervention_nonneg

/-- Proposition 5.2, pointwise form:
\[
|\Delta_{\psi,J}(y)-\widetilde\Delta_{\psi,J}(y)|
\le \varepsilon_0+\varepsilon_J.
\]
-/
theorem constitutiveEffect_perturbation_abs_le
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (profile : PerturbedPropertyProfile (JointState S X) Z)
    (ε₀ εJ : ℝ)
    (h : HasConstitutiveOutputErrors M spec F ψ B₁ J profile ε₀ εJ)
    {y : JointState S X}
    (hy : y ∈ B₁.states) :
    |constitutiveEffect M ψ J y - perturbedConstitutiveEffect profile y| ≤
      ε₀ + εJ := by
  have hdist :
      dist
          (dist
            (baselinePropertyValue ψ M y)
            (intervenedPropertyValue ψ J.intervention y))
          (dist (profile.baseline y) (profile.intervention y))
        ≤
      dist (baselinePropertyValue ψ M y) (profile.baseline y) +
        dist
          (intervenedPropertyValue ψ J.intervention y)
          (profile.intervention y) :=
    dist_dist_dist_le _ _ _ _
  have hle := hdist.trans (add_le_add (h.baseline_le y hy) (h.intervention_le y hy))
  simpa [constitutiveEffect, perturbedConstitutiveEffect, Real.dist_eq] using hle

/-- Proposition 5.2, uniform-margin form:
\[
|\widetilde\kappa-\kappa|\le\varepsilon_0+\varepsilon_J.
\]
-/
theorem constitutiveMargin_perturbation_abs_le
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (profile : PerturbedPropertyProfile (JointState S X) Z)
    (ε₀ εJ : ℝ)
    (h : HasConstitutiveOutputErrors M spec F ψ B₁ J profile ε₀ εJ) :
    |perturbedConstitutiveMargin M spec B₁ profile -
        constitutiveMargin M spec F ψ B₁ J| ≤
      ε₀ + εJ := by
  simpa [constitutiveMargin, perturbedConstitutiveMargin, abs_sub_comm] using
    (abs_sInf_image_sub_sInf_image_le_of_uniform
      B₁.states B₁.states_nonempty
      (constitutiveEffect M ψ J)
      (perturbedConstitutiveEffect profile)
      (fun y _ => constitutiveEffect_nonneg M ψ J y)
      (fun y _ => perturbedConstitutiveEffect_nonneg profile y)
      (fun y hy => constitutiveEffect_perturbation_abs_le
        M spec F ψ B₁ J profile ε₀ εJ h hy))

/-- Lower-bound form of Proposition 5.2. -/
theorem perturbedConstitutiveMargin_ge
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (profile : PerturbedPropertyProfile (JointState S X) Z)
    (ε₀ εJ : ℝ)
    (h : HasConstitutiveOutputErrors M spec F ψ B₁ J profile ε₀ εJ) :
    constitutiveMargin M spec F ψ B₁ J - (ε₀ + εJ) ≤
      perturbedConstitutiveMargin M spec B₁ profile := by
  have habs := constitutiveMargin_perturbation_abs_le
    M spec F ψ B₁ J profile ε₀ εJ h
  have hright :
      constitutiveMargin M spec F ψ B₁ J -
          perturbedConstitutiveMargin M spec B₁ profile ≤
        ε₀ + εJ :=
    (abs_sub_le_iff.mp habs).2
  have hle :
      constitutiveMargin M spec F ψ B₁ J ≤
        (ε₀ + εJ) + perturbedConstitutiveMargin M spec B₁ profile :=
    (sub_le_iff_le_add).1 hright
  exact (sub_le_iff_le_add).2 (by simpa [add_comm] using hle)

/-- Corollary 5.3: if the true constitutive margin dominates the total
output-error envelope, the approximate constitutive margin remains positive. -/
theorem robustUniformConstitution
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (profile : PerturbedPropertyProfile (JointState S X) Z)
    (ε₀ εJ : ℝ)
    (h : HasConstitutiveOutputErrors M spec F ψ B₁ J profile ε₀ εJ)
    (hgap :
      ε₀ + εJ < constitutiveMargin M spec F ψ B₁ J) :
    0 < perturbedConstitutiveMargin M spec B₁ profile := by
  have hpos :
      0 < constitutiveMargin M spec F ψ B₁ J - (ε₀ + εJ) :=
    sub_pos.mpr hgap
  exact lt_of_lt_of_le hpos
    (perturbedConstitutiveMargin_ge M spec F ψ B₁ J profile ε₀ εJ h)

end RegimeSpecification

end PermanssonLean
