import PermanssonResearch.ApplicationBridge.ExitReceipt
import PermanssonResearch.ConstitutiveQuasi.Certificate
import PermanssonResearch.ConstitutiveQuasi.PropertyErrors
import Mathlib.Tactic

/-!
# ApplicationBridge — CQ-1 finite constitutive certificates from survival tables

A receipt for a finite rational baseline `K₀` and a strategic intervention
`K₁` reports, at horizon `L`, killed survival in the declared region `R` for
every start in `R`, and the prefix-survival property "stay in `Q` at times
`0..L`" under both models on the declared comparison set `B₁`.

`CQ1Checks` decides the persistence gate `1 - η ≤ survival` on all of `R`
(not only on `B₁`), a positive margin `κ` below every comparison effect and
attained by one of them, and the inclusions `B₁ ⊆ basin ⊆ R`.
`checked_finite_constitutive_certificate` constructs Research's
`FiniteConstitutiveCertificate` for the realized typed model of `K₀`
(`FiniteStrategicRealization.realizedModel`), the typed admissible strategic
intervention to `K₁` (`rationalStrategicIntervention`) and a comparison set
whose states are exactly `B₁`; `checked_margin_eq` identifies `κ` with the
original constitutive margin. In the realized model every row change is an
action-selection change, so that P is held fixed at the source must be proved
separately on the reflected α/P/U inputs. The descriptor, target law and
convergence mode of `spec` are not used by the finite certificate. Exact GR,
Exact PR, QSD and error-budget transport are not claimed.
-/

namespace PermanssonResearch.ApplicationBridge.FiniteScoreReceipt

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open PermanssonLean PermanssonLean.RegimeSpecification
open PermanssonResearch.ReverseSolver
open PermanssonResearch.ReverseSolver.FiniteStrategicRealization
open PermanssonResearch.ConstitutiveQuasi
open PermanssonResearch.ApplicationBridge.MenuReceipt
open PermanssonResearch.ApplicationBridge.ExitReceipt

set_option autoImplicit false

variable {n : ℕ}

attribute [local instance] StrategicWorldModel.inducedKernel_isMarkov

/-- Joint states of the realized model whose world component lies in `B`. -/
def liftSet (B : Finset (Fin n)) : Set (JointState Unit (Fin n)) := {y | encode y ∈ B}

/-- Region `R` and basin `basin ∩ R`; the checks require `basin ⊆ R`. -/
noncomputable def spec (R basin : Finset (Fin n)) :
    RegimeSpecification (JointState Unit (Fin n)) Bool where
  region := liftSet R
  region_measurable := MeasurableSet.of_discrete
  basin := liftSet basin ∩ liftSet R
  basin_measurable := MeasurableSet.of_discrete
  basin_subset_region := fun _ hy => hy.2
  descriptor := fun y => decide (encode y ∈ R)
  descriptor_measurable := Measurable.of_discrete
  target := ⟨Measure.dirac true, inferInstance⟩
  convergenceMode := ConvergenceMode.almostSureWeak _ Bool

/-- Killed survival in `R`, from the rational exit recursion. -/
def survival (K : RationalMarkovMatrix n) (R : Finset (Fin n)) (L : ℕ) (x : Fin n) : ℚ :=
  1 - rationalHittingValue K (exitTarget R) L x

/-- Stay in `Q` at observation times `0..L`, on the prefix space. -/
def prefixSet (Q : Finset (Fin n)) (L : ℕ) : Set ((i : Finset.Iic L) → JointState Unit (Fin n)) :=
  {w | ∀ i, encode (w i) ∈ Q}

theorem measurableSet_prefixSet (Q : Finset (Fin n)) (L : ℕ) : MeasurableSet (prefixSet Q L) := by
  have : prefixSet Q L = ⋂ i, (fun w : (i : Finset.Iic L) → JointState Unit (Fin n) => w i) ⁻¹'
      liftSet Q := by
    ext w
    simp [prefixSet, liftSet]
  rw [this]
  exact MeasurableSet.iInter (fun i => (measurable_pi_apply i) MeasurableSet.of_discrete)

/-- The prefix-survival indicator as a bounded measurable finite-path property. -/
noncomputable def prefixScore (Q : Finset (Fin n)) (L : ℕ) :
    FinitePathProperty (JointState Unit (Fin n)) L where
  score := (prefixSet Q L).indicator (fun _ => (1 : ℝ))
  measurable_score := measurable_const.indicator (measurableSet_prefixSet Q L)
  score_nonneg := by
    intro w
    by_cases hw : w ∈ prefixSet Q L <;> simp [Set.indicator, hw]
  score_le_one := by
    intro w
    by_cases hw : w ∈ prefixSet Q L <;> simp [Set.indicator, hw]

theorem frestrict_prefixSet (Q : Finset (Fin n)) (L : ℕ) :
    Preorder.frestrictLe L ⁻¹' prefixSet Q L = staysThrough Q L := by
  ext w
  simp only [prefixSet, staysThrough, Set.mem_preimage, Set.mem_ofPred_eq, Preorder.frestrictLe_apply]
  constructor
  · intro h u hu
    exact h ⟨u, Finset.mem_Iic.mpr hu⟩
  · intro h i
    exact h i.1 (Finset.mem_Iic.mp i.2)

/-- The property's expectation under the realized model is the rational
    killed survival in `Q`. -/
theorem prefixScore_fromKernel (K : RationalMarkovMatrix n) (Q : Finset (Fin n)) (L : ℕ)
    (x : Fin n) :
    (prefixScore Q L).fromKernel L (realizedModel K).inducedKernel (decode x) =
      (survival K Q L x : ℝ) := by
  rw [finitePathExpectation_eq_pathLaw]
  have hint : ∫ w, (prefixSet Q L).indicator (fun _ => (1 : ℝ)) w
      ∂((realizedModel K).pathLaw (Measure.dirac (decode x))).map (Preorder.frestrictLe L) =
      (((realizedModel K).pathLaw (Measure.dirac (decode x))).map
        (Preorder.frestrictLe L)).real (prefixSet Q L) :=
    integral_indicator_one (measurableSet_prefixSet Q L)
  change ∫ w, (prefixSet Q L).indicator (fun _ => (1 : ℝ)) w ∂_ = _
  rw [hint, map_measureReal_apply (Preorder.measurable_frestrictLe L) (measurableSet_prefixSet Q L),
    frestrict_prefixSet, survival_actual]
  simp [survival]

theorem baseline_value (K : RationalMarkovMatrix n) (Q : Finset (Fin n)) (L : ℕ) (x : Fin n) :
    baselinePropertyValue ((prefixScore Q L).toRegimeProperty L) (realizedModel K) (decode x) =
      (survival K Q L x : ℝ) := by
  rw [← finitePathExpectation_eq_baselineProperty, prefixScore_fromKernel]

theorem intervened_value (K₀ K₁ : RationalMarkovMatrix n) (Q : Finset (Fin n)) (L : ℕ)
    (x : Fin n) :
    intervenedPropertyValue ((prefixScore Q L).toRegimeProperty L)
      (rationalStrategicIntervention K₀ K₁).intervention (decode x) =
      (survival K₁ Q L x : ℝ) := by
  rw [← finitePathExpectation_eq_intervenedProperty, rationalStrategicIntervention_applied,
    prefixScore_fromKernel]

/-- Core survival probability of the realized model in the region of `spec`. -/
theorem survivalProbability_eq (K : RationalMarkovMatrix n) (R basin : Finset (Fin n))
    (x : Fin n) (L : ℕ) :
    survivalProbability (realizedModel K) (spec R basin) (decode x) L =
      ENNReal.ofReal (survival K R L x : ℝ) := by
  have hset : survivesThroughSet (spec R basin) L = staysThrough R L := by
    ext w
    simp [survivesThroughSet, SurvivesThrough, staysThrough, spec, liftSet]
  have hreal := survival_actual K R x L
  unfold survivalProbability
  rw [hset, ← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  congr 1
  rw [← measureReal_def, hreal]
  simp [survival]

/-- Distinct comparison starts have distinct path laws (time-0 occupation). -/
theorem pathLaw_ne (K : RationalMarkovMatrix n) {y₁ y₂ : Fin n} (hne : y₁ ≠ y₂) :
    (realizedModel K).pathLaw (Measure.dirac (decode y₁)) ≠
      (realizedModel K).pathLaw (Measure.dirac (decode y₂)) := by
  intro heq
  have h₁ := survival_actual K {y₁} y₁ 0
  have h₂ := survival_actual K {y₁} y₂ 0
  rw [heq] at h₁
  rw [h₁] at h₂
  simp [exitTarget, hne.symm] at h₂

def CQ1Checks (K₀ K₁ : RationalMarkovMatrix n) (R basin B₁ Q : Finset (Fin n)) (L : ℕ)
    (η κ : ℚ) (y₁ y₂ : Fin n) : Prop :=
  basin ⊆ R ∧ B₁ ⊆ basin ∧ y₁ ∈ B₁ ∧ y₂ ∈ B₁ ∧ y₁ ≠ y₂ ∧
  0 ≤ η ∧ η ≤ 1 ∧ (∀ x ∈ R, 1 - η ≤ survival K₀ R L x) ∧
  0 < κ ∧ (∀ x ∈ B₁, κ ≤ |survival K₀ Q L x - survival K₁ Q L x|) ∧
  ∃ x ∈ B₁, |survival K₀ Q L x - survival K₁ Q L x| = κ

instance (K₀ K₁ : RationalMarkovMatrix n) (R basin B₁ Q : Finset (Fin n)) (L : ℕ) (η κ : ℚ)
    (y₁ y₂ : Fin n) : Decidable (CQ1Checks K₀ K₁ R basin B₁ Q L η κ y₁ y₂) := by
  unfold CQ1Checks
  infer_instance

def checkCQ1 (K₀ K₁ : RationalMarkovMatrix n) (R basin B₁ Q : Finset (Fin n)) (L : ℕ)
    (η κ : ℚ) (y₁ y₂ : Fin n) : Bool :=
  decide (CQ1Checks K₀ K₁ R basin B₁ Q L η κ y₁ y₂)

theorem checkCQ1_sound (K₀ K₁ : RationalMarkovMatrix n) (R basin B₁ Q : Finset (Fin n)) (L : ℕ)
    (η κ : ℚ) (y₁ y₂ : Fin n) (h : checkCQ1 K₀ K₁ R basin B₁ Q L η κ y₁ y₂ = true) :
    CQ1Checks K₀ K₁ R basin B₁ Q L η κ y₁ y₂ := by
  unfold checkCQ1 at h
  exact of_decide_eq_true h

/-- A comparison set whose states are exactly the declared `B₁`. -/
noncomputable def comparison (K₀ : RationalMarkovMatrix n) (R basin B₁ : Finset (Fin n))
    (hbasin : basin ⊆ R) (hB₁ : B₁ ⊆ basin) {y₁ y₂ : Fin n} (h₁ : y₁ ∈ B₁) (h₂ : y₂ ∈ B₁)
    (hne : y₁ ≠ y₂) : ConstitutiveComparisonSet (realizedModel K₀) (spec R basin) where
  states := liftSet B₁
  states_measurable := MeasurableSet.of_discrete
  states_subset_basin := fun _ hy => ⟨hB₁ hy, hbasin (hB₁ hy)⟩
  pathLawNontrivial := ⟨decode y₁, h₁, decode y₂, h₂, pathLaw_ne K₀ hne⟩

theorem effect_eq (K₀ K₁ : RationalMarkovMatrix n) (Q : Finset (Fin n)) (L : ℕ)
    (y : JointState Unit (Fin n)) :
    constitutiveEffect (realizedModel K₀) ((prefixScore Q L).toRegimeProperty L)
      (rationalStrategicIntervention K₀ K₁) y =
      (|survival K₀ Q L (encode y) - survival K₁ Q L (encode y)| : ℚ) := by
  rw [← decode_encode y]
  unfold constitutiveEffect
  rw [baseline_value, intervened_value, Real.dist_eq]
  push_cast
  rfl

/-- **CQ-1 certificate.** Region-wide finite persistence and a positive
    uniform margin over a comparison set whose states are exactly `B₁`. -/
theorem checked_finite_constitutive_certificate (K₀ K₁ : RationalMarkovMatrix n)
    (R basin B₁ Q : Finset (Fin n)) (L : ℕ) (η κ : ℚ) (y₁ y₂ : Fin n)
    (h : checkCQ1 K₀ K₁ R basin B₁ Q L η κ y₁ y₂ = true) :
    ∃ C : ConstitutiveComparisonSet (realizedModel K₀) (spec R basin),
      C.states = liftSet B₁ ∧
      FiniteConstitutiveCertificate (realizedModel K₀) (spec R basin)
        (researchActionFamily K₀) C (rationalStrategicIntervention K₀ K₁) L
        (prefixScore Q L) (ENNReal.ofReal (η : ℝ)) (κ : ℝ) ∧
      constitutiveMargin (realizedModel K₀) (spec R basin) (researchActionFamily K₀)
        ((prefixScore Q L).toRegimeProperty L) C (rationalStrategicIntervention K₀ K₁) = κ := by
  obtain ⟨hbasin, hB₁, h₁, h₂, hne, hη0, hη1, hsurv, hκ, hle, x, hx, hatt⟩ :=
    checkCQ1_sound K₀ K₁ R basin B₁ Q L η κ y₁ y₂ h
  let C := comparison K₀ R basin B₁ hbasin hB₁ h₁ h₂ hne
  have himage : constitutiveEffect (realizedModel K₀) ((prefixScore Q L).toRegimeProperty L)
      (rationalStrategicIntervention K₀ K₁) '' C.states =
      constitutiveEffect (realizedModel K₀) ((prefixScore Q L).toRegimeProperty L)
      (rationalStrategicIntervention K₀ K₁) '' liftSet B₁ := rfl
  have hlower : ∀ r ∈ constitutiveEffect (realizedModel K₀) ((prefixScore Q L).toRegimeProperty L)
      (rationalStrategicIntervention K₀ K₁) '' C.states, (κ : ℝ) ≤ r := by
    rintro r ⟨y, hy, rfl⟩
    rw [effect_eq]
    exact_mod_cast hle (encode y) hy
  have hmargin : constitutiveMargin (realizedModel K₀) (spec R basin) (researchActionFamily K₀)
      ((prefixScore Q L).toRegimeProperty L) C (rationalStrategicIntervention K₀ K₁) = κ := by
    unfold constitutiveMargin
    apply le_antisymm
    · apply csInf_le
      · exact ⟨0, by rintro r ⟨y, -, rfl⟩; exact constitutiveEffect_nonneg _ _ _ _⟩
      · refine ⟨decode x, hx, ?_⟩
        rw [effect_eq, encode_decode, hatt]
    · exact le_csInf ⟨_, decode x, hx, rfl⟩ hlower
  refine ⟨C, rfl, ⟨⟨?_, ?_⟩, by exact_mod_cast hκ, hmargin.ge⟩, hmargin⟩
  · exact ENNReal.ofReal_le_one.mpr (by exact_mod_cast hη1)
  · intro y hy
    have hyR : encode y ∈ R := hy
    rw [← decode_encode y, survivalProbability_eq, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ (by exact_mod_cast hη0)]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hsurv _ hyR)

end PermanssonResearch.ApplicationBridge.FiniteScoreReceipt
