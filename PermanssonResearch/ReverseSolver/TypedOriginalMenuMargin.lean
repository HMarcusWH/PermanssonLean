import PermanssonResearch.ReverseSolver.CheckedRationalEventValue
import PermanssonResearch.ReverseSolver.FrozenConstitutiveMenu
import PermanssonResearch.ReverseSolver.ExecutableConstitutiveSelection
import PermanssonResearch.MultipleLimit.FiniteObservedUniformMargin
import Mathlib.Tactic

/-!
# C10 — exact computed menu margins equal the ORIGINAL Permansson margin

This is the unmodified original `constitutiveMargin` on an authentic
`ConstitutiveComparisonSet` of the D0-constructed alpha/P/U strategic-world
model. No special post-hoc comparison subset, new regime predicate or
assumed path-law values are permitted. The same fixed infinite-path
`eventuallyObservedProperty` is used for baseline and typed intervention.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

open PermanssonLean
open PermanssonLean.RegimeSpecification
open FiniteStrategicRealization
open FrozenConstitutiveMenu
open PermanssonResearch.MultipleLimit.FrozenObservedEvent
open PermanssonResearch.MultipleLimit.FiniteObservedUniformMargin

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

/-- Exactly the specified normalized finite interventions, represented as
original admissible strategic alpha replacements with P and U fixed. -/
def realizedNumericMenu {n m : ℕ}
    (raw : RawInput n m) (checked : CheckedInput raw) :
    FrozenMenu (realizedModel checked.baseline)
      (researchActionFamily checked.baseline) (Fin m) where
  indices := Finset.univ
  nonempty := ⟨⟨0, checked.menuPositive⟩, Finset.mem_univ _⟩
  choice := fun i => rationalStrategicIntervention
    checked.baseline (checked.members i)

/-- The original pointwise effect for any of the typed menu members is
literally the computed exact rational difference of the TWO original
infinite-path event probabilities. -/
theorem typed_numericEffect_eq_original {n m : ℕ} [NeZero n]
    (raw : RawInput n m) (checked : CheckedInput raw)
    (cert : MenuCertificate n m)
    (hCheck : checkMenu raw checked cert = true)
    (spec : RegimeSpecification (JointState Unit (Fin n)) Bool)
    (hDescriptor : ∀ x : Fin n,
      spec.descriptor (decode x) = raw.descriptor x)
    (i : Fin m) (x : Fin n) :
    constitutiveEffect (realizedModel checked.baseline)
      (eventuallyObservedProperty spec.descriptor true)
      (rationalStrategicIntervention checked.baseline (checked.members i))
      (decode x) = (numericalEffect raw cert i x : ℝ) := by
  have hMenu := checkMenu_sound raw checked cert hCheck
  have hBase : checkDirichlet checked.baseline cert.baseline = true :=
    checkDirichlet_complete checked.baseline cert.baseline hMenu.1
  have hMember : checkDirichlet (checked.members i) (cert.members i) = true :=
    checkDirichlet_complete (checked.members i) (cert.members i) (hMenu.2 i)
  have hDescrEq : spec.descriptor = (fun y => raw.descriptor (encode y)) := by
    funext y
    have h := hDescriptor (encode y)
    simpa only [decode_encode] using h
  change dist
      ((realizedModel checked.baseline).pathLaw (Measure.dirac (decode x))).real
        (eventuallyObserved spec.descriptor true)
      ((rationalStrategicIntervention checked.baseline
          (checked.members i)).intervention.apply.pathLaw
          (Measure.dirac (decode x))).real
        (eventuallyObserved spec.descriptor true) =
      (numericalEffect raw cert i x : ℝ)
  rw [hDescrEq, rationalStrategicIntervention_applied]
  rw [checked_eventValue_eq_actual_path checked.baseline cert.baseline
        hBase raw.descriptor x,
      checked_eventValue_eq_actual_path (checked.members i) (cert.members i)
        hMember raw.descriptor x]
  simp [numericalEffect, Real.dist_eq]

/-- This is the full original `B₁` constitutive infimum, proven equal
to the exact finite minimum over the COMPLETE declared rational B₁ copy.
The baseline Exact GR proof is not needed for this numerical identity. -/
theorem typed_numericMargin_eq_original {n m : ℕ} [NeZero n]
    (raw : RawInput n m) (checked : CheckedInput raw)
    (cert : MenuCertificate n m)
    (hCheck : checkMenu raw checked cert = true)
    (spec : RegimeSpecification (JointState Unit (Fin n)) Bool)
    (B₁ : ConstitutiveComparisonSet (realizedModel checked.baseline) spec)
    (hDescriptor : ∀ x : Fin n,
      spec.descriptor (decode x) = raw.descriptor x)
    (hComparison : ∀ x : Fin n,
      x ∈ raw.comparison ↔ decode x ∈ B₁.states)
    (i : Fin m) :
    constitutiveMargin (realizedModel checked.baseline) spec
      (researchActionFamily checked.baseline)
      (eventuallyObservedProperty spec.descriptor true) B₁
      (rationalStrategicIntervention checked.baseline (checked.members i)) =
        (numericalMargin raw checked cert i : ℝ) := by
  classical
  let M := realizedModel checked.baseline
  let F := researchActionFamily checked.baseline
  let ψ := eventuallyObservedProperty spec.descriptor true
  let J := rationalStrategicIntervention checked.baseline (checked.members i)
  have hEffect (x : Fin n) :
      constitutiveEffect M ψ J (decode x) =
        (numericalEffect raw cert i x : ℝ) :=
    typed_numericEffect_eq_original raw checked cert hCheck spec hDescriptor i x
  have hNumMin : ∃ x ∈ raw.comparison,
      numericalMargin raw checked cert i = numericalEffect raw cert i x := by
    obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image raw.comparison
      (numericalEffect raw cert i) checked.comparisonNonempty
    refine ⟨x, hx, le_antisymm (Finset.inf'_le _ hx) ?_⟩
    exact Finset.le_inf' _ _ (fun y hy => hmin y hy)
  apply le_antisymm
  · obtain ⟨x, hx, hmin⟩ := hNumMin
    have hOrigLe := constitutiveMargin_le_effect M spec F ψ B₁ J
      ((hComparison x).mp hx)
    rw [hEffect x] at hOrigLe
    rw [hmin]
    exact hOrigLe
  · obtain ⟨y, hy, hmin⟩ := finite_margin_attained M spec F ψ B₁ J
    have hx : encode y ∈ raw.comparison := by
      apply (hComparison (encode y)).mpr
      simpa only [decode_encode] using hy
    have hnum : numericalMargin raw checked cert i ≤
        numericalEffect raw cert i (encode y) :=
      Finset.inf'_le _ hx
    have hnumReal : (numericalMargin raw checked cert i : ℝ) ≤
        (numericalEffect raw cert i (encode y) : ℝ) := by
      exact_mod_cast hnum
    calc
      (numericalMargin raw checked cert i : ℝ) ≤
        (numericalEffect raw cert i (encode y) : ℝ) := hnumReal
      _ = constitutiveEffect M ψ J y := by
        simpa only [decode_encode] using (hEffect (encode y)).symm
      _ = constitutiveMargin M spec F ψ B₁ J := hmin.symm

/-- Every complete checked rational menu optimizes the genuinely ORIGINAL
unmodified constitutive margin, not the old D0 hitting-value objective. -/
theorem realized_numeric_menu_margin {n m : ℕ} [NeZero n]
    (raw : RawInput n m) (checked : CheckedInput raw)
    (cert : MenuCertificate n m)
    (hCheck : checkMenu raw checked cert = true)
    (spec : RegimeSpecification (JointState Unit (Fin n)) Bool)
    (B₁ : ConstitutiveComparisonSet (realizedModel checked.baseline) spec)
    (hDescriptor : ∀ x : Fin n,
      spec.descriptor (decode x) = raw.descriptor x)
    (hComparison : ∀ x : Fin n,
      x ∈ raw.comparison ↔ decode x ∈ B₁.states)
    (i : Fin m) :
    menuConstitutiveMargin (realizedModel checked.baseline) spec
      (researchActionFamily checked.baseline) B₁
      (realizedNumericMenu raw checked) i =
        (numericalMargin raw checked cert i : ℝ) := by
  exact typed_numericMargin_eq_original raw checked cert hCheck
    spec B₁ hDescriptor hComparison i

/-- The executable selected index genuinely dominates EVERY originally
listed admissible strategic intervention in original real-valued margin. -/
theorem realized_numeric_menu_selected_dominates {n m : ℕ} [NeZero n]
    (raw : RawInput n m) (checked : CheckedInput raw)
    (cert : MenuCertificate n m)
    (hCheck : checkMenu raw checked cert = true)
    (spec : RegimeSpecification (JointState Unit (Fin n)) Bool)
    (B₁ : ConstitutiveComparisonSet (realizedModel checked.baseline) spec)
    (hDescriptor : ∀ x : Fin n,
      spec.descriptor (decode x) = raw.descriptor x)
    (hComparison : ∀ x : Fin n,
      x ∈ raw.comparison ↔ decode x ∈ B₁.states)
    (i : Fin m) :
    menuConstitutiveMargin (realizedModel checked.baseline) spec
      (researchActionFamily checked.baseline) B₁
      (realizedNumericMenu raw checked) i ≤
    menuConstitutiveMargin (realizedModel checked.baseline) spec
      (researchActionFamily checked.baseline) B₁
      (realizedNumericMenu raw checked) (selectBest raw checked cert) := by
  rw [realized_numeric_menu_margin raw checked cert hCheck
        spec B₁ hDescriptor hComparison i,
      realized_numeric_menu_margin raw checked cert hCheck
        spec B₁ hDescriptor hComparison (selectBest raw checked cert)]
  exact_mod_cast (selected_dominates raw checked cert i)

end
end C10
end ReverseSolver
end PermanssonResearch