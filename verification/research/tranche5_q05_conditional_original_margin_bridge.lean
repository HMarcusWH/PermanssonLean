import PermanssonResearch.Quotient.Q05ActualAtomClosure
import Mathlib.Tactic

/-!
# Q-05 exact original margin: conditional bridge only

This proves the algebraic and original full-B₁ infimum portion of Q-05,
**conditional** on eight separate baseline/treated canonical whole-path
output identities. It does NOT establish those identities; their proof is the
remaining substantive work. No admitted axioms, no sorry, and no Exact GR
claim are introduced.
-/

open MeasureTheory ProbabilityTheory Set

namespace PermanssonResearch.Quotient.Q05ConditionalExactMargin
open PermanssonLean
open PermanssonLean.RegimeSpecification
open PermanssonResearch.Quotient.Q05ActualOriginalMarginWitnessFixture
open PermanssonResearch.Quotient.Q05ActualOriginalMarginAdapter
open PermanssonResearch.Quotient.DiscountedOriginalMargin

set_option autoImplicit false

noncomputable def fineOriginalProperty : RegimePropertyMap FineState ℝ :=
  projectedDiscountedProperty compression (1/3 : ℝ) observedWorldScore

noncomputable def coarseOriginalProperty : RegimePropertyMap CoarseState ℝ :=
  discountedWholePathProperty (1/3 : ℝ) observedWorldScore

/-- This is an explicit, independently dischargeable path-law obligation, NOT
an assumption that the original margins have already been proved. -/
def FineWholePathIdentified : Prop :=
  (∀ x : Bool, baselinePropertyValue fineOriginalProperty
      (fineModel false) (false, x) =
        (fineDiscountedOutput false false x : ℝ)) ∧
  (∀ x : Bool, intervenedPropertyValue fineOriginalProperty
      fineJ.intervention (false, x) =
        (fineDiscountedOutput true false x : ℝ))

def CoarseWholePathIdentified : Prop :=
  (∀ x : Bool, baselinePropertyValue coarseOriginalProperty
      (coarseModel false) ((), x) =
        (coarseDiscountedOutput false x : ℝ)) ∧
  (∀ x : Bool, intervenedPropertyValue coarseOriginalProperty
      coarseJ.intervention ((), x) =
        (coarseDiscountedOutput true x : ℝ))

/-- Per-start original pointwise effect follows from the genuine point-started
canonical path-law identities, not from a surrogate Markov table. -/
theorem fine_original_effect_of_path_identification
    (h : FineWholePathIdentified) (x : Bool) :
    constitutiveEffect (fineModel false) fineOriginalProperty
      fineJ (false, x) = (19/90 : ℝ) := by
  rcases h with ⟨hb, hj⟩
  unfold constitutiveEffect
  rw [hb x, hj x, Real.dist_eq]
  have hv : (fineDiscountedOutput true false x : ℝ) -
      (fineDiscountedOutput false false x : ℝ) = 19/90 := by
    have hq := (actual_two_start_effects x).1
    unfold fineOriginalEffect at hq
    exact_mod_cast hq
  rw [abs_sub_comm, hv]
  norm_num

theorem coarse_original_effect_of_path_identification
    (h : CoarseWholePathIdentified) (x : Bool) :
    constitutiveEffect (coarseModel false) coarseOriginalProperty
      coarseJ ((), x) = (1/5 : ℝ) := by
  rcases h with ⟨hb, hj⟩
  unfold constitutiveEffect
  rw [hb x, hj x, Real.dist_eq]
  have hv : (coarseDiscountedOutput true x : ℝ) -
      (coarseDiscountedOutput false x : ℝ) = 1/5 := by
    have hq := (actual_two_start_effects x).2
    unfold coarseOriginalEffect at hq
    exact_mod_cast hq
  rw [abs_sub_comm, hv]
  norm_num

/-- Conditional exact original fine constitutive margin, taken over ALL of the
original frozen B₁ comparison states, not a restricted single-start domain. -/
theorem fine_original_margin_of_path_identification
    (h : FineWholePathIdentified) :
    constitutiveMargin (fineModel false) fineSpec fineFamily
      fineOriginalProperty fineComparisonSet fineJ = (19/90 : ℝ) := by
  have heq : constitutiveEffect (fineModel false) fineOriginalProperty fineJ ''
      fineComparisonSet.states = {(19/90 : ℝ)} := by
    apply Set.Subset.antisymm
    · rintro z ⟨y, hy, rfl⟩
      rcases y with ⟨s, x⟩
      have hs : s = false := by
        change (s, x) ∈ twoStartDomain at hy
        simp only [twoStartDomain, Set.mem_insert_iff,
          Set.mem_singleton_iff, Prod.mk.injEq] at hy
        rcases hy with hx | hx
        · exact hx.1
        · exact hx.1
      subst s
      simpa using (fine_original_effect_of_path_identification h x)
    · intro z hz
      have hz' : z = (19/90 : ℝ) := by simpa using hz
      subst z
      refine ⟨(false, false), ?_, ?_⟩
      · change (false, false) ∈ twoStartDomain
        simp [twoStartDomain]
      · exact fine_original_effect_of_path_identification h false
  unfold constitutiveMargin
  rw [heq]
  simp

/-- Conditional exact original coarse margin over the FULL declared B₁ image. -/
theorem coarse_original_margin_of_path_identification
    (h : CoarseWholePathIdentified) :
    constitutiveMargin (coarseModel false) coarseSpec coarseFamily
      coarseOriginalProperty coarseComparisonSet coarseJ = (1/5 : ℝ) := by
  have heq : constitutiveEffect (coarseModel false) coarseOriginalProperty coarseJ ''
      coarseComparisonSet.states = {(1/5 : ℝ)} := by
    apply Set.Subset.antisymm
    · rintro z ⟨y, hy, rfl⟩
      rcases y with ⟨u, x⟩
      cases u
      simpa using (coarse_original_effect_of_path_identification h x)
    · intro z hz
      have hz' : z = (1/5 : ℝ) := by simpa using hz
      subst z
      refine ⟨((), false), Set.mem_univ _, ?_⟩
      exact coarse_original_effect_of_path_identification h false
  unfold constitutiveMargin
  rw [heq]
  simp

/-- The exact gap is conditional on BOTH canonical path-law identification
claims. This theorem may never be used as an unconditional original witness. -/
theorem original_margin_gap_of_path_identification
    (hf : FineWholePathIdentified)
    (hc : CoarseWholePathIdentified) :
    |constitutiveMargin (fineModel false) fineSpec fineFamily
         fineOriginalProperty fineComparisonSet fineJ -
      constitutiveMargin (coarseModel false) coarseSpec coarseFamily
         coarseOriginalProperty coarseComparisonSet coarseJ| = (1/90 : ℝ) := by
  rw [fine_original_margin_of_path_identification hf,
      coarse_original_margin_of_path_identification hc]
  norm_num

end PermanssonResearch.Quotient.Q05ConditionalExactMargin

-- Every theorem above remains explicitly conditional on typed path-law identities.
-- This probe is not a certificate that those identities hold.
#check PermanssonResearch.Quotient.Q05ConditionalExactMargin.fine_original_effect_of_path_identification
#print axioms PermanssonResearch.Quotient.Q05ConditionalExactMargin.fine_original_effect_of_path_identification
#check PermanssonResearch.Quotient.Q05ConditionalExactMargin.coarse_original_effect_of_path_identification
#print axioms PermanssonResearch.Quotient.Q05ConditionalExactMargin.coarse_original_effect_of_path_identification
#check PermanssonResearch.Quotient.Q05ConditionalExactMargin.fine_original_margin_of_path_identification
#print axioms PermanssonResearch.Quotient.Q05ConditionalExactMargin.fine_original_margin_of_path_identification
#check PermanssonResearch.Quotient.Q05ConditionalExactMargin.coarse_original_margin_of_path_identification
#print axioms PermanssonResearch.Quotient.Q05ConditionalExactMargin.coarse_original_margin_of_path_identification
#check PermanssonResearch.Quotient.Q05ConditionalExactMargin.original_margin_gap_of_path_identification
#print axioms PermanssonResearch.Quotient.Q05ConditionalExactMargin.original_margin_gap_of_path_identification
