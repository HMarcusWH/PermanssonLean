import verification.research.tranche5_q05_conditional_margin_correction_addendum
import verification.research.tranche6_q05_whole_path_identification

/-!
# Q-05 addendum: original whole-path margins

The preceding whole-path calculation discharges both explicit identification
obligations of the historical conditional bridge.  The resulting effects and
infimum margins retain the original admitted interventions, property maps and
full comparison sets.  No output identity is assumed in any theorem below.

These declarations concern the exact original margin values.  They do not
change the independent certification ledger or establish an Exact GR claim.
-/

namespace PermanssonResearch.Quotient.Q05OriginalMarginClosure

open PermanssonLean
open PermanssonLean.RegimeSpecification
open PermanssonResearch.Quotient.Q05ActualOriginalMarginWitnessFixture
open PermanssonResearch.Quotient.Q05ActualOriginalMarginAdapter
open PermanssonResearch.Quotient.Q05ConditionalExactMargin
open PermanssonResearch.Quotient.Q05WholePathIdentification

set_option autoImplicit false

/-- Both original fine baseline and admitted-intervention outputs are
identified with their exact rational values at both original starts. -/
theorem fine_whole_path_identified : FineWholePathIdentified := by
  constructor
  · intro x
    exact fine_whole_path_output false false x
  · intro x
    change baselinePropertyValue fineOriginalProperty
      fineJ.intervention.apply (false, x) = _
    rw [fineJ_is_treated_source]
    exact fine_whole_path_output true false x

/-- Both original coarse baseline and admitted-intervention outputs are
identified at every state of the original coarse comparison set. -/
theorem coarse_whole_path_identified : CoarseWholePathIdentified := by
  constructor
  · intro x
    exact coarse_whole_path_output false x
  · intro x
    change baselinePropertyValue coarseOriginalProperty
      coarseJ.intervention.apply ((), x) = _
    rw [coarseJ_is_treated_source]
    exact coarse_whole_path_output true x

/-- The genuine fine pointwise effect at either original comparison start. -/
theorem fine_original_effect (x : Bool) :
    constitutiveEffect (fineModel false) fineOriginalProperty
      fineJ (false, x) = (19/90 : ℝ) :=
  fine_original_effect_of_path_identification fine_whole_path_identified x

/-- The genuine coarse pointwise effect at either original comparison start. -/
theorem coarse_original_effect (x : Bool) :
    constitutiveEffect (coarseModel false) coarseOriginalProperty
      coarseJ ((), x) = (1/5 : ℝ) :=
  coarse_original_effect_of_path_identification coarse_whole_path_identified x

/-- The fine constitutive margin uses the entire frozen original B₁ set. -/
theorem fine_original_margin :
    constitutiveMargin (fineModel false) fineSpec fineFamily
      fineOriginalProperty fineComparisonSet fineJ = (19/90 : ℝ) :=
  fine_original_margin_of_path_identification fine_whole_path_identified

/-- The coarse constitutive margin uses its entire original comparison set. -/
theorem coarse_original_margin :
    constitutiveMargin (coarseModel false) coarseSpec coarseFamily
      coarseOriginalProperty coarseComparisonSet coarseJ = (1/5 : ℝ) :=
  coarse_original_margin_of_path_identification coarse_whole_path_identified

/-- Exact original margin gap, with both canonical path-law identification
obligations discharged by the preceding whole-path calculation. -/
theorem original_margin_gap :
    |constitutiveMargin (fineModel false) fineSpec fineFamily
         fineOriginalProperty fineComparisonSet fineJ -
      constitutiveMargin (coarseModel false) coarseSpec coarseFamily
         coarseOriginalProperty coarseComparisonSet coarseJ| = (1/90 : ℝ) :=
  original_margin_gap_of_path_identification
    fine_whole_path_identified coarse_whole_path_identified

end PermanssonResearch.Quotient.Q05OriginalMarginClosure

#check PermanssonResearch.Quotient.Q05OriginalMarginClosure.fine_whole_path_identified
#print axioms PermanssonResearch.Quotient.Q05OriginalMarginClosure.fine_whole_path_identified
#check PermanssonResearch.Quotient.Q05OriginalMarginClosure.coarse_whole_path_identified
#print axioms PermanssonResearch.Quotient.Q05OriginalMarginClosure.coarse_whole_path_identified
#check PermanssonResearch.Quotient.Q05OriginalMarginClosure.fine_original_effect
#print axioms PermanssonResearch.Quotient.Q05OriginalMarginClosure.fine_original_effect
#check PermanssonResearch.Quotient.Q05OriginalMarginClosure.coarse_original_effect
#print axioms PermanssonResearch.Quotient.Q05OriginalMarginClosure.coarse_original_effect
#check PermanssonResearch.Quotient.Q05OriginalMarginClosure.fine_original_margin
#print axioms PermanssonResearch.Quotient.Q05OriginalMarginClosure.fine_original_margin
#check PermanssonResearch.Quotient.Q05OriginalMarginClosure.coarse_original_margin
#print axioms PermanssonResearch.Quotient.Q05OriginalMarginClosure.coarse_original_margin
#check PermanssonResearch.Quotient.Q05OriginalMarginClosure.original_margin_gap
#print axioms PermanssonResearch.Quotient.Q05OriginalMarginClosure.original_margin_gap
