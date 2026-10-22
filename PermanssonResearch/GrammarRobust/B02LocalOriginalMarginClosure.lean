import PermanssonResearch.GrammarRobust.BooleanMinimalityCases
import PermanssonResearch.GrammarRobust.OriginalLowerSetTransport
import Mathlib.Tactic

/-!
# B-02: original constitutive minimality with local lower-set coverage

The actual two-atom bank, typed alpha-P-U block interventions, frozen OR
whole-path property, and original comparison set are unchanged. The fine
grammar admits EMPTY and the COMPLETE joint block only; this admission
constraint is frozen ex ante. The coarsening Fin 2 -> Fin 1 is genuinely
noninjective, so there is no global component-level grammar isomorphism.
Every *admitted* strict lower block of the chosen positive fine intervention
has a matching coarse preimage. No unjustified downward closure or
global subblock equivalence is asserted.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch.GrammarRobust.B02LocalOriginalMarginClosure

open PermanssonLean
open PermanssonLean.RegimeSpecification
open PermanssonResearch.GrammarRobust
open BooleanModel BooleanBaseline BooleanDynamics BooleanPersistence
open BooleanOneStepEvents BooleanEffects BooleanMinimalityCases

set_option autoImplicit false

/-- Source-frozen admissibility excludes partial patches. Because B-02 is
about an admitted explanatory grammar, it must never treat syntactically
valid but inadmissible subsets as actual interventions. -/
noncomputable def fullOrEmptyFine :
    PartitionGrammar (Fin 1) (Fin 1) (Fin 2) where
  atomsOf := fine.atomsOf
  nonempty := fine.nonempty
  disjoint := fine.disjoint
  cover := fine.cover
  allowed := fun D => D = ∅ ∨ D = Finset.univ
  allowed_empty := Or.inl rfl

theorem fullOrEmptyFine_joint_allowed :
    fullOrEmptyFine.allowed ({0,1} : Finset (Fin 2)) := by
  right
  decide

theorem fullOrEmptyFine_empty_allowed :
    fullOrEmptyFine.allowed (∅ : Finset (Fin 2)) := by
  left
  rfl

theorem fullOrEmptyFine_rejects_singleton_zero :
    ¬ fullOrEmptyFine.allowed ({0} : Finset (Fin 2)) := by
  simp [fullOrEmptyFine]

theorem fullOrEmptyFine_rejects_singleton_one :
    ¬ fullOrEmptyFine.allowed ({1} : Finset (Fin 2)) := by
  simp [fullOrEmptyFine]

/-- The original coarse grammar accepts its empty and full blocks. -/
noncomputable def actualCoarsening : Coarsening fullOrEmptyFine coarse where
  map := fun _ => 0
  onto := by
    intro c
    refine ⟨0, ?_⟩
    exact Subsingleton.elim _ _
  coarse_atoms := by
    intro c
    ext a
    have hc : c = (0 : Fin 1) := Subsingleton.elim _ _
    subst c
    cases a with
    | inl i =>
        have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
        subst i
        simp [coarse, fullOrEmptyFine, fine]
    | inr i =>
        have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
        subst i
        simp [coarse, fullOrEmptyFine, fine]
  respects_allowed := by
    intro D _
    by_cases h : (0 : Fin 1) ∈ D
    · right
      change (Finset.univ.filter
        (fun _ : Fin 2 => (0 : Fin 1) ∈ D)) = Finset.univ
      simp [h]
    · left
      change (Finset.univ.filter
        (fun _ : Fin 2 => (0 : Fin 1) ∈ D)) = ∅
      simp [h]

theorem actualCoarsening_not_global_injective :
    ¬ Function.Injective actualCoarsening.map := by
  intro hinj
  have he : actualCoarsening.map (0 : Fin 2) =
      actualCoarsening.map (1 : Fin 2) := rfl
  have hh : (0 : Fin 2) = 1 := hinj he
  exact absurd hh (by decide)

theorem actualCoarsening_lift_full :
    actualCoarsening.lift ({0} : Finset (Fin 1)) =
      (Finset.univ : Finset (Fin 2)) := by
  ext f
  simp [Coarsening.lift, actualCoarsening]

theorem actualCoarsening_lift_empty :
    actualCoarsening.lift (∅ : Finset (Fin 1)) =
      (∅ : Finset (Fin 2)) := by
  ext f
  simp [Coarsening.lift, actualCoarsening]

/-- The genuine local strict-lower-set coverage, established for the
original admitted-block poset, not postulated as a general isomorphism. -/
theorem original_admitted_lower_coverage :
    ∀ E : Finset (Fin 2), fullOrEmptyFine.allowed E →
      E ⊂ actualCoarsening.lift ({0} : Finset (Fin 1)) →
      ∃ C : Finset (Fin 1),
        coarse.allowed C ∧ C ⊂ ({0} : Finset (Fin 1)) ∧
        actualCoarsening.lift C = E := by
  intro E hE hstrict
  change E = ∅ ∨ E = Finset.univ at hE
  rcases hE with he | he
  · refine ⟨∅, trivial, (by decide), ?_⟩
    rw [actualCoarsening_lift_empty, he]
  · subst E
    rw [actualCoarsening_lift_full] at hstrict
    exact False.elim (lt_irrefl _ hstrict)

/-- The coarse OR intervention has the actual ORIGINAL uniform margin
one, not merely a syntactically named positive predicate. -/
def originalCoarsePositive (D : Finset (Fin 1)) : Prop :=
  ∃ hD : coarse.allowed D,
    0 < blockMargin baseline bank coarse ⟨D, hD⟩ spec
      (propertyAtOne orP) comparison

theorem coarse_original_OR_positive :
    originalCoarsePositive ({0} : Finset (Fin 1)) := by
  refine ⟨trivial, ?_⟩
  change 0 < blockMargin baseline bank coarse (coarseBlock {0})
    spec (propertyAtOne orP) comparison
  rw [coarse_margin_eq_fine_joint, or_joint_margin_one]
  norm_num

theorem coarse_original_empty_not_positive :
    ¬ originalCoarsePositive (∅ : Finset (Fin 1)) := by
  rintro ⟨h, hp⟩
  change 0 < blockMargin baseline bank coarse (coarseBlock ∅)
    spec (propertyAtOne orP) comparison at hp
  rw [coarse_empty_margin_zero] at hp
  norm_num at hp

theorem coarse_original_OR_minimal :
    IsMinimalAllowed coarse originalCoarsePositive
      ({0} : Finset (Fin 1)) := by
  refine ⟨trivial, coarse_original_OR_positive, ?_⟩
  intro E _ hproper hpositive
  have hE : E = ∅ := Finset.eq_empty_of_ssubset_singleton hproper
  exact coarse_original_empty_not_positive (hE ▸ hpositive)

/-- The existing general original-margin local coverage theorem now
INSTantiates nontrivially with the actual finite bank/grammar and
noninjective component map. -/
theorem original_local_minimality_without_global_isomorphism :
    IsMinimalAllowed fullOrEmptyFine
      (fun E => ∃ hE : fullOrEmptyFine.allowed E,
        0 < blockMargin baseline bank fullOrEmptyFine ⟨E,hE⟩ spec
          (propertyAtOne orP) comparison)
      (actualCoarsening.lift ({0} : Finset (Fin 1))) ∧
      ¬ Function.Injective actualCoarsening.map := by
  constructor
  · have htransport :=
      actualCoarsening.original_margin_minimal_iff_of_lower_coverage
        baseline bank spec (propertyAtOne orP) comparison
        ({0} : Finset (Fin 1)) trivial original_admitted_lower_coverage
    exact htransport.mp coarse_original_OR_minimal
  · exact actualCoarsening_not_global_injective

/-- This result is a local positive theorem, not a grant to admit the
excluded singleton patches or an unrestricted minimality transfer. -/
theorem false_extra_admission_rejected :
    ¬ fullOrEmptyFine.allowed ({0} : Finset (Fin 2)) :=
  fullOrEmptyFine_rejects_singleton_zero

end PermanssonResearch.GrammarRobust.B02LocalOriginalMarginClosure
