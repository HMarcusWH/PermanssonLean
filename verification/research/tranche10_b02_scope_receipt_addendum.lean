import PermanssonResearch.GrammarRobust.B02ActualOriginalMarginFixture
import PermanssonResearch.GrammarRobust.B02LocalOriginalMarginClosure
import PermanssonResearch.GrammarRobust.LocalOrderPositiveFixture
import Mathlib.Tactic

/-!
# Tranche 10: original B-02 and a genuinely local admitted-order transport

The original Boolean bank, baseline, canonical one-step path properties, and
comparison set are retained. AND has two incomparable minimal positive blocks;
XOR positivity and its original constitutive margin are not upward monotone.

The additional local-order example changes only the frozen admissibility of a
second grammar with the same physical partition. Its component map is identity.
The restricted grammar admits empty and action-only blocks; the original fine
grammar admits every subset. Local strict-lower coverage holds at the positive
AND action singleton, and actual original margins/minimality transport there.
The admitted orders are NOT globally order-isomorphic: the restricted carrier
is a chain, whereas the fine carrier contains incomparable singletons. This
addresses admitted-order nonisomorphism without conflating it with component-map
noninjectivity. No unconditional coarsening or independent acceptance follows.
-/

namespace PermanssonResearch.Certification.Tranche10B02

open PermanssonLean PermanssonLean.RegimeSpecification
open PermanssonResearch.GrammarRobust
open BooleanModel BooleanBaseline BooleanPersistence BooleanOneStepEvents BooleanEffects
open BooleanMinimalityCases

set_option autoImplicit false

/-- Distinctness and both failed subset relations are explicit. -/
theorem singleton_blocks_incomparable :
    ({0} : Finset (Fin 2)) ≠ {1} ∧
    ¬ ({0} : Finset (Fin 2)) ⊆ {1} ∧
    ¬ ({1} : Finset (Fin 2)) ⊆ {0} := by
  decide

/-- Two actual original-margin minimal blocks, with incomparability. -/
theorem two_incomparable_original_minima :
    IsMinimalAllowed fine andPos ({0} : Finset (Fin 2)) ∧
    IsMinimalAllowed fine andPos ({1} : Finset (Fin 2)) ∧
    ¬ ({0} : Finset (Fin 2)) ⊆ {1} ∧
    ¬ ({1} : Finset (Fin 2)) ⊆ {0} :=
  ⟨and_action_minimal, and_update_minimal,
    singleton_blocks_incomparable.2.1, singleton_blocks_incomparable.2.2⟩

theorem no_unique_original_minimal_block :
    ¬ ∃! D : Finset (Fin 2), IsMinimalAllowed fine andPos D := by
  rintro ⟨D, _, hunique⟩
  have h0 := hunique ({0} : Finset (Fin 2)) and_action_minimal
  have h1 := hunique ({1} : Finset (Fin 2)) and_update_minimal
  exact singleton_blocks_incomparable.1 (h0.trans h1.symm)

theorem xor_joint_not_positive :
    ¬ xorPos ({0, 1} : Finset (Fin 2)) := by
  change ¬ 0 < blockMargin baseline bank fine jointBlock spec
    (propertyAtOne xorP) comparison
  rw [xor_nonmonotone_margins.2]
  norm_num

/-- A subset-positive block can have a nonpositive admitted superset. -/
theorem xor_positivity_not_upward_monotone :
    ¬ (∀ D E : Finset (Fin 2), D ⊆ E → xorPos D → xorPos E) := by
  intro h
  exact xor_joint_not_positive
    (h {0} {0, 1} (by decide) xorPos_action)

/-- The actual real-valued margin, rather than a surrogate predicate. -/
theorem xor_original_margin_not_monotone :
    ¬ Monotone (fun D : Finset (Fin 2) =>
      blockMargin baseline bank fine (fineBlock D) spec
        (propertyAtOne xorP) comparison) := by
  intro h
  have hle := h (show ({0} : Finset (Fin 2)) ⊆ {0, 1} by decide)
  change blockMargin baseline bank fine actionBlock spec
      (propertyAtOne xorP) comparison ≤
    blockMargin baseline bank fine jointBlock spec
      (propertyAtOne xorP) comparison at hle
  rw [xor_nonmonotone_margins.1, xor_nonmonotone_margins.2] at hle
  norm_num at hle

/-- Admissibility is frozen before evaluating the unchanged physical model.
No physical atom or component partition is changed in this example. -/
noncomputable def restrictedGrammar :
    PartitionGrammar (Fin 1) (Fin 1) (Fin 2) where
  atomsOf := fine.atomsOf
  nonempty := fine.nonempty
  disjoint := fine.disjoint
  cover := fine.cover
  allowed := fun D => D = ∅ ∨ D = {0}
  allowed_empty := Or.inl rfl

/-- A valid Coarsening structure; the non-global feature is solely the admitted
carrier, not this identity component map. -/
noncomputable def restrictedCoarsening : Coarsening fine restrictedGrammar where
  map := id
  onto := Function.surjective_id
  coarse_atoms := by
    intro c
    classical
    change fine.atomsOf c =
      (Finset.univ.filter (fun f : Fin 2 => f = c)).biUnion fine.atomsOf
    ext a
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ha; exact ⟨c, rfl, ha⟩
    · rintro ⟨f, rfl, ha⟩; exact ha
  respects_allowed := by intro D hD; trivial

theorem restricted_component_map_identity :
    restrictedCoarsening.map = id := rfl

theorem restricted_lift_eq (D : Finset (Fin 2)) :
    restrictedCoarsening.lift D = D := by
  classical
  ext c
  change c ∈ Finset.univ.filter (fun f : Fin 2 => f ∈ D) ↔ c ∈ D
  constructor
  · intro h; exact (Finset.mem_filter.mp h).2
  · intro h; exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, h⟩

theorem restricted_selected_allowed :
    restrictedGrammar.allowed ({0} : Finset (Fin 2)) := Or.inr rfl

theorem restricted_selected_is_proper :
    restrictedCoarsening.lift ({0} : Finset (Fin 2)) ⊂ Finset.univ := by
  rw [restricted_lift_eq]
  decide

/-- Every admitted strict lower fine block of the selected singleton has a
restricted preimage. Blocks outside this lower set are intentionally absent. -/
theorem restricted_local_lower_coverage :
    ∀ E : Finset (Fin 2), fine.allowed E →
      E ⊂ restrictedCoarsening.lift ({0} : Finset (Fin 2)) →
      ∃ C : Finset (Fin 2), restrictedGrammar.allowed C ∧
        C ⊂ ({0} : Finset (Fin 2)) ∧ restrictedCoarsening.lift C = E := by
  intro E _ hE
  rw [restricted_lift_eq] at hE
  have he : E = ∅ := Finset.eq_empty_of_ssubset_singleton hE
  refine ⟨∅, Or.inl rfl, (by decide), ?_⟩
  rw [restricted_lift_eq, he]

/-- Equality is derived from the original expansion/model transport theorem. -/
theorem restricted_original_margin_eq
    (D : Finset (Fin 2)) (hD : restrictedGrammar.allowed D) :
    blockMargin baseline bank restrictedGrammar ⟨D, hD⟩ spec
      (propertyAtOne andP) comparison =
    blockMargin baseline bank fine (fineBlock D) spec
      (propertyAtOne andP) comparison := by
  have h := restrictedCoarsening.blockMargin_lift_eq baseline bank
    (⟨D, hD⟩ : AllowedBlock restrictedGrammar) spec
    (propertyAtOne andP) comparison
  have heq : restrictedCoarsening.liftAllowed
      (⟨D, hD⟩ : AllowedBlock restrictedGrammar) = fineBlock D := by
    change (⟨restrictedCoarsening.lift D, _⟩ : AllowedBlock fine) = ⟨D, _⟩
    simp only [restricted_lift_eq]
  rw [heq] at h
  exact h.symm

def restrictedPositive (D : Finset (Fin 2)) : Prop :=
  ∃ hD : restrictedGrammar.allowed D,
    0 < blockMargin baseline bank restrictedGrammar ⟨D, hD⟩ spec
      (propertyAtOne andP) comparison

theorem restricted_selected_original_margin_one :
    blockMargin baseline bank restrictedGrammar
      ⟨{0}, restricted_selected_allowed⟩ spec
      (propertyAtOne andP) comparison = 1 := by
  rw [restricted_original_margin_eq]
  exact and_singleton_margins_one.1

theorem restricted_empty_not_positive : ¬ restrictedPositive ∅ := by
  rintro ⟨hD, hpos⟩
  rw [restricted_original_margin_eq, fine_empty_margin_zero] at hpos
  norm_num at hpos

theorem restricted_original_minimal :
    IsMinimalAllowed restrictedGrammar restrictedPositive
      ({0} : Finset (Fin 2)) := by
  refine ⟨restricted_selected_allowed, ?_, ?_⟩
  · refine ⟨restricted_selected_allowed, ?_⟩
    rw [restricted_selected_original_margin_one]
    norm_num
  · intro E _ hE hpos
    have he : E = ∅ := Finset.eq_empty_of_ssubset_singleton hE
    exact restricted_empty_not_positive (he ▸ hpos)

/-- Apply the general original-margin theorem at the proper selected lower set. -/
theorem restricted_original_minimality_transport :
    IsMinimalAllowed fine
      (fun E => ∃ hE : fine.allowed E,
        0 < blockMargin baseline bank fine ⟨E, hE⟩ spec
          (propertyAtOne andP) comparison)
      (restrictedCoarsening.lift ({0} : Finset (Fin 2))) := by
  have h := restrictedCoarsening.original_margin_minimal_iff_of_lower_coverage
    baseline bank spec (propertyAtOne andP) comparison
    ({0} : Finset (Fin 2)) restricted_selected_allowed
    restricted_local_lower_coverage
  exact h.mp restricted_original_minimal

abbrev FineAdmitted := {D : Finset (Fin 2) // fine.allowed D}
abbrev RestrictedAdmitted := {D : Finset (Fin 2) // restrictedGrammar.allowed D}

noncomputable def admittedLift (D : RestrictedAdmitted) : FineAdmitted :=
  ⟨restrictedCoarsening.lift D.1, restrictedCoarsening.respects_allowed D.1 D.2⟩

theorem outside_block_admitted_and_uncovered :
    fine.allowed ({1} : Finset (Fin 2)) ∧
    ¬ ∃ C : Finset (Fin 2), restrictedGrammar.allowed C ∧
      restrictedCoarsening.lift C = ({1} : Finset (Fin 2)) := by
  constructor
  · trivial
  · rintro ⟨C, hC, heq⟩
    rw [restricted_lift_eq] at heq
    subst C
    change ({1} : Finset (Fin 2)) = ∅ ∨ ({1} : Finset (Fin 2)) = {0} at hC
    exact (by decide : ¬ (({1} : Finset (Fin 2)) = ∅ ∨
      ({1} : Finset (Fin 2)) = {0})) hC

theorem admitted_lift_not_surjective : ¬ Function.Surjective admittedLift := by
  intro hsurj
  obtain ⟨C, hC⟩ := hsurj ⟨{1}, trivial⟩
  exact outside_block_admitted_and_uncovered.2
    ⟨C.1, C.2, congrArg Subtype.val hC⟩

theorem restricted_admitted_chain (C D : RestrictedAdmitted) :
    C ≤ D ∨ D ≤ C := by
  have hC : C.val = ∅ ∨ C.val = {0} := C.property
  have hD : D.val = ∅ ∨ D.val = {0} := D.property
  change C.val ⊆ D.val ∨ D.val ⊆ C.val
  rcases hC with hC | hC <;> rcases hD with hD | hD <;>
    simp [hC, hD]

/-- A genuinely nonisomorphic pair of admitted-block orders, independently of
whether the particular lift is surjective. -/
theorem admitted_orders_not_isomorphic :
    ¬ Nonempty (RestrictedAdmitted ≃o FineAdmitted) := by
  rintro ⟨e⟩
  let a : FineAdmitted := ⟨{0}, trivial⟩
  let b : FineAdmitted := ⟨{1}, trivial⟩
  have h := restricted_admitted_chain (e.symm a) (e.symm b)
  rcases h with h | h
  · have hle : a ≤ b := by simpa using e.monotone h
    exact singleton_blocks_incomparable.2.1 hle
  · have hle : b ≤ a := by simpa using e.monotone h
    exact singleton_blocks_incomparable.2.2 hle

/-- Positive local original-margin transport survives the precise stronger
admitted-order nonisomorphism boundary; no global admission match is assumed. -/
theorem positive_local_transport_without_admitted_order_isomorphism :
    IsMinimalAllowed restrictedGrammar restrictedPositive
      ({0} : Finset (Fin 2)) ∧
    IsMinimalAllowed fine
      (fun E => ∃ hE : fine.allowed E,
        0 < blockMargin baseline bank fine ⟨E, hE⟩ spec
          (propertyAtOne andP) comparison)
      (restrictedCoarsening.lift ({0} : Finset (Fin 2))) ∧
    ¬ Nonempty (RestrictedAdmitted ≃o FineAdmitted) :=
  ⟨restricted_original_minimal, restricted_original_minimality_transport,
    admitted_orders_not_isomorphic⟩

end PermanssonResearch.Certification.Tranche10B02

/-! Complete named declaration and transitive-axiom receipt. -/

#check PermanssonResearch.GrammarRobust.BooleanEffects.and_singleton_margins_one
#check PermanssonResearch.GrammarRobust.BooleanEffects.xor_nonmonotone_margins
#check PermanssonResearch.GrammarRobust.BooleanMinimalityCases.and_action_minimal
#check PermanssonResearch.GrammarRobust.BooleanMinimalityCases.and_update_minimal
#check PermanssonResearch.GrammarRobust.BooleanMinimalityCases.and_joint_not_minimal
#check PermanssonResearch.GrammarRobust.B02ActualOriginalMarginFixture.two_actual_minimal_original_blocks
#check PermanssonResearch.GrammarRobust.B02ActualOriginalMarginFixture.and_joint_is_positive_but_not_minimal
#check PermanssonResearch.GrammarRobust.BooleanEffects.or_singleton_margins_zero
#check PermanssonResearch.GrammarRobust.BooleanEffects.or_joint_margin_one
#check PermanssonResearch.GrammarRobust.BooleanOneStepEvents.or_pathlaw_table
#check PermanssonResearch.GrammarRobust.BooleanOneStepEvents.and_pathlaw_table
#check PermanssonResearch.GrammarRobust.BooleanOneStepEvents.xor_pathlaw_table
#check PermanssonResearch.GrammarRobust.IsMinimalAllowed
#check PermanssonResearch.GrammarRobust.exists_minimal_allowed_subblock
#check PermanssonResearch.GrammarRobust.minimalPositive_iff_of_lowerSet_lifting
#check PermanssonResearch.GrammarRobust.exists_least_positive_of_finite_meet_closed
#check PermanssonResearch.GrammarRobust.Coarsening.original_margin_minimal_iff_of_lower_coverage
#check PermanssonResearch.GrammarRobust.FullRelabelingTransport.relabelEquiv_is_nonidentity
#check PermanssonResearch.GrammarRobust.FullRelabelingTransport.relabelEquiv_order_iff
#check PermanssonResearch.GrammarRobust.FullRelabelingTransport.relabeled_margin_all
#check PermanssonResearch.GrammarRobust.FullRelabelingTransport.relabeled_AND_minimal_iff
#check PermanssonResearch.GrammarRobust.B02ActualOriginalMarginFixture.nonidentity_relabeling_preserves_actual_margin
#check PermanssonResearch.GrammarRobust.B02ActualOriginalMarginFixture.actual_local_minimality_transport_not_global_identity
#check PermanssonResearch.GrammarRobust.B02LocalOriginalMarginClosure.fullOrEmptyFine
#check PermanssonResearch.GrammarRobust.B02LocalOriginalMarginClosure.actualCoarsening_not_global_injective
#check PermanssonResearch.GrammarRobust.B02LocalOriginalMarginClosure.actualCoarsening_lift_full
#check PermanssonResearch.GrammarRobust.B02LocalOriginalMarginClosure.actualCoarsening_lift_empty
#check PermanssonResearch.GrammarRobust.B02LocalOriginalMarginClosure.original_admitted_lower_coverage
#check PermanssonResearch.GrammarRobust.B02LocalOriginalMarginClosure.coarse_original_OR_positive
#check PermanssonResearch.GrammarRobust.B02LocalOriginalMarginClosure.coarse_original_OR_minimal
#check PermanssonResearch.GrammarRobust.B02LocalOriginalMarginClosure.original_local_minimality_without_global_isomorphism
#check PermanssonResearch.GrammarRobust.B02LocalOriginalMarginClosure.false_extra_admission_rejected
#check PermanssonResearch.GrammarRobust.B02ActualOriginalMarginFixture.actual_coarsening_does_not_preserve_minimality
#check PermanssonResearch.GrammarRobust.BooleanMinimalityCases.B7_minimality_not_preserved_by_refinement
#check PermanssonResearch.GrammarRobust.BooleanMinimalityCases.B8_coarse_hides_positive_fine_singleton
#check PermanssonResearch.GrammarRobust.LocalOrderPositiveFixture.folded_not_injective
#check PermanssonResearch.GrammarRobust.LocalOrderPositiveFixture.local_transport_under_noninjective_fold
#check PermanssonResearch.GrammarRobust.LocalOrderPositiveFixture.local_minimality_without_global_isomorphism
#check PermanssonResearch.Certification.Tranche10B02.singleton_blocks_incomparable
#check PermanssonResearch.Certification.Tranche10B02.two_incomparable_original_minima
#check PermanssonResearch.Certification.Tranche10B02.no_unique_original_minimal_block
#check PermanssonResearch.Certification.Tranche10B02.xor_joint_not_positive
#check PermanssonResearch.Certification.Tranche10B02.xor_positivity_not_upward_monotone
#check PermanssonResearch.Certification.Tranche10B02.xor_original_margin_not_monotone
#check PermanssonResearch.Certification.Tranche10B02.restrictedGrammar
#check PermanssonResearch.Certification.Tranche10B02.restrictedCoarsening
#check PermanssonResearch.Certification.Tranche10B02.restricted_component_map_identity
#check PermanssonResearch.Certification.Tranche10B02.restricted_lift_eq
#check PermanssonResearch.Certification.Tranche10B02.restricted_selected_allowed
#check PermanssonResearch.Certification.Tranche10B02.restricted_selected_is_proper
#check PermanssonResearch.Certification.Tranche10B02.restricted_local_lower_coverage
#check PermanssonResearch.Certification.Tranche10B02.restricted_original_margin_eq
#check PermanssonResearch.Certification.Tranche10B02.restrictedPositive
#check PermanssonResearch.Certification.Tranche10B02.restricted_selected_original_margin_one
#check PermanssonResearch.Certification.Tranche10B02.restricted_empty_not_positive
#check PermanssonResearch.Certification.Tranche10B02.restricted_original_minimal
#check PermanssonResearch.Certification.Tranche10B02.restricted_original_minimality_transport
#check PermanssonResearch.Certification.Tranche10B02.FineAdmitted
#check PermanssonResearch.Certification.Tranche10B02.RestrictedAdmitted
#check PermanssonResearch.Certification.Tranche10B02.admittedLift
#check PermanssonResearch.Certification.Tranche10B02.outside_block_admitted_and_uncovered
#check PermanssonResearch.Certification.Tranche10B02.admitted_lift_not_surjective
#check PermanssonResearch.Certification.Tranche10B02.restricted_admitted_chain
#check PermanssonResearch.Certification.Tranche10B02.admitted_orders_not_isomorphic
#check PermanssonResearch.Certification.Tranche10B02.positive_local_transport_without_admitted_order_isomorphism

#print axioms PermanssonResearch.GrammarRobust.BooleanEffects.and_singleton_margins_one
#print axioms PermanssonResearch.GrammarRobust.BooleanEffects.xor_nonmonotone_margins
#print axioms PermanssonResearch.GrammarRobust.BooleanMinimalityCases.and_action_minimal
#print axioms PermanssonResearch.GrammarRobust.BooleanMinimalityCases.and_update_minimal
#print axioms PermanssonResearch.GrammarRobust.BooleanMinimalityCases.and_joint_not_minimal
#print axioms PermanssonResearch.GrammarRobust.B02ActualOriginalMarginFixture.two_actual_minimal_original_blocks
#print axioms PermanssonResearch.GrammarRobust.B02ActualOriginalMarginFixture.and_joint_is_positive_but_not_minimal
#print axioms PermanssonResearch.GrammarRobust.BooleanEffects.or_singleton_margins_zero
#print axioms PermanssonResearch.GrammarRobust.BooleanEffects.or_joint_margin_one
#print axioms PermanssonResearch.GrammarRobust.BooleanOneStepEvents.or_pathlaw_table
#print axioms PermanssonResearch.GrammarRobust.BooleanOneStepEvents.and_pathlaw_table
#print axioms PermanssonResearch.GrammarRobust.BooleanOneStepEvents.xor_pathlaw_table
#print axioms PermanssonResearch.GrammarRobust.IsMinimalAllowed
#print axioms PermanssonResearch.GrammarRobust.exists_minimal_allowed_subblock
#print axioms PermanssonResearch.GrammarRobust.minimalPositive_iff_of_lowerSet_lifting
#print axioms PermanssonResearch.GrammarRobust.exists_least_positive_of_finite_meet_closed
#print axioms PermanssonResearch.GrammarRobust.Coarsening.original_margin_minimal_iff_of_lower_coverage
#print axioms PermanssonResearch.GrammarRobust.FullRelabelingTransport.relabelEquiv_is_nonidentity
#print axioms PermanssonResearch.GrammarRobust.FullRelabelingTransport.relabelEquiv_order_iff
#print axioms PermanssonResearch.GrammarRobust.FullRelabelingTransport.relabeled_margin_all
#print axioms PermanssonResearch.GrammarRobust.FullRelabelingTransport.relabeled_AND_minimal_iff
#print axioms PermanssonResearch.GrammarRobust.B02ActualOriginalMarginFixture.nonidentity_relabeling_preserves_actual_margin
#print axioms PermanssonResearch.GrammarRobust.B02ActualOriginalMarginFixture.actual_local_minimality_transport_not_global_identity
#print axioms PermanssonResearch.GrammarRobust.B02LocalOriginalMarginClosure.fullOrEmptyFine
#print axioms PermanssonResearch.GrammarRobust.B02LocalOriginalMarginClosure.actualCoarsening_not_global_injective
#print axioms PermanssonResearch.GrammarRobust.B02LocalOriginalMarginClosure.actualCoarsening_lift_full
#print axioms PermanssonResearch.GrammarRobust.B02LocalOriginalMarginClosure.actualCoarsening_lift_empty
#print axioms PermanssonResearch.GrammarRobust.B02LocalOriginalMarginClosure.original_admitted_lower_coverage
#print axioms PermanssonResearch.GrammarRobust.B02LocalOriginalMarginClosure.coarse_original_OR_positive
#print axioms PermanssonResearch.GrammarRobust.B02LocalOriginalMarginClosure.coarse_original_OR_minimal
#print axioms PermanssonResearch.GrammarRobust.B02LocalOriginalMarginClosure.original_local_minimality_without_global_isomorphism
#print axioms PermanssonResearch.GrammarRobust.B02LocalOriginalMarginClosure.false_extra_admission_rejected
#print axioms PermanssonResearch.GrammarRobust.B02ActualOriginalMarginFixture.actual_coarsening_does_not_preserve_minimality
#print axioms PermanssonResearch.GrammarRobust.BooleanMinimalityCases.B7_minimality_not_preserved_by_refinement
#print axioms PermanssonResearch.GrammarRobust.BooleanMinimalityCases.B8_coarse_hides_positive_fine_singleton
#print axioms PermanssonResearch.GrammarRobust.LocalOrderPositiveFixture.folded_not_injective
#print axioms PermanssonResearch.GrammarRobust.LocalOrderPositiveFixture.local_transport_under_noninjective_fold
#print axioms PermanssonResearch.GrammarRobust.LocalOrderPositiveFixture.local_minimality_without_global_isomorphism
#print axioms PermanssonResearch.Certification.Tranche10B02.singleton_blocks_incomparable
#print axioms PermanssonResearch.Certification.Tranche10B02.two_incomparable_original_minima
#print axioms PermanssonResearch.Certification.Tranche10B02.no_unique_original_minimal_block
#print axioms PermanssonResearch.Certification.Tranche10B02.xor_joint_not_positive
#print axioms PermanssonResearch.Certification.Tranche10B02.xor_positivity_not_upward_monotone
#print axioms PermanssonResearch.Certification.Tranche10B02.xor_original_margin_not_monotone
#print axioms PermanssonResearch.Certification.Tranche10B02.restrictedGrammar
#print axioms PermanssonResearch.Certification.Tranche10B02.restrictedCoarsening
#print axioms PermanssonResearch.Certification.Tranche10B02.restricted_component_map_identity
#print axioms PermanssonResearch.Certification.Tranche10B02.restricted_lift_eq
#print axioms PermanssonResearch.Certification.Tranche10B02.restricted_selected_allowed
#print axioms PermanssonResearch.Certification.Tranche10B02.restricted_selected_is_proper
#print axioms PermanssonResearch.Certification.Tranche10B02.restricted_local_lower_coverage
#print axioms PermanssonResearch.Certification.Tranche10B02.restricted_original_margin_eq
#print axioms PermanssonResearch.Certification.Tranche10B02.restrictedPositive
#print axioms PermanssonResearch.Certification.Tranche10B02.restricted_selected_original_margin_one
#print axioms PermanssonResearch.Certification.Tranche10B02.restricted_empty_not_positive
#print axioms PermanssonResearch.Certification.Tranche10B02.restricted_original_minimal
#print axioms PermanssonResearch.Certification.Tranche10B02.restricted_original_minimality_transport
#print axioms PermanssonResearch.Certification.Tranche10B02.FineAdmitted
#print axioms PermanssonResearch.Certification.Tranche10B02.RestrictedAdmitted
#print axioms PermanssonResearch.Certification.Tranche10B02.admittedLift
#print axioms PermanssonResearch.Certification.Tranche10B02.outside_block_admitted_and_uncovered
#print axioms PermanssonResearch.Certification.Tranche10B02.admitted_lift_not_surjective
#print axioms PermanssonResearch.Certification.Tranche10B02.restricted_admitted_chain
#print axioms PermanssonResearch.Certification.Tranche10B02.admitted_orders_not_isomorphic
#print axioms PermanssonResearch.Certification.Tranche10B02.positive_local_transport_without_admitted_order_isomorphism
