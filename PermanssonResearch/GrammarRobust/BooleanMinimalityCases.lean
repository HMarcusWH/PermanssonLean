import PermanssonResearch.GrammarRobust.BooleanEffects
import PermanssonResearch.GrammarRobust.EmptyBridge
import PermanssonResearch.GrammarRobust.ImageMinimality
import Mathlib.Tactic

/-!
# Lane B B1/B2/B3/B7/B8 — actual uniform-margin minimality countermodels

Every positive/zero test below is the original sInf constitutive margin
of a real typed Boolean α/P/U path-law intervention. A change in grammar
can preserve the complete process while changing its minimal explanatory
components. No monotonicity or uniqueness is assumed.
-/

open ProbabilityTheory MeasureTheory

namespace PermanssonResearch
namespace GrammarRobust
namespace BooleanMinimalityCases

open PermanssonLean PermanssonLean.RegimeSpecification
open BooleanModel BooleanBaseline BooleanDynamics BooleanPersistence
open BooleanOneStepEvents BooleanEffects

private theorem allowedBlock_eq_of_components_eq
    {IA IU C : Type*} [Fintype IA] [Fintype IU] [Fintype C]
    {Γ : PartitionGrammar IA IU C} (D E : AllowedBlock Γ)
    (h : D.components = E.components) : D = E := by
  cases D with
  | mk d hd =>
    cases E with
    | mk e he =>
      cases h
      rfl

noncomputable def fineBlock (D : Finset (Fin 2)) : AllowedBlock fine :=
  ⟨D, trivial⟩

noncomputable def coarseBlock (D : Finset (Fin 1)) : AllowedBlock coarse :=
  ⟨D, trivial⟩

def andPos (D : Finset (Fin 2)) : Prop :=
  IsUniformBlock baseline bank fine (fineBlock D) spec
    (propertyAtOne andP) comparison

def orPos (D : Finset (Fin 2)) : Prop :=
  IsUniformBlock baseline bank fine (fineBlock D) spec
    (propertyAtOne orP) comparison

def xorPos (D : Finset (Fin 2)) : Prop :=
  IsUniformBlock baseline bank fine (fineBlock D) spec
    (propertyAtOne xorP) comparison

/-- Empty is a literal baseline intervention for *every* frozen property,
so no finite comparison set can give it a positive constitutive margin. -/
theorem fine_empty_effect_zero
    (ψ : RegimePropertyMap Y ℝ) (y : Y) :
    blockEffect baseline bank fine (fineBlock ∅) ψ y = 0 := by
  unfold blockEffect constitutiveEffect
  change dist (ψ (pathProbability baseline (diracProba y)))
    (ψ (pathProbability
      (admittedBlockIntervention baseline bank fine (fineBlock ∅)).intervention.apply
      (diracProba y))) = 0
  rw [admittedBlockIntervention_apply]
  change dist (ψ (pathProbability baseline (diracProba y)))
    (ψ (pathProbability (blockModel baseline bank fine ∅) (diracProba y))) = 0
  rw [blockModel_empty]
  simp

theorem fine_empty_margin_zero (ψ : RegimePropertyMap Y ℝ) :
    blockMargin baseline bank fine (fineBlock ∅) spec ψ comparison = 0 := by
  apply blockMargin_eq_of_constant_effect
  intro y _
  exact fine_empty_effect_zero ψ y

theorem andPos_action : andPos ({0} : Finset (Fin 2)) := by
  change 0 < blockMargin baseline bank fine actionBlock spec
    (propertyAtOne andP) comparison
  rw [and_singleton_margins_one.1]
  norm_num

theorem andPos_update : andPos ({1} : Finset (Fin 2)) := by
  change 0 < blockMargin baseline bank fine updateBlock spec
    (propertyAtOne andP) comparison
  rw [and_singleton_margins_one.2]
  norm_num

theorem andPos_joint : andPos ({0,1} : Finset (Fin 2)) := by
  change 0 < blockMargin baseline bank fine jointBlock spec
    (propertyAtOne andP) comparison
  have h : blockMargin baseline bank fine jointBlock spec
      (propertyAtOne andP) comparison = 1 := by
    apply blockMargin_eq_of_constant_effect
    intro y _
    exact and_joint_one y
  rw [h]
  norm_num

theorem andPos_empty_false : ¬ andPos (∅ : Finset (Fin 2)) := by
  change ¬ (0 < blockMargin baseline bank fine (fineBlock ∅) spec
    (propertyAtOne andP) comparison)
  rw [fine_empty_margin_zero]
  norm_num

/-- B2: two genuinely incomparable minimal *constitutive* blocks. -/
theorem and_action_minimal :
    IsMinimalAllowed fine andPos ({0} : Finset (Fin 2)) := by
  refine ⟨trivial, andPos_action, ?_⟩
  intro E _ hproper hpositive
  have hE : E = ∅ := Finset.eq_empty_of_ssubset_singleton hproper
  exact andPos_empty_false (hE ▸ hpositive)

theorem and_update_minimal :
    IsMinimalAllowed fine andPos ({1} : Finset (Fin 2)) := by
  refine ⟨trivial, andPos_update, ?_⟩
  intro E _ hproper hpositive
  have hE : E = ∅ := Finset.eq_empty_of_ssubset_singleton hproper
  exact andPos_empty_false (hE ▸ hpositive)

theorem and_joint_not_minimal :
    ¬ IsMinimalAllowed fine andPos ({0,1} : Finset (Fin 2)) := by
  intro hmin
  exact hmin.2.2 ({0} : Finset (Fin 2)) trivial
    (by decide) andPos_action

/-- B1: singleton-null OR, but joint-positive OR. -/
theorem orPos_action_false : ¬ orPos ({0} : Finset (Fin 2)) := by
  change ¬ (0 < blockMargin baseline bank fine actionBlock spec
    (propertyAtOne orP) comparison)
  rw [or_singleton_margins_zero.1]
  norm_num

theorem orPos_update_false : ¬ orPos ({1} : Finset (Fin 2)) := by
  change ¬ (0 < blockMargin baseline bank fine updateBlock spec
    (propertyAtOne orP) comparison)
  rw [or_singleton_margins_zero.2]
  norm_num

theorem orPos_joint : orPos ({0,1} : Finset (Fin 2)) := by
  change 0 < blockMargin baseline bank fine jointBlock spec
    (propertyAtOne orP) comparison
  rw [or_joint_margin_one]
  norm_num

theorem orPos_empty_false : ¬ orPos (∅ : Finset (Fin 2)) := by
  change ¬ (0 < blockMargin baseline bank fine (fineBlock ∅) spec
    (propertyAtOne orP) comparison)
  rw [fine_empty_margin_zero]
  norm_num

/-- B1, strengthened: the joint-only positive block is *minimal* in
the actual finite admissible-subblock partial order. -/
theorem or_joint_minimal :
    IsMinimalAllowed fine orPos ({0,1} : Finset (Fin 2)) := by
  refine ⟨trivial, orPos_joint, ?_⟩
  intro E _ hproper hpositive
  classical
  by_cases h0 : (0 : Fin 2) ∈ E
  · by_cases h1 : (1 : Fin 2) ∈ E
    · have heq : E = ({0,1} : Finset (Fin 2)) := by
        ext i
        fin_cases i <;> simp [h0,h1]
      exact ((Finset.ssubset_iff_subset_ne.mp hproper).2 heq).elim
    · have heq : E = ({0} : Finset (Fin 2)) := by
        ext i
        fin_cases i <;> simp [h0,h1]
      exact orPos_action_false (heq ▸ hpositive)
  · by_cases h1 : (1 : Fin 2) ∈ E
    · have heq : E = ({1} : Finset (Fin 2)) := by
        ext i
        fin_cases i <;> simp [h0,h1]
      exact orPos_update_false (heq ▸ hpositive)
    · have heq : E = (∅ : Finset (Fin 2)) := by
        ext i
        fin_cases i <;> simp [h0,h1]
      exact orPos_empty_false (heq ▸ hpositive)

/-- A coarse component is genuinely compound: selecting it picks both fine
physical atoms. This is a NON-bijective component grammar matching. -/
theorem coarse_lift_joint :
    coarsening.lift ({0} : Finset (Fin 1)) =
      ({0,1} : Finset (Fin 2)) := by
  ext i
  fin_cases i <;> simp [Coarsening.lift, coarsening]

theorem coarse_margin_eq_fine_joint
    (ψ : RegimePropertyMap Y ℝ) :
    blockMargin baseline bank coarse (coarseBlock {0})
      spec ψ comparison =
    blockMargin baseline bank fine jointBlock spec ψ comparison := by
  have h := coarsening.blockMargin_lift_eq baseline bank
    (coarseBlock {0}) spec ψ comparison
  have hh : coarsening.liftAllowed (coarseBlock {0}) = jointBlock := by
    apply allowedBlock_eq_of_components_eq
    exact coarse_lift_joint
  rw [hh] at h
  exact h.symm

theorem coarse_empty_effect_zero (ψ : RegimePropertyMap Y ℝ) (y : Y) :
    blockEffect baseline bank coarse (coarseBlock ∅) ψ y = 0 := by
  unfold blockEffect constitutiveEffect
  change dist (ψ (pathProbability baseline (diracProba y)))
    (ψ (pathProbability
      (admittedBlockIntervention baseline bank coarse (coarseBlock ∅)).intervention.apply
      (diracProba y))) = 0
  rw [admittedBlockIntervention_apply]
  change dist (ψ (pathProbability baseline (diracProba y)))
    (ψ (pathProbability (blockModel baseline bank coarse ∅) (diracProba y))) = 0
  rw [blockModel_empty]
  simp

theorem coarse_empty_margin_zero (ψ : RegimePropertyMap Y ℝ) :
    blockMargin baseline bank coarse (coarseBlock ∅) spec ψ comparison = 0 := by
  apply blockMargin_eq_of_constant_effect
  intro y _
  exact coarse_empty_effect_zero ψ y

def coarseAndPos (D : Finset (Fin 1)) : Prop :=
  IsUniformBlock baseline bank coarse (coarseBlock D) spec
    (propertyAtOne andP) comparison

def coarseXorPos (D : Finset (Fin 1)) : Prop :=
  IsUniformBlock baseline bank coarse (coarseBlock D) spec
    (propertyAtOne xorP) comparison

theorem coarseAndPos_one : coarseAndPos ({0} : Finset (Fin 1)) := by
  change 0 < blockMargin baseline bank coarse (coarseBlock {0})
    spec (propertyAtOne andP) comparison
  rw [coarse_margin_eq_fine_joint]
  have h : blockMargin baseline bank fine jointBlock spec
      (propertyAtOne andP) comparison = 1 := by
    apply blockMargin_eq_of_constant_effect
    intro y _
    exact and_joint_one y
  rw [h]
  norm_num

theorem coarseAndPos_empty_false : ¬ coarseAndPos ∅ := by
  change ¬ (0 < blockMargin baseline bank coarse (coarseBlock ∅)
    spec (propertyAtOne andP) comparison)
  rw [coarse_empty_margin_zero]
  norm_num

/-- B7: same actual model is minimal as ONE coarse component, but
nonminimal as TWO fine components. Minimality is grammar-relative. -/
theorem coarse_and_is_minimal :
    IsMinimalAllowed coarse coarseAndPos ({0} : Finset (Fin 1)) := by
  refine ⟨trivial, coarseAndPos_one, ?_⟩
  intro E _ hproper hpositive
  have heq : E = ∅ := Finset.eq_empty_of_ssubset_singleton hproper
  exact coarseAndPos_empty_false (heq ▸ hpositive)

theorem B7_minimality_not_preserved_by_refinement :
    IsMinimalAllowed coarse coarseAndPos ({0} : Finset (Fin 1)) ∧
    ¬ IsMinimalAllowed fine andPos
      (coarsening.lift ({0} : Finset (Fin 1))) := by
  refine ⟨coarse_and_is_minimal, ?_⟩
  rw [coarse_lift_joint]
  exact and_joint_not_minimal

/-- B8: XOR cancellation: no positive coarse intervention exists for the
one-component grammar, even though each fine singleton is positive. -/
theorem coarseXorPos_one_false : ¬ coarseXorPos ({0} : Finset (Fin 1)) := by
  change ¬ (0 < blockMargin baseline bank coarse (coarseBlock {0})
    spec (propertyAtOne xorP) comparison)
  rw [coarse_margin_eq_fine_joint, xor_nonmonotone_margins.2]
  norm_num

theorem coarseXorPos_empty_false : ¬ coarseXorPos ∅ := by
  change ¬ (0 < blockMargin baseline bank coarse (coarseBlock ∅)
    spec (propertyAtOne xorP) comparison)
  rw [coarse_empty_margin_zero]
  norm_num

theorem xorPos_action : xorPos ({0} : Finset (Fin 2)) := by
  change 0 < blockMargin baseline bank fine actionBlock spec
    (propertyAtOne xorP) comparison
  rw [xor_nonmonotone_margins.1]
  norm_num

theorem B8_coarse_hides_positive_fine_singleton :
    xorPos ({0} : Finset (Fin 2)) ∧
    ¬ coarseXorPos ({0} : Finset (Fin 1)) := by
  exact ⟨xorPos_action, coarseXorPos_one_false⟩

end BooleanMinimalityCases
end GrammarRobust
end PermanssonResearch
