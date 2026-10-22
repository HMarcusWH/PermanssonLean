import PermanssonResearch.Quotient.DiscountedCanonicalMarginClosure
import PermanssonResearch.X1.TypedModels
import PermanssonResearch.ConstitutiveQuasi.ComparisonTransport
import Mathlib.Tactic

/-!
# Q-05 typed finite source witness (not the final original-margin certificate)
Genuine alpha -> P -> U models with fixed physical transition P.
The exact rational score calculations are a separate finite calculation;
PointWitness, full canonical paths and original comparison-set margin remain
additional required obligations before full Q-05 acceptance.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch.Quotient.Q05ActualOriginalMarginWitnessFixture
open PermanssonLean
open PermanssonResearch.X1 (coin coin_probability)
set_option autoImplicit false

abbrev FineState := JointState Bool Bool
abbrev CoarseState := JointState Unit Bool

def fineActionRate (treated strategic : Bool) : ℚ :=
  if treated then (if strategic then 4/5 else 7/10)
  else (if strategic then 1/5 else 1/10)

def coarseActionRate (treated : Bool) : ℚ :=
  if treated then 3/4 else 3/20

theorem fineActionRate_bounds (t s : Bool) :
    0 ≤ fineActionRate t s ∧ fineActionRate t s ≤ 1 := by
  cases t <;> cases s <;> norm_num [fineActionRate]

theorem coarseActionRate_bounds (t : Bool) :
    0 ≤ coarseActionRate t ∧ coarseActionRate t ≤ 1 := by
  cases t <;> norm_num [coarseActionRate]

noncomputable def fineAction (t : Bool) : Kernel FineState Bool where
  toFun y := coin (fineActionRate t y.1)
  measurable' := Measurable.of_discrete

instance fineAction_isMarkov (t : Bool) : IsMarkovKernel (fineAction t) :=
  ⟨fun y => coin_probability _ (fineActionRate_bounds t y.1)⟩

noncomputable def coarseAction (t : Bool) : Kernel CoarseState Bool where
  toFun _ := coin (coarseActionRate t)
  measurable' := Measurable.of_discrete

instance coarseAction_isMarkov (t : Bool) : IsMarkovKernel (coarseAction t) :=
  ⟨fun _ => coin_probability _ (coarseActionRate_bounds t)⟩

noncomputable def fineWorld : Kernel (WorldInput Bool Bool Bool) Bool :=
  Kernel.deterministic (fun z => z.2) Measurable.of_discrete

noncomputable def coarseWorld : Kernel (WorldInput Unit Bool Bool) Bool :=
  Kernel.deterministic (fun z => z.2) Measurable.of_discrete

noncomputable def fineUpdate (t : Bool) :
    Kernel (UpdateInput Bool Bool Bool) Bool :=
  Kernel.deterministic (fun _ => t) Measurable.of_discrete

noncomputable def coarseUpdate :
    Kernel (UpdateInput Unit Bool Bool) Unit :=
  Kernel.deterministic (fun _ => ()) Measurable.of_discrete

noncomputable def fineModel (t : Bool) : StrategicWorldModel Bool Bool Bool where
  generator := {
    action := fineAction t
    update := fineUpdate t
    action_isMarkov := inferInstance
    update_isMarkov := by unfold fineUpdate; infer_instance
  }
  world := fineWorld
  world_isMarkov := by unfold fineWorld; infer_instance

noncomputable def coarseModel (t : Bool) : StrategicWorldModel Unit Bool Bool where
  generator := {
    action := coarseAction t
    update := coarseUpdate
    action_isMarkov := inferInstance
    update_isMarkov := by unfold coarseUpdate; infer_instance
  }
  world := coarseWorld
  world_isMarkov := by unfold coarseWorld; infer_instance

theorem fine_world_fixed : (fineModel false).world = (fineModel true).world := rfl
theorem coarse_world_fixed : (coarseModel false).world = (coarseModel true).world := rfl

def compression : TypeRespectingStateCompression Bool Bool Unit Bool where
  strategic := fun _ => ()
  world := id
  strategic_measurable := Measurable.of_discrete
  world_measurable := measurable_id
  strategic_surjective := by
    intro z
    exact ⟨false, by cases z; rfl⟩
  world_surjective := Function.surjective_id

/-- Frozen admitted joint strategic intervention, not a model-swapping label. -/
inductive FamilyComponent | joint

noncomputable def fineFamily :
    InterventionFamily (fineModel false) FamilyComponent where
  targetOf
    | .joint => .jointStrategic
  admissible
    | .joint, r => r = (fineModel true).generator

noncomputable def coarseFamily :
    InterventionFamily (coarseModel false) FamilyComponent where
  targetOf
    | .joint => .jointStrategic
  admissible
    | .joint, r => r = (coarseModel true).generator

noncomputable def fineJ : AdmissibleStrategicIntervention fineFamily where
  intervention := ⟨.joint, (fineModel true).generator⟩
  accepted := rfl
  strategic := InterventionTarget.isStrategic_jointStrategic

noncomputable def coarseJ : AdmissibleStrategicIntervention coarseFamily where
  intervention := ⟨.joint, (coarseModel true).generator⟩
  accepted := rfl
  strategic := InterventionTarget.isStrategic_jointStrategic

/-- This is the actual intervention grammar's world preservation lemma. -/
theorem admitted_fine_world_fixed :
    fineJ.intervention.apply.world = (fineModel false).world := fineJ.world_eq

theorem admitted_coarse_world_fixed :
    coarseJ.intervention.apply.world = (coarseModel false).world := coarseJ.world_eq

/-- The original predeclared two-state comparison domain, not one random
singleton path law. A genuine full ConstitutiveComparisonSet must additionally
carry a chosen regime specification and the corresponding source law. -/
def twoStartDomain : Set FineState := {(false, false), (false, true)}

theorem twoStartDomain_contains_both :
    (false, false) ∈ twoStartDomain ∧
    (false, true) ∈ twoStartDomain := by
  simp [twoStartDomain]

theorem twoStartDomain_has_distinct_starts :
    (false, false) ≠ (false, true) := by decide

/-- Frozen original source regime specification: no parameter is optimized
after the witness is calculated. All finite states are declared in the basin.
This does NOT assert Exact GR. -/
noncomputable def fineSpec : RegimeSpecification FineState Bool where
  region := Set.univ
  region_measurable := MeasurableSet.univ
  basin := Set.univ
  basin_measurable := MeasurableSet.univ
  basin_subset_region := Set.Subset.rfl
  descriptor := Prod.snd
  descriptor_measurable := measurable_snd
  target := ⟨coin (1/2), coin_probability _ (by constructor <;> norm_num)⟩
  convergenceMode := ConvergenceMode.almostSureWeak FineState Bool

noncomputable def coarseSpec : RegimeSpecification CoarseState Bool where
  region := Set.univ
  region_measurable := MeasurableSet.univ
  basin := Set.univ
  basin_measurable := MeasurableSet.univ
  basin_subset_region := Set.Subset.rfl
  descriptor := Prod.snd
  descriptor_measurable := measurable_snd
  target := ⟨coin (1/2), coin_probability _ (by constructor <;> norm_num)⟩
  convergenceMode := ConvergenceMode.almostSureWeak CoarseState Bool

/-- The original B₁ object has TWO distinct baseline point-started
whole-path laws. Randomness in one point-started law is not substituted for
the required nontriviality premise. -/
noncomputable def fineComparisonSet :
    RegimeSpecification.ConstitutiveComparisonSet (fineModel false) fineSpec where
  states := twoStartDomain
  states_measurable := MeasurableSet.of_discrete
  states_subset_basin := by intro y hy; trivial
  pathLawNontrivial := by
    refine ⟨(false, false), ?_, (false, true), ?_, ?_⟩
    · simp [twoStartDomain]
    · simp [twoStartDomain]
    · exact PermanssonResearch.ConstitutiveQuasi.pointStarted_pathLaw_ne_of_ne
        (fineModel false) (by decide)

noncomputable def coarseComparisonSet :
    RegimeSpecification.ConstitutiveComparisonSet (coarseModel false) coarseSpec where
  states := Set.univ
  states_measurable := MeasurableSet.univ
  states_subset_basin := by intro y hy; trivial
  pathLawNontrivial := by
    refine ⟨((), false), Set.mem_univ _, ((), true), Set.mem_univ _, ?_⟩
    exact PermanssonResearch.ConstitutiveQuasi.pointStarted_pathLaw_ne_of_ne
      (coarseModel false) (by decide)

/-- The *entire* original two-start domain maps to the coarse domain.
No post-hoc smaller comparison subset or weaker surrogate margin. -/
theorem entire_original_comparison_domain :
    coarseComparisonSet.states =
      compression.stateMap '' fineComparisonSet.states := by
  change Set.univ = compression.stateMap '' twoStartDomain
  ext z
  constructor
  · intro _
    refine ⟨(false, z.2), ?_, ?_⟩
    · cases z.2 <;> simp [twoStartDomain]
    · cases z.1; rfl
  · intro _
    exact Set.mem_univ _

theorem compression_preserves_world (y : FineState) :
    (compression.stateMap y).2 = y.2 := rfl

theorem compression_collapses_distinct_states :
    compression.stateMap (false, true) =
      compression.stateMap (true, true) ∧
    (false, true) ≠ (true, true) := by
  constructor
  · rfl
  · decide

theorem compression_noninjective :
    ¬ Function.Injective compression.stateMap := by
  intro h
  have eqmap : compression.stateMap (false, true) =
      compression.stateMap (true, true) := rfl
  have heq := h eqmap
  have impossible : (false : Bool) = true := congrArg Prod.fst heq
  simp at impossible

def fineDiscountedOutput (treated s x : Bool) : ℚ :=
  (2/3 : ℚ) * (if x then 1 else 0) +
  (2/9 : ℚ) * fineActionRate treated s +
  (1/9 : ℚ) * fineActionRate treated treated

def coarseDiscountedOutput (treated x : Bool) : ℚ :=
  (2/3 : ℚ) * (if x then 1 else 0) +
  (1/3 : ℚ) * coarseActionRate treated

def fineOriginalEffect (x : Bool) : ℚ :=
  fineDiscountedOutput true false x - fineDiscountedOutput false false x

def coarseOriginalEffect (x : Bool) : ℚ :=
  coarseDiscountedOutput true x - coarseDiscountedOutput false x

theorem exact_four_outputs_false :
    fineDiscountedOutput false false false = 1/30 ∧
    fineDiscountedOutput true false false = 11/45 ∧
    coarseDiscountedOutput false false = 1/20 ∧
    coarseDiscountedOutput true false = 1/4 := by
  norm_num [fineDiscountedOutput, fineActionRate,
    coarseDiscountedOutput, coarseActionRate]

theorem exact_four_outputs_true :
    fineDiscountedOutput false false true = 7/10 ∧
    fineDiscountedOutput true false true = 41/45 ∧
    coarseDiscountedOutput false true = 43/60 ∧
    coarseDiscountedOutput true true = 11/12 := by
  norm_num [fineDiscountedOutput, fineActionRate,
    coarseDiscountedOutput, coarseActionRate]

theorem actual_two_start_effects (x : Bool) :
    fineOriginalEffect x = (19/90 : ℚ) ∧
    coarseOriginalEffect x = (1/5 : ℚ) := by
  cases x <;> norm_num [fineOriginalEffect, coarseOriginalEffect,
    fineDiscountedOutput, coarseDiscountedOutput,
    fineActionRate, coarseActionRate]

theorem exact_margin_gap (x : Bool) :
    |fineOriginalEffect x - coarseOriginalEffect x| = (1/90 : ℚ) := by
  cases x <;> norm_num [fineOriginalEffect, coarseOriginalEffect,
    fineDiscountedOutput, coarseDiscountedOutput,
    fineActionRate, coarseActionRate]

def commonMass (p q : ℚ) : ℚ :=
  min p q + min (1-p) (1-q)

theorem both_sides_every_strategic_row (t s : Bool) :
    commonMass (fineActionRate t s) (coarseActionRate t) = 19/20 := by
  cases t <;> cases s <;>
    norm_num [commonMass, fineActionRate, coarseActionRate, min_def]

theorem discounted_defect_budget :
    ((1/3 : ℚ) * (1/20) / (1-(1/3)+(1/3)*(1/20))) = 1/41 := by
  norm_num

theorem two_sided_original_margin_bound (x : Bool) :
    |fineOriginalEffect x - coarseOriginalEffect x| ≤ (2/41 : ℚ) := by
  cases x <;> norm_num [fineOriginalEffect, coarseOriginalEffect,
    fineDiscountedOutput, coarseDiscountedOutput,
    fineActionRate, coarseActionRate]

theorem positive_gap_survives_budget :
    (0 : ℚ) < 19/90 - 2/41 := by norm_num

theorem treatment_reaches_other_strategic_state :
    (false : Bool) ≠ true ∧
    fineActionRate true true ≠ coarseActionRate true := by
  norm_num [fineActionRate, coarseActionRate]

end PermanssonResearch.Quotient.Q05ActualOriginalMarginWitnessFixture
