import PermanssonResearch.X1.ExactTerminalTables

/-!
# The six exact original X1 constitutive margins

Every lower bound ranges over the whole nine-state comparison region. The
minimum calculation uses the checked recurrence table and the original typed
path-law property bridge. It does not assert Exact GR for the leaking region.
-/

namespace PermanssonResearch.X1

set_option autoImplicit false
open PermanssonLean PermanssonLean.RegimeSpecification

instance componentFintype : Fintype Component where
  elems := {.action, .update, .joint}
  complete c := by cases c <;> simp

def componentFlags : Component → Bool × Bool
  | .action => (true, false)
  | .update => (false, true)
  | .joint => (true, true)

noncomputable def componentIntervention (m : Mode) : Component →
    AdmissibleStrategicIntervention (family m)
  | .action => Jaction m
  | .update => Jupdate m
  | .joint => Jjoint m

theorem componentIntervention_apply (m : Mode) (c : Component) :
    (componentIntervention m c).intervention.apply =
      protocolModel m (componentFlags c).1 (componentFlags c).2 := by
  cases c <;> rfl

def exactEffect (learner : Bool) (c : Component) (y : Y) : ℚ :=
  |InterventionNumerics.table learner (componentFlags c).1 (componentFlags c).2 3 y -
    InterventionNumerics.table learner false false 3 y|

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signed_effect_nonneg : ∀ (learner : Bool) (c : Component) (y : Y),
    y ∈ comparisonStarts →
      0 ≤ InterventionNumerics.table learner (componentFlags c).1 (componentFlags c).2 3 y -
        InterventionNumerics.table learner false false 3 y := by
  intro learner c y hy
  rcases y with ⟨q,x⟩
  have hx : x = true := hy
  subst x
  clear hy
  revert learner c q
  decide +kernel

/-- The 54 supplied effect candidates, checked against terminal values below. -/
def effectData : Bool → Component → Fin 9 → ℚ
  | false, .action => ![271/800, 271/800, 271/800, 271/800, 271/800, 271/800, 271/800, 271/800, 271/800]
  | false, .update => ![0, 0, 0, 0, 0, 0, 0, 0, 0]
  | false, .joint => ![271/800, 271/800, 271/800, 271/800, 271/800, 271/800, 271/800, 271/800, 271/800]
  | true, .action => ![3010663529/6400000000, 1342445531/2560000000, 284197969/512000000, 1342445531/2560000000, 16986541/32000000, 2886717043/5120000000, 284197969/512000000, 2886717043/5120000000, 15243920951/25600000000]
  | true, .update => ![504938529/6400000000, 240750531/2560000000, 43977969/512000000, 240750531/2560000000, 1972791/32000000, 285707043/5120000000, 43977969/512000000, 285707043/5120000000, 1244820951/25600000000]
  | true, .joint => ![3010663529/6400000000, 1342445531/2560000000, 284197969/512000000, 1342445531/2560000000, 16986541/32000000, 2886717043/5120000000, 284197969/512000000, 2886717043/5120000000, 15243920951/25600000000]

def candidateEffect (learner : Bool) (c : Component) (q : Memory) : ℚ :=
  effectData learner c ⟨3 * q.1.val + q.2.val, by
    have h₁ := q.1.isLt
    have h₂ := q.2.isLt
    omega⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem effects_eq_candidates : ∀ (learner : Bool) (c : Component) (q : Memory),
    exactEffect learner c (q,true) = candidateEffect learner c q := by
  decide +kernel

theorem finiteEffect_eq_exactEffect (m : Mode) (c : Component) (y : Y) :
    finiteEffect m (componentIntervention m c) y = (exactEffect (learnerFlag m) c y : ℝ) := by
  rw [← constitutiveEffect_eq_finiteEffect]
  unfold constitutiveEffect
  change dist (baselinePropertyValue property (model m) y)
    (baselinePropertyValue property (componentIntervention m c).intervention.apply y) = _
  rw [componentIntervention_apply]
  change dist (baselinePropertyValue property (protocolModel m false false) y) _ = _
  rw [original_property_eq_table, original_property_eq_table, Real.dist_eq, abs_sub_comm]
  simp only [exactEffect, Rat.cast_abs, Rat.cast_sub]

def exactMargin : Bool → Component → ℚ
  | false, .action => 271 / 800
  | false, .update => 0
  | false, .joint => 271 / 800
  | true, .action => 3010663529 / 6400000000
  | true, .update => 1244820951 / 25600000000
  | true, .joint => 3010663529 / 6400000000

def attainingStart (learner : Bool) (c : Component) : Y :=
  if learner then
    if c = .update then ((2,2),true) else ((0,0),true)
  else y0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exactEffect_lower : ∀ (learner : Bool) (c : Component) (y : Y),
    y ∈ comparisonStarts → exactMargin learner c ≤ exactEffect learner c y := by
  intro learner c y hy
  rcases y with ⟨q,x⟩
  have hx : x = true := hy
  subst x
  clear hy
  revert learner c q
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exactEffect_attained : ∀ (learner : Bool) (c : Component),
    exactEffect learner c (attainingStart learner c) = exactMargin learner c := by
  decide +kernel

theorem attainingStart_mem (learner : Bool) (c : Component) :
    attainingStart learner c ∈ comparisonStarts := by
  cases learner <;> cases c <;> rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
/-- Every equilibrium start ties; the learner attaining starts are unique. -/
theorem exactEffect_attainers : ∀ (learner : Bool) (c : Component) (y : Y),
    y ∈ comparisonStarts →
      (exactEffect learner c y = exactMargin learner c ↔
        learner = false ∨ y = attainingStart learner c) := by
  intro learner c y hy
  rcases y with ⟨q,x⟩
  have hx : x = true := hy
  subst x
  clear hy
  revert learner c q
  decide +kernel

theorem component_original_margin (m : Mode) (c : Component) :
    constitutiveMargin (model m) (specification m) (family m) property (comparisonSet m)
      (componentIntervention m c) = (exactMargin (learnerFlag m) c : ℝ) := by
  rw [constitutiveMargin_eq_finiteInf]
  have hlow (y : Y) (hy : y ∈ comparisonStarts) :
      (exactMargin (learnerFlag m) c : ℝ) ≤ finiteEffect m (componentIntervention m c) y := by
    rw [finiteEffect_eq_exactEffect]
    exact_mod_cast exactEffect_lower (learnerFlag m) c y hy
  have hatt : finiteEffect m (componentIntervention m c) (attainingStart (learnerFlag m) c) =
      (exactMargin (learnerFlag m) c : ℝ) := by
    rw [finiteEffect_eq_exactEffect, exactEffect_attained]
  apply le_antisymm
  · rw [← hatt]
    apply csInf_le
    · refine ⟨(exactMargin (learnerFlag m) c : ℝ), ?_⟩
      rintro v ⟨y,hy,rfl⟩
      exact hlow y hy
    · exact ⟨attainingStart (learnerFlag m) c, attainingStart_mem (learnerFlag m) c, rfl⟩
  · apply le_csInf
    · exact ⟨finiteEffect m (componentIntervention m c) (attainingStart (learnerFlag m) c),
        attainingStart (learnerFlag m) c, attainingStart_mem (learnerFlag m) c, rfl⟩
    · rintro v ⟨y,hy,rfl⟩
      exact hlow y hy

theorem equilibrium_action_margin :
    constitutiveMargin (model .equilibrium) (specification .equilibrium) (family .equilibrium)
      property (comparisonSet .equilibrium) (Jaction .equilibrium) =
        ((271 / 800 : ℚ) : ℝ) :=
  component_original_margin .equilibrium .action

theorem equilibrium_update_margin :
    constitutiveMargin (model .equilibrium) (specification .equilibrium) (family .equilibrium)
      property (comparisonSet .equilibrium) (Jupdate .equilibrium) = ((0 : ℚ) : ℝ) :=
  component_original_margin .equilibrium .update

theorem equilibrium_joint_margin :
    constitutiveMargin (model .equilibrium) (specification .equilibrium) (family .equilibrium)
      property (comparisonSet .equilibrium) (Jjoint .equilibrium) =
        ((271 / 800 : ℚ) : ℝ) :=
  component_original_margin .equilibrium .joint

theorem learner_action_margin :
    constitutiveMargin (model .learner) (specification .learner) (family .learner)
      property (comparisonSet .learner) (Jaction .learner) =
        ((3010663529 / 6400000000 : ℚ) : ℝ) :=
  component_original_margin .learner .action

theorem learner_update_margin :
    constitutiveMargin (model .learner) (specification .learner) (family .learner)
      property (comparisonSet .learner) (Jupdate .learner) =
        ((1244820951 / 25600000000 : ℚ) : ℝ) :=
  component_original_margin .learner .update

theorem learner_joint_margin :
    constitutiveMargin (model .learner) (specification .learner) (family .learner)
      property (comparisonSet .learner) (Jjoint .learner) =
        ((3010663529 / 6400000000 : ℚ) : ℝ) :=
  component_original_margin .learner .joint

end PermanssonResearch.X1
