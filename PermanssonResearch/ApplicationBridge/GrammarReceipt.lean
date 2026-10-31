import PermanssonResearch.ApplicationBridge.QuotientReceipt
import Mathlib.Tactic

/-!
# ApplicationBridge — admitted patch-grammar receipts

A grammar receipt lists declared α/U patches, the explicitly admitted blocks
(sets of patches; no downward closure), and for every admitted block the
exact finite-horizon survival (or exit) values of its treated model on the
comparison states, the effects against the baseline, the inclusion-minimal
blocks whose effect is positive on the whole comparison set, and four-corner
interactions `v(a ∪ u) - v(a) - v(u) + v(∅)`.

`GrammarChecks` decides all of these from the block matrices, the block
component sets and the reported tables; soundness identifies every value
with an actual path-law probability of the block's realized chain and the
minimal positive set and interactions with the corresponding statements
about those probabilities. Which treated model a block denotes (baseline
plus exactly its patch rows, P held fixed) is proved per instance. A
positive finite effect is not a constitutive or PR certificate.
-/

open MeasureTheory

namespace PermanssonResearch.ApplicationBridge.GrammarReceipt

open PermanssonResearch.ReverseSolver
open PermanssonResearch.ReverseSolver.FiniteStrategicRealization
open PermanssonResearch.ApplicationBridge.MenuReceipt
open PermanssonResearch.ApplicationBridge.ExitReceipt
open PermanssonResearch.ApplicationBridge.QuotientReceipt

set_option autoImplicit false

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

variable {n k c : ℕ}

/-- The effect of block `i` is positive at every comparison state. -/
def PositiveBlock (values : Fin k → Fin n → ℚ) (baseValues : Fin n → ℚ)
    (comparison : Finset (Fin n)) (i : Fin k) : Prop :=
  ∀ x ∈ comparison, baseValues x < values i x

instance (values : Fin k → Fin n → ℚ) (baseValues : Fin n → ℚ)
    (comparison : Finset (Fin n)) (i : Fin k) :
    Decidable (PositiveBlock values baseValues comparison i) := by
  unfold PositiveBlock
  infer_instance

/-- Four-corner index tuple: blocks `∅`, `{a}`, `{u}`, `{a, u}`. -/
structure Corner (k c : ℕ) where
  none : Fin k
  onlyA : Fin k
  onlyU : Fin k
  joint : Fin k
  a : Fin c
  u : Fin c

def GrammarChecks (base : RationalMarkovMatrix n) (members : Fin k → RationalMarkovMatrix n)
    (blocks : Fin k → Finset (Fin c)) (region : Finset (Fin n)) (horizon : ℕ)
    (survival : Bool) (comparison : Finset (Fin n)) (baseValues : Fin n → ℚ)
    (values : Fin k → Fin n → ℚ) (minimal : Finset (Fin k))
    (corners : List (Corner k c)) (interactions : ℕ → Fin n → ℚ) : Prop :=
  (∀ x ∈ comparison, baseValues x = menuObjective survival base region horizon x) ∧
  (∀ i, ∀ x ∈ comparison, values i x = menuObjective survival (members i) region horizon x) ∧
  (∀ i, i ∈ minimal ↔ (PositiveBlock values baseValues comparison i ∧
      ∀ j, blocks j ⊂ blocks i → ¬ PositiveBlock values baseValues comparison j)) ∧
  (∀ r : Fin corners.length,
    blocks corners[r].none = ∅ ∧ blocks corners[r].onlyA = {corners[r].a} ∧
    blocks corners[r].onlyU = {corners[r].u} ∧
    blocks corners[r].joint = {corners[r].a, corners[r].u} ∧
    ∀ x ∈ comparison, interactions r x =
      values corners[r].joint x - values corners[r].onlyA x - values corners[r].onlyU x +
        values corners[r].none x)

instance (base : RationalMarkovMatrix n) (members : Fin k → RationalMarkovMatrix n)
    (blocks : Fin k → Finset (Fin c)) (region : Finset (Fin n)) (horizon : ℕ)
    (survival : Bool) (comparison : Finset (Fin n)) (baseValues : Fin n → ℚ)
    (values : Fin k → Fin n → ℚ) (minimal : Finset (Fin k))
    (corners : List (Corner k c)) (interactions : ℕ → Fin n → ℚ) :
    Decidable (GrammarChecks base members blocks region horizon survival comparison baseValues
      values minimal corners interactions) := by
  unfold GrammarChecks
  infer_instance

def checkAdmittedBlocks (base : RationalMarkovMatrix n) (members : Fin k → RationalMarkovMatrix n)
    (blocks : Fin k → Finset (Fin c)) (region : Finset (Fin n)) (horizon : ℕ)
    (survival : Bool) (comparison : Finset (Fin n)) (baseValues : Fin n → ℚ)
    (values : Fin k → Fin n → ℚ) (minimal : Finset (Fin k))
    (corners : List (Corner k c)) (interactions : ℕ → Fin n → ℚ) : Bool :=
  decide (GrammarChecks base members blocks region horizon survival comparison baseValues
    values minimal corners interactions)

theorem checkAdmittedBlocks_sound (base : RationalMarkovMatrix n)
    (members : Fin k → RationalMarkovMatrix n)
    (blocks : Fin k → Finset (Fin c)) (region : Finset (Fin n)) (horizon : ℕ)
    (survival : Bool) (comparison : Finset (Fin n)) (baseValues : Fin n → ℚ)
    (values : Fin k → Fin n → ℚ) (minimal : Finset (Fin k))
    (corners : List (Corner k c)) (interactions : ℕ → Fin n → ℚ)
    (h : checkAdmittedBlocks base members blocks region horizon survival comparison baseValues
      values minimal corners interactions = true) :
    GrammarChecks base members blocks region horizon survival comparison baseValues
      values minimal corners interactions := by
  unfold checkAdmittedBlocks at h
  exact of_decide_eq_true h

/-- The survival (or exit) objective of a realized chain from `x`. -/
noncomputable def actualObjective (M : RationalMarkovMatrix n) (region : Finset (Fin n))
    (horizon : ℕ) (survival : Bool) (x : Fin n) : ℝ :=
  if survival then
    ((realizedModel M).pathLaw (Measure.dirac (decode x))).real (staysThrough region horizon)
  else
    1 - ((realizedModel M).pathLaw (Measure.dirac (decode x))).real (staysThrough region horizon)

section Receipt

variable (base : RationalMarkovMatrix n) (members : Fin k → RationalMarkovMatrix n)
  (blocks : Fin k → Finset (Fin c)) (region : Finset (Fin n)) (horizon : ℕ)
  (survival : Bool) (comparison : Finset (Fin n)) (baseValues : Fin n → ℚ)
  (values : Fin k → Fin n → ℚ) (minimal : Finset (Fin k))
  (corners : List (Corner k c)) (interactions : ℕ → Fin n → ℚ)
  (h : checkAdmittedBlocks base members blocks region horizon survival comparison baseValues
    values minimal corners interactions = true)
include h

theorem checked_base_value_actual (x : Fin n) (hx : x ∈ comparison) :
    (baseValues x : ℝ) = actualObjective base region horizon survival x := by
  rw [(checkAdmittedBlocks_sound base members blocks region horizon survival comparison
    baseValues values minimal corners interactions h).1 x hx, menuObjective_actual]
  rfl

theorem checked_block_value_actual (i : Fin k) (x : Fin n) (hx : x ∈ comparison) :
    (values i x : ℝ) = actualObjective (members i) region horizon survival x := by
  rw [(checkAdmittedBlocks_sound base members blocks region horizon survival comparison
    baseValues values minimal corners interactions h).2.1 i x hx, menuObjective_actual]
  rfl

/-- Positivity of a block's checked effect is positivity of its actual effect. -/
theorem positive_iff_actual (i : Fin k) :
    PositiveBlock values baseValues comparison i ↔
      ∀ x ∈ comparison, actualObjective base region horizon survival x <
        actualObjective (members i) region horizon survival x := by
  unfold PositiveBlock
  constructor
  · intro hp x hx
    rw [← checked_base_value_actual base members blocks region horizon survival comparison
      baseValues values minimal corners interactions h x hx,
      ← checked_block_value_actual base members blocks region horizon survival comparison
      baseValues values minimal corners interactions h i x hx]
    exact_mod_cast hp x hx
  · intro hp x hx
    have := hp x hx
    rw [← checked_base_value_actual base members blocks region horizon survival comparison
      baseValues values minimal corners interactions h x hx,
      ← checked_block_value_actual base members blocks region horizon survival comparison
      baseValues values minimal corners interactions h i x hx] at this
    exact_mod_cast this

/-- The checked minimal set is exactly the admitted blocks whose actual
    effect is positive on the whole comparison set and that contain no
    strictly smaller admitted block with that property. -/
theorem checked_minimal_positive_blocks (i : Fin k) :
    i ∈ minimal ↔
      ((∀ x ∈ comparison, actualObjective base region horizon survival x <
          actualObjective (members i) region horizon survival x) ∧
        ∀ j, blocks j ⊂ blocks i →
          ¬ ∀ x ∈ comparison, actualObjective base region horizon survival x <
            actualObjective (members j) region horizon survival x) := by
  rw [(checkAdmittedBlocks_sound base members blocks region horizon survival comparison
    baseValues values minimal corners interactions h).2.2.1 i]
  simp only [positive_iff_actual base members blocks region horizon survival comparison
    baseValues values minimal corners interactions h]

/-- Every checked four-corner interaction is the actual interaction. -/
theorem checked_four_corner_effects (r : Fin corners.length) (x : Fin n) (hx : x ∈ comparison) :
    (interactions r x : ℝ) =
      actualObjective (members corners[r].joint) region horizon survival x -
        actualObjective (members corners[r].onlyA) region horizon survival x -
        actualObjective (members corners[r].onlyU) region horizon survival x +
        actualObjective (members corners[r].none) region horizon survival x := by
  have hr := ((checkAdmittedBlocks_sound base members blocks region horizon survival comparison
    baseValues values minimal corners interactions h).2.2.2 r).2.2.2.2 x hx
  rw [hr]
  push_cast
  rw [checked_block_value_actual base members blocks region horizon survival comparison
      baseValues values minimal corners interactions h _ x hx,
    checked_block_value_actual base members blocks region horizon survival comparison
      baseValues values minimal corners interactions h _ x hx,
    checked_block_value_actual base members blocks region horizon survival comparison
      baseValues values minimal corners interactions h _ x hx,
    checked_block_value_actual base members blocks region horizon survival comparison
      baseValues values minimal corners interactions h _ x hx]

end Receipt

end PermanssonResearch.ApplicationBridge.GrammarReceipt
