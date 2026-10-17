import Mathlib.Tactic

/-!+# X1: frozen rational commons instance

The parameter choice is the committed handover candidate. Economic labels are
interpretations of this mathematical example, not empirical identification.
Both typed models and both players' incentive certificates use these SAME
world probabilities and rewards.
-/

namespace PermanssonResearch.X1

set_option autoImplicit false

abbrev Memory := Fin 3 × Fin 3
abbrev Action := Bool × Bool
abbrev Y := Memory × Bool
abbrev Player := Fin 2

theorem sum_bool {α : Type*} [AddCommMonoid α] (f : Bool → α) :
    (∑ b : Bool, f b) = f false + f true := by
  rw [show (Finset.univ : Finset Bool) = {false, true} by decide]
  simp

def indicator (b : Bool) : ℚ := if b then 1 else 0
def discount : ℚ := 9 / 10
def congestion : ℚ := 193 / 211
def depletionCost : ℚ := 1 / 10

/-- Literal clipped world probability (V20.35a), shared by E and L. -/
def pRep (x : Bool) (a : Action) : ℚ :=
  min 1 (max 0 ((if x then 9 / 10 else 1 / 4) -
    (1 / 4) * (indicator a.1 + indicator a.2)))

theorem pRep_bounds (x : Bool) (a : Action) : 0 ≤ pRep x a ∧ pRep x a ≤ 1 := by
  rcases a with ⟨a, b⟩
  cases x <;> cases a <;> cases b <;> norm_num [pRep, indicator]

def ownAction (i : Player) (a : Action) : Bool := if i = 0 then a.1 else a.2
def otherAction (i : Player) (a : Action) : Bool := if i = 0 then a.2 else a.1
def deviationAction (i : Player) (own other : Bool) : Action :=
  if i = 0 then (own, other) else (other, own)

/-- Player-indexed reward; neither player's incentive is left to a symmetry comment. -/
def reward (i : Player) (x : Bool) (a : Action) : ℚ :=
  (if x then 1 / 2 else 0) * indicator (ownAction i a) -
    congestion * indicator (ownAction i a) * indicator (otherAction i a) -
    depletionCost * (1 - indicator x)

def piExtract (x : Bool) : ℚ := if x then 1 / 2 else 0
def boolMass (p : ℚ) (b : Bool) : ℚ := if b then p else 1 - p
def piAction (x a : Bool) : ℚ := boolMass (piExtract x) a
def value (_i : Player) (x : Bool) : ℚ := if x then -81 / 211 else -121 / 211

theorem piExtract_bounds (x : Bool) : 0 ≤ piExtract x ∧ piExtract x ≤ 1 := by
  cases x <;> norm_num [piExtract]

/-- Exploratory extraction rate with M=2 and epsilon=1/10 (V20.35c). -/
def learnerExtract (q : Fin 3) : ℚ := (9 / 10) * ((q.val : ℚ) / 2) + 1 / 20

theorem learnerExtract_bounds (q : Fin 3) :
    0 ≤ learnerExtract q ∧ learnerExtract q ≤ 1 := by
  fin_cases q <;> norm_num [learnerExtract]

def referencePayoff (x : Bool) : ℚ := if x then 1 / 20 else -1 / 20
def payoffSign (r : ℚ) : ℤ := if 0 < r then 1 else if r < 0 then -1 else 0

/-- Exact integer clipping onto {0,1,2}, including both endpoints. -/
def clipMemory (n : ℤ) : Fin 3 := if n ≤ 0 then 0 else if 2 ≤ n then 2 else 1

def reinforce (i : Player) (q : Fin 3) (x : Bool) (a : Action) : Fin 3 :=
  clipMemory ((q.val : ℤ) + (if ownAction i a then 1 else -1) *
    payoffSign (reward i x a - referencePayoff x))

/-- Complete learner memory update, using the old world and realized action. -/
def updateL (y : Y) (a : Action) : Memory :=
  (reinforce 0 y.1.1 y.2 a, reinforce 1 y.1.2 y.2 a)

def y0 : Y := ((1, 1), true)

/- The substantive region/descriptor/property and initial pointwise scenario
were registered first. Design v2 below transparently repairs the invalid
singleton comparison BEFORE any margin evaluation: it includes the WHOLE
already-declared region, not an outcome-selected subset. This is exploratory
mathematical design revision, not retroactive pre-registration. -/
def region : Set Y := {y | y.2 = true}
def pointwiseStarts : Set Y := {y0}
def basin : Set Y := region
def comparisonStarts : Set Y := region
def descriptor (y : Y) : Bool := y.2
def relevance (y : Y) : Bool := y.2
def propertyHorizon : ℕ := 3

end PermanssonResearch.X1
