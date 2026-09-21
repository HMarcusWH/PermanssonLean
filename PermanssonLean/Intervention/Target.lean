namespace PermanssonLean

/--
Typed intervention target.

Strategic interventions alter the strategic generator while structural interventions
alter the world-transition kernel. The distinction is frozen at the type boundary so
later constitution theorems cannot silently reinterpret one intervention class as the
other.
-/
inductive InterventionTarget where
  | actionSelection
  | strategicUpdate
  | worldTransition
  | jointStrategic
deriving DecidableEq, Repr

namespace InterventionTarget

/-- Strategic-generator targets are exactly action selection, strategic update,
and their joint replacement. World-transition interventions are structural. -/
def IsStrategic : InterventionTarget → Prop
  | .actionSelection => True
  | .strategicUpdate => True
  | .jointStrategic => True
  | .worldTransition => False

@[simp] theorem isStrategic_actionSelection : IsStrategic .actionSelection := trivial
@[simp] theorem isStrategic_strategicUpdate : IsStrategic .strategicUpdate := trivial
@[simp] theorem isStrategic_jointStrategic : IsStrategic .jointStrategic := trivial
@[simp] theorem not_isStrategic_worldTransition : ¬ IsStrategic .worldTransition := id

end InterventionTarget

end PermanssonLean
