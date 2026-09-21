namespace PermanssonLean

/--
Typed intervention target.

The formalization intentionally keeps strategic and structural interventions distinct.
A later intervention grammar will carry target-specific replacement data, so an
action-selection intervention cannot be silently reinterpreted as a world or update intervention.
-/
inductive InterventionTarget where
  | actionSelection
  | strategicUpdate
  | worldTransition
  | jointStrategic
deriving DecidableEq, Repr

end PermanssonLean
