import PermanssonLean.StrategicWorld.Model
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory ProbabilityTheory

namespace PermanssonLean

universe uS uX uA uSbar uXbar

/-- A type-respecting compression of strategic and world coordinates.
The product state map is therefore forced to preserve the semantic split
Y = S × X rather than arbitrarily mixing coordinates. -/
structure TypeRespectingStateCompression
    (S : Type uS) (X : Type uX)
    (Sbar : Type uSbar) (Xbar : Type uXbar)
    [MeasurableSpace S] [MeasurableSpace X]
    [MeasurableSpace Sbar] [MeasurableSpace Xbar] where
  strategic : S → Sbar
  world : X → Xbar
  strategic_measurable : Measurable strategic
  world_measurable : Measurable world
  strategic_surjective : Function.Surjective strategic
  world_surjective : Function.Surjective world

namespace TypeRespectingStateCompression

variable {S : Type uS} {X : Type uX}
variable {Sbar : Type uSbar} {Xbar : Type uXbar}
variable [MeasurableSpace S] [MeasurableSpace X]
variable [MeasurableSpace Sbar] [MeasurableSpace Xbar]

/-- Product state compression q(s,x) = (q_S(s), q_X(x)). -/
def stateMap
    (Q : TypeRespectingStateCompression S X Sbar Xbar) :
    JointState S X → JointState Sbar Xbar :=
  fun y => (Q.strategic y.1, Q.world y.2)

theorem stateMap_measurable
    (Q : TypeRespectingStateCompression S X Sbar Xbar) :
    Measurable Q.stateMap :=
  Q.strategic_measurable.comp measurable_fst |>.prod_mk
    (Q.world_measurable.comp measurable_snd)

theorem stateMap_surjective
    (Q : TypeRespectingStateCompression S X Sbar Xbar) :
    Function.Surjective Q.stateMap := by
  intro ybar
  rcases Q.strategic_surjective ybar.1 with ⟨s, hs⟩
  rcases Q.world_surjective ybar.2 with ⟨x, hx⟩
  exact ⟨(s, x), by simp [stateMap, hs, hx]⟩

/-- Coordinatewise compression of an infinite joint-state path. -/
def pathMap
    (Q : TypeRespectingStateCompression S X Sbar Xbar) :
    (ℕ → JointState S X) → (ℕ → JointState Sbar Xbar) :=
  fun w n => Q.stateMap (w n)

theorem pathMap_measurable
    (Q : TypeRespectingStateCompression S X Sbar Xbar) :
    Measurable Q.pathMap := by
  refine Measurable.of_eval fun n => ?_
  exact Q.stateMap_measurable.comp (measurable_pi_apply n)

/-- Push an initial probability law through the state compression. -/
noncomputable def pushInitial
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (μ : ProbabilityMeasure (JointState S X)) :
    ProbabilityMeasure (JointState Sbar Xbar) :=
  μ.map Q.stateMap

/-- Push a path probability law through the coordinatewise path compression. -/
noncomputable def pushPath
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (μ : ProbabilityMeasure (ℕ → JointState S X)) :
    ProbabilityMeasure (ℕ → JointState Sbar Xbar) :=
  μ.map Q.pathMap

end TypeRespectingStateCompression

end PermanssonLean
