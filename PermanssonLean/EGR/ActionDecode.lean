import PermanssonLean.EGR.GroundedTransport

open MeasureTheory ProbabilityTheory

namespace PermanssonLean

universe uX uA

/-- Paper-I execution record recovered from the canonical embedding:
world-state path together with realized action path. -/
abbrev PaperIDecodedPath (X : Type uX) (A : Type uA) :=
  (ℕ → X) × (ℕ → A)

namespace PaperISelectedModel

variable {X : Type uX} {A : Type uA}
variable [MeasurableSpace X] [MeasurableSpace A]
variable [Inhabited A]

/-- Total decoder for the action-record coordinate.  The `Sum.inl ()`
branch is the arbitrary off-support/default extension permitted by Section 6.2;
actual realized actions are stored as `Sum.inr a`. -/
def decodeActionRecord : PaperIActionRecord A → A :=
  Sum.elim (fun _ => default) id

theorem decodeActionRecord_measurable :
    Measurable (decodeActionRecord (A := A)) := by
  exact Measurable.sumElim measurable_const measurable_id

@[simp]
theorem decodeActionRecord_inr (a : A) :
    decodeActionRecord (Sum.inr a : PaperIActionRecord A) = a :=
  rfl

@[simp]
theorem decodeActionRecord_inl :
    decodeActionRecord (Sum.inl () : PaperIActionRecord A) = default :=
  rfl

/-- Realized action at date t is read from the next strategic coordinate,
exactly as in Section 6.2: a_t = \bar a_{t+1}. -/
def recordedActionPath :
    (ℕ → JointState (PaperIStrategicState A) X) →
      (ℕ → A) :=
  fun w t => decodeActionRecord ((w (t + 1)).1.2)

theorem recordedActionPath_measurable :
    Measurable (recordedActionPath (X := X) (A := A)) := by
  refine Measurable.of_eval fun t => ?_
  exact decodeActionRecord_measurable.comp
    (measurable_snd.comp
      (measurable_fst.comp (measurable_pi_apply (t + 1))))

/-- Section-6.2 total decoding map D. -/
def recordedDecode :
    (ℕ → JointState (PaperIStrategicState A) X) →
      PaperIDecodedPath X A :=
  fun w =>
    (worldPathProjection (X := X) (S := PaperIStrategicState A) w,
      recordedActionPath w)

theorem recordedDecode_measurable :
    Measurable (recordedDecode (X := X) (A := A)) :=
  (worldPathProjection_measurable
    (X := X) (S := PaperIStrategicState A)).prodMk
      recordedActionPath_measurable

@[simp]
theorem recordedDecode_world
    (w : ℕ → JointState (PaperIStrategicState A) X) :
    (recordedDecode (X := X) (A := A) w).1 =
      worldPathProjection (X := X) (S := PaperIStrategicState A) w :=
  rfl

@[simp]
theorem recordedDecode_action
    (w : ℕ → JointState (PaperIStrategicState A) X)
    (t : ℕ) :
    (recordedDecode (X := X) (A := A) w).2 t =
      decodeActionRecord ((w (t + 1)).1.2) :=
  rfl

/-- The deterministic recording update stores the just-realized action. -/
@[simp]
theorem recordingUpdateMap_records_action
    (z : UpdateInput (PaperIStrategicState A) X A) :
    (recordingUpdateMap (X := X) (A := A) z).2 =
      Sum.inr z.1.2 :=
  rfl

/-- The deterministic recording update advances the clock by one. -/
@[simp]
theorem recordingUpdateMap_advances_clock
    (z : UpdateInput (PaperIStrategicState A) X A) :
    (recordingUpdateMap (X := X) (A := A) z).1 =
      z.1.1.1.1 + 1 :=
  rfl

/-- Baseline decoded execution law obtained by the Section-6.2 map D. -/
noncomputable def recordedPathProbability
    (M : PaperISelectedModel X A)
    (x : X) :
    ProbabilityMeasure (PaperIDecodedPath X A) :=
  (RegimeSpecification.pathProbability
    M.embeddedModel
    (diracProba (initialEmbedding (X := X) (A := A) x))).map
      (recordedDecode (X := X) (A := A))

/-- Counterfactual decoded execution law under a transported Paper-I
policy intervention. -/
noncomputable def recordedCounterfactualPathProbability
    (M : PaperISelectedModel X A)
    (J : PaperIPolicyIntervention X A)
    (x : X) :
    ProbabilityMeasure (PaperIDecodedPath X A) :=
  (RegimeSpecification.pathProbability
    (J.transportedIntervention M).intervention.apply
    (diracProba (initialEmbedding (X := X) (A := A) x))).map
      (recordedDecode (X := X) (A := A))

/-- The decoded baseline execution has exactly the already-proved Paper-I
world-path law as its first marginal. -/
theorem recordedPathProbability_worldMarginal
    (M : PaperISelectedModel X A)
    (x : X) :
    (M.recordedPathProbability x).map Prod.fst =
      M.pathProbability (diracProba x) := by
  apply ProbabilityMeasure.toMeasure_injective
  change
    ((RegimeSpecification.pathProbability M.embeddedModel
      (diracProba (initialEmbedding (X := X) (A := A) x))).toMeasure.map
        (recordedDecode (X := X) (A := A))).map Prod.fst =
      (M.pathProbability (diracProba x)).toMeasure
  rw [Measure.map_map measurable_fst recordedDecode_measurable]
  have hproj :=
    M.embedded_worldPathLaw_eq_paperI
      (diracProba (initialEmbedding (X := X) (A := A) x))
  have hwm :
      (diracProba (initialEmbedding (X := X) (A := A) x)).map Prod.snd =
        diracProba x := by
    apply ProbabilityMeasure.toMeasure_injective
    change
      (Measure.dirac (initialEmbedding (X := X) (A := A) x)).map Prod.snd =
        Measure.dirac x
    exact Measure.map_dirac' measurable_snd _
  rw [hwm] at hproj
  simpa [recordedDecode, Function.comp_def,
    RegimeSpecification.pathProbability, pathProbability] using hproj

/-- The decoded counterfactual execution has the previously formalized
Paper-I counterfactual world law as its first marginal. -/
theorem recordedCounterfactualPathProbability_worldMarginal
    (M : PaperISelectedModel X A)
    (J : PaperIPolicyIntervention X A)
    (x : X) :
    (M.recordedCounterfactualPathProbability J x).map Prod.fst =
      J.counterfactualPathProbability M x := by
  apply ProbabilityMeasure.toMeasure_injective
  change
    ((RegimeSpecification.pathProbability
      (J.transportedIntervention M).intervention.apply
      (diracProba (initialEmbedding (X := X) (A := A) x))).toMeasure.map
        (recordedDecode (X := X) (A := A))).map Prod.fst =
      (J.counterfactualPathProbability M x).toMeasure
  rw [Measure.map_map measurable_fst recordedDecode_measurable]
  unfold PaperIPolicyIntervention.counterfactualPathProbability
  apply Measure.map_congr
  filter_upwards [] with w
  rfl

end PaperISelectedModel

end PermanssonLean
