import PermanssonLean.Regime.Admissible
import PermanssonLean.StrategicWorld.PathLaw
import Mathlib.Probability.Kernel.Deterministic
import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Measure.DiracProba

open Finset Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory Topology

namespace PermanssonLean

universe uX uA uH

/-- Paper-I process after a measurable pure stationary equilibrium selection
has already been fixed. Equilibrium certification itself is an upstream
game-theoretic input; this structure stores the selected policy and original
world-transition kernel needed by the EGR semantics. -/
structure PaperISelectedModel
    (X : Type uX) (A : Type uA)
    [MeasurableSpace X] [MeasurableSpace A] where
  policy : X → A
  policy_measurable : Measurable policy
  world : Kernel (X × A) X
  world_isMarkov : IsMarkovKernel world

namespace PaperISelectedModel

variable {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace H]

/-- Paper-I equilibrium-induced world kernel
P^{π*}(D | x) = P(D | x, π*(x)). -/
noncomputable def equilibriumKernel
    (M : PaperISelectedModel X A) : Kernel X X :=
  M.world.comap
    (fun x => (x, M.policy x))
    (measurable_id.prodMk M.policy_measurable)

theorem equilibriumKernel_isMarkov
    (M : PaperISelectedModel X A) :
    IsMarkovKernel M.equilibriumKernel := by
  letI : IsMarkovKernel M.world := M.world_isMarkov
  unfold equilibriumKernel
  infer_instance

/-- Canonical no-memory strategic wrapper of the selected Paper-I process.
The Unit coordinate is semantically inert and exists only to reuse the already
formalized strategic-world path-law machinery. -/
noncomputable def unitModel
    (M : PaperISelectedModel X A) :
    StrategicWorldModel Unit X A where
  generator := {
    action := Kernel.deterministic
      (fun y : JointState Unit X => M.policy y.2)
      (M.policy_measurable.comp measurable_snd)
    update := Kernel.deterministic
      (fun _ : UpdateInput Unit X A => ())
      (by fun_prop)
    action_isMarkov := by infer_instance
    update_isMarkov := by infer_instance
  }
  world := M.world.comap
    (fun z : WorldInput Unit X A => (z.1.2, z.2))
    (by fun_prop)
  world_isMarkov := by
    letI : IsMarkovKernel M.world := M.world_isMarkov
    infer_instance

/-- Canonical embedding of a Paper-I world state into the Unit wrapper. -/
def unitEmbedding : X → JointState Unit X :=
  fun x => ((), x)

theorem unitEmbedding_measurable :
    Measurable (unitEmbedding (X := X)) :=
  measurable_const.prodMk measurable_id

/-- World projection from the semantically inert Unit wrapper. -/
def unitWorldProjection : JointState Unit X → X :=
  Prod.snd

theorem unitWorldProjection_measurable :
    Measurable (unitWorldProjection (X := X)) :=
  measurable_snd

/-- World-path projection from any strategic-world path. -/
def worldPathProjection {S : Type*} :
    (ℕ → JointState S X) → (ℕ → X) :=
  fun w n => (w n).2

theorem worldPathProjection_measurable {S : Type*}
    [MeasurableSpace S] :
    Measurable (worldPathProjection (X := X) (S := S)) := by
  refine Measurable.of_eval fun n => ?_
  exact measurable_snd.comp (measurable_pi_apply n)

/-- Canonical Paper-I world-state trajectory law, defined as the world
projection of the semantically inert Unit strategic wrapper. -/
noncomputable def pathLaw
    (M : PaperISelectedModel X A)
    (μ0 : Measure X)
    [IsProbabilityMeasure μ0] :
    Measure (ℕ → X) :=
  (M.unitModel.pathLaw
    (μ0.map (unitEmbedding (X := X)))).map
      (worldPathProjection (X := X) (S := Unit))

instance pathLaw_isProbability
    (M : PaperISelectedModel X A)
    (μ0 : Measure X)
    [IsProbabilityMeasure μ0] :
    IsProbabilityMeasure (M.pathLaw μ0) := by
  unfold pathLaw
  infer_instance

/-- Probability-measure bundle of the Paper-I path law. -/
noncomputable def pathProbability
    (M : PaperISelectedModel X A)
    (μ0 : ProbabilityMeasure X) :
    ProbabilityMeasure (ℕ → X) :=
  ⟨M.pathLaw μ0.toMeasure, inferInstance⟩

/-- Paper-I pathwise empirical descriptor occupation law, using the frozen
global Borel extension of h supplied in the regime specification. -/
noncomputable def empiricalOccupation
    (spec : RegimeSpecification X H)
    (w : ℕ → X)
    (T : ℕ) (hT : 0 < T) :
    ProbabilityMeasure H := by
  letI : Nonempty (Fin T) := ⟨⟨0, hT⟩⟩
  let u : ProbabilityMeasure (Fin T) :=
    ⟨uniformOn Set.univ, inferInstance⟩
  exact u.map (fun i => spec.descriptor (w (i : ℕ)))

/-- Exact one-step Paper-I invariance under the equilibrium-induced kernel. -/
def IsExactlyInvariant
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H) : Prop :=
  ∀ x ∈ spec.region, M.equilibriumKernel x spec.region = 1

/-- Paper-I limiting occupation-law condition for one initial law. -/
def IsLimitingOccupationLaw
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (μ0 : ProbabilityMeasure X) : Prop :=
  spec.convergenceMode.holds
    (M.pathLaw μ0.toMeasure)
    (empiricalOccupation spec)
    spec.target

end PaperISelectedModel

/-- Paper-I ex-ante nontriviality gate, stated directly on the original
world-state process. The descriptor is the frozen global Borel extension used
for transport into Paper II. -/
structure PaperINontriviality
    {X : Type uX} {A : Type uA} {H : Type uH}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace H]
    [TopologicalSpace X]
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (m : Measure X) : Prop where
  basin_nonempty : spec.basin.Nonempty
  region_nontrivial :
    (interior spec.region).Nonempty ∨ 0 < m spec.region
  descriptor_two_values :
    ∃ x₁ ∈ spec.region, ∃ x₂ ∈ spec.region,
      spec.descriptor x₁ ≠ spec.descriptor x₂
  basin_two_states :
    ∃ x₁ ∈ spec.basin, ∃ x₂ ∈ spec.basin,
      x₁ ≠ x₂

/-- Paper-I EGR semantic kernel after the selected measurable pure stationary
MPE has been supplied. -/
def IsPaperIEGR
    {X : Type uX} {A : Type uA} {H : Type uH}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace H]
    [TopologicalSpace X]
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (m : Measure X) : Prop :=
  PaperINontriviality M spec m ∧
  M.IsExactlyInvariant spec ∧
  ∀ μ0 : ProbabilityMeasure X,
    IsAdmissibleInitialLaw spec μ0 →
      M.IsLimitingOccupationLaw spec μ0

end PermanssonLean
