import PermanssonLean.Regime.ConvergenceMode
import PermanssonLean.Regime.Admissible
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.MeasureTheory.Measure.DiracProba

open Finset Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory Topology

namespace PermanssonLean

universe uX uA uH

/-- Paper-I process after a measurable pure stationary equilibrium selection
has already been fixed.  Equilibrium certification itself is an upstream
game-theoretic input; this structure stores exactly the selected policy and
the original world-transition kernel needed by the EGR semantics. -/
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

/-- Lift a stationary Paper-I world kernel to finite histories. -/
noncomputable def stationaryHistoryKernel
    (K : Kernel X X) (n : ℕ) :
    Kernel ((i : Iic n) → X) X :=
  K.comap (fun h => h ⟨n, mem_Iic.mpr le_rfl⟩) (by fun_prop)

instance stationaryHistoryKernel_isMarkov
    (K : Kernel X X) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (stationaryHistoryKernel K n) := by
  unfold stationaryHistoryKernel
  infer_instance

/-- Canonical Paper-I world-state trajectory law. -/
noncomputable def pathLaw
    (M : PaperISelectedModel X A)
    (μ0 : Measure X)
    [IsProbabilityMeasure μ0] :
    Measure (ℕ → X) := by
  letI : IsMarkovKernel M.equilibriumKernel := M.equilibriumKernel_isMarkov
  exact Kernel.trajMeasure μ0
    (fun n => stationaryHistoryKernel M.equilibriumKernel n)

instance pathLaw_isProbability
    (M : PaperISelectedModel X A)
    (μ0 : Measure X)
    [IsProbabilityMeasure μ0] :
    IsProbabilityMeasure (M.pathLaw μ0) := by
  letI : IsMarkovKernel M.equilibriumKernel := M.equilibriumKernel_isMarkov
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
world-state process.  The descriptor is the frozen global extension used for
transport into Paper II. -/
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
  basin_path_nontrivial :
    ∃ x₁ ∈ spec.basin, ∃ x₂ ∈ spec.basin,
      M.pathLaw (Measure.dirac x₁) ≠
        M.pathLaw (Measure.dirac x₂)

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
