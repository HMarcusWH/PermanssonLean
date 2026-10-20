import PermanssonResearch.MultiAgent.MeasurableProductTwoPathLaw
import PermanssonLean.Regime.ConstitutiveMargin
import PermanssonLean.Quotient.PathLaw
import Mathlib.Tactic

/-!
NEXT-05.2: actual original whole-path property and B1 constitutive-margin
transport. A matched, typed, admitted binary-side intervention and its
all-measurable induced-kernel intertwining are explicitly required. These
are not inferred from a similarly-named intervention or an unadmitted
favorable opponent anchor.
-/
open MeasureTheory ProbabilityTheory Set
namespace PermanssonResearch.MultiAgent.MeasurableProduct.Two
open PermanssonLean
open PermanssonLean.RegimeSpecification
open PermanssonResearch.MultiAgent
open PermanssonResearch.MultiAgent.FiniteProduct
open PermanssonResearch.MultiAgent.MeasurableProduct
set_option autoImplicit false

universe u0 uS uX uA uH uHb uZ
variable {S0 : Type u0} {S : Fin 2 → Type uS}
variable {X : Type uX} {A : Fin 2 → Type uA}
variable [MeasurableSpace S0] [∀ i, MeasurableSpace (S i)]
variable [MeasurableSpace X] [∀ i, MeasurableSpace (A i)]
variable {H : Type uH} {Hb : Type uHb} {Z : Type uZ}
variable [MeasurableSpace H] [MeasurableSpace Hb] [MetricSpace Z]

/-- Any type-respecting compression transports point-initialization without
fabricating an initial mismatch. -/
theorem pushInitial_dirac_two
    (Q : TypeRespectingStateCompression
      (FiniteProduct.StrategicState S0 S) X
      (GameState S0 (S 0) (S 1)) X)
    (y : JointState (FiniteProduct.StrategicState S0 S) X) :
    Q.pushInitial (diracProba y) = diracProba (Q.stateMap y) := by
  apply ProbabilityMeasure.toMeasure_injective
  change (Measure.dirac y).map Q.stateMap = Measure.dirac (Q.stateMap y)
  rw [Measure.map_dirac y]

/-- Entire-path property map: the original fine path is evaluated by the
same frozen coarse descriptor/property through the actual Q.pathMap. -/
noncomputable def pullbackWholePathProperty
    (Q : TypeRespectingStateCompression
      (FiniteProduct.StrategicState S0 S) X
      (GameState S0 (S 0) (S 1)) X)
    (ψbar : RegimePropertyMap
      (JointState (GameState S0 (S 0) (S 1)) X) Z) :
    RegimePropertyMap (JointState (FiniteProduct.StrategicState S0 S) X) Z :=
  fun ν => ψbar (Q.pushPath ν)

/-- Equality is of original whole-path point-start properties, not
merely equality of terminal values or one-time marginals. -/
theorem baseline_whole_path_property_two
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P]
    (ψbar : RegimePropertyMap
      (JointState (GameState S0 (S 0) (S 1)) X) Z)
    (y : JointState (FiniteProduct.StrategicState S0 S) X) :
    baselinePropertyValue
      (pullbackWholePathProperty
        (compression_two (S0 := S0) (S := S) (X := X)) ψbar)
      (MeasurableProduct.model G P) y =
    baselinePropertyValue ψbar ((binary G).toModel (physical P))
      ((compression_two (S0 := S0) (S := S) (X := X)).stateMap y) := by
  unfold baselinePropertyValue pullbackWholePathProperty
  rw [pathProbability_push_eq_of_kernelIntertwines
    (compression_two (S0 := S0) (S := S) (X := X))
    (MeasurableProduct.model G P)
    ((binary G).toModel (physical P))
    (induced_kernel_intertwines_two G P) (diracProba y)]
  rw [pushInitial_dirac_two]

/-- Intervention property equality requires a separately legal binary
intervention and a proved intertwining for those two treated kernels. -/
theorem intervention_whole_path_property_two
    (Q : TypeRespectingStateCompression
      (FiniteProduct.StrategicState S0 S) X
      (GameState S0 (S 0) (S 1)) X)
    {M : StrategicWorldModel (FiniteProduct.StrategicState S0 S) X (∀ i, A i)}
    {Mbar : StrategicWorldModel (GameState S0 (S 0) (S 1)) X (A 0 × A 1)}
    {C Cbar : Type*} {F : InterventionFamily M C}
    {Fbar : InterventionFamily Mbar Cbar}
    (J : AdmissibleStrategicIntervention F)
    (Jbar : AdmissibleStrategicIntervention Fbar)
    (hK : KernelIntertwines Q J.intervention.apply.inducedKernel
      Jbar.intervention.apply.inducedKernel)
    (ψbar : RegimePropertyMap
      (JointState (GameState S0 (S 0) (S 1)) X) Z)
    (y : JointState (FiniteProduct.StrategicState S0 S) X) :
    intervenedPropertyValue (pullbackWholePathProperty Q ψbar)
      J.intervention y =
      intervenedPropertyValue ψbar Jbar.intervention (Q.stateMap y) := by
  unfold intervenedPropertyValue pullbackWholePathProperty
  rw [pathProbability_push_eq_of_kernelIntertwines
    Q J.intervention.apply Jbar.intervention.apply hK (diracProba y)]
  rw [pushInitial_dirac_two]

/-- Original full B1 constitutive margin is invariant under an actual
admissible, intervention-compatible binary reconstruction. The exact
comparison-domain equality forbids dropping any fine start. -/
theorem original_margin_transport_two
    (G : FiniteProduct.Generator S0 S X A)
    (P : Kernel (WorldInput (FiniteProduct.StrategicState S0 S) X (∀ i, A i)) X)
    [IsMarkovKernel P]
    (spec : RegimeSpecification
      (JointState (FiniteProduct.StrategicState S0 S) X) H)
    (specBar : RegimeSpecification
      (JointState (GameState S0 (S 0) (S 1)) X) Hb)
    {C Cbar : Type*}
    (F : InterventionFamily (MeasurableProduct.model G P) C)
    (Fbar : InterventionFamily ((binary G).toModel (physical P)) Cbar)
    (B₁ : ConstitutiveComparisonSet (MeasurableProduct.model G P) spec)
    (Bbar₁ : ConstitutiveComparisonSet ((binary G).toModel (physical P)) specBar)
    (Q := compression_two (S0 := S0) (S := S) (X := X))
    (hB : Bbar₁.states = Q.stateMap '' B₁.states)
    (J : AdmissibleStrategicIntervention F)
    (Jbar : AdmissibleStrategicIntervention Fbar)
    (hJ : KernelIntertwines Q J.intervention.apply.inducedKernel
      Jbar.intervention.apply.inducedKernel)
    (ψbar : RegimePropertyMap
      (JointState (GameState S0 (S 0) (S 1)) X) Z) :
    constitutiveMargin (MeasurableProduct.model G P) spec F
      (pullbackWholePathProperty Q ψbar) B₁ J =
      constitutiveMargin ((binary G).toModel (physical P)) specBar Fbar
        ψbar Bbar₁ Jbar := by
  have heffect (y : JointState (FiniteProduct.StrategicState S0 S) X) :
      constitutiveEffect (MeasurableProduct.model G P)
        (pullbackWholePathProperty Q ψbar) J y =
      constitutiveEffect ((binary G).toModel (physical P))
        ψbar Jbar (Q.stateMap y) := by
    unfold constitutiveEffect
    rw [baseline_whole_path_property_two G P ψbar y]
    rw [intervention_whole_path_property_two Q J Jbar hJ ψbar y]
  unfold constitutiveMargin
  rw [hB, ← Set.image_comp]
  exact congrArg (fun f : Set ℝ => sInf f)
    (Set.image_congr fun y _ => heffect y)

end PermanssonResearch.MultiAgent.MeasurableProduct.Two
