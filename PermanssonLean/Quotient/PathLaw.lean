import PermanssonLean.Quotient.KernelIntertwining
import PermanssonLean.Regime.Occupation
import PermanssonLean.StrategicWorld.WellPosedness
import Mathlib.Probability.Kernel.Composition.Lemmas

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonLean

universe uS uX uA uSbar uXbar uAbar

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {Sbar : Type uSbar} {Xbar : Type uXbar} {Abar : Type uAbar}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace Sbar] [MeasurableSpace Xbar] [MeasurableSpace Abar]

namespace TypeRespectingStateCompression

/-- Coordinatewise compression of a finite path prefix. -/
def prefixMap
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (n : ℕ) :
    ((i : Iic n) → JointState S X) →
      ((i : Iic n) → JointState Sbar Xbar) :=
  fun h i => Q.stateMap (h i)

theorem prefixMap_measurable
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (n : ℕ) :
    Measurable (Q.prefixMap n) := by
  refine Measurable.of_eval fun i => ?_
  exact Q.stateMap_measurable.comp (measurable_pi_apply i)

theorem prefixMap_frestrictLe
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (n : ℕ)
    (w : ℕ → JointState S X) :
    Q.prefixMap n (Preorder.frestrictLe n w) =
      Preorder.frestrictLe n (Q.pathMap w) :=
  rfl

theorem map_path_prefix
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (μ : Measure (ℕ → JointState S X))
    (n : ℕ) :
    (μ.map Q.pathMap).map (Preorder.frestrictLe n) =
      (μ.map (Preorder.frestrictLe n)).map (Q.prefixMap n) := by
  rw [Measure.map_map (measurable_frestrictLe n) Q.pathMap_measurable,
      Measure.map_map (Q.prefixMap_measurable n) (measurable_frestrictLe n)]
  apply Measure.map_congr
  filter_upwards [] with w
  exact (Q.prefixMap_frestrictLe n w).symm

theorem map_path_transitionPair
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (μ : Measure (ℕ → JointState S X))
    (n : ℕ) :
    (μ.map Q.pathMap).map
        (fun w : ℕ → JointState Sbar Xbar =>
          (Preorder.frestrictLe n w, w (n + 1))) =
      (μ.map
        (fun w : ℕ → JointState S X =>
          (Preorder.frestrictLe n w, w (n + 1)))).map
        (Prod.map (Q.prefixMap n) Q.stateMap) := by
  rw [Measure.map_map (by fun_prop) Q.pathMap_measurable,
      Measure.map_map
        ((Q.prefixMap_measurable n).prodMap Q.stateMap_measurable)
        (by fun_prop)]
  apply Measure.map_congr
  filter_upwards [] with w
  rfl

end TypeRespectingStateCompression

/-- Mapping the first coordinate of a compositional product whose conditional
kernel is pulled back through the same map recovers the compositional product
over the pushed base measure. -/
theorem compProd_comap_map_first
    {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) [SFinite μ]
    (κ : Kernel γ β) [IsSFiniteKernel κ]
    (f : α → γ) (hf : Measurable f) :
    (μ.map f) ⊗ₘ κ =
      (μ ⊗ₘ κ.comap f hf).map (Prod.map f id) := by
  ext s hs
  rw [Measure.compProd_apply hs,
      Measure.map_apply (hf.prodMap measurable_id) hs,
      Measure.compProd_apply ((hf.prodMap measurable_id) hs),
      lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  congr with a
  rw [Kernel.comap_apply']
  congr 1
  ext b
  simp [Prod.map]

/-- Push both coordinates of a transition-pair law through an intertwining
square. -/
theorem compProd_map_both_of_intertwines
    {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    (μ : Measure α) [SFinite μ]
    (K : Kernel α β) [IsSFiniteKernel K]
    (Kbar : Kernel γ δ) [IsSFiniteKernel Kbar]
    (f : α → γ) (g : β → δ)
    (hf : Measurable f) (hg : Measurable g)
    (hK : K.map g = Kbar.comap f hf) :
    (μ.map f) ⊗ₘ Kbar =
      (μ ⊗ₘ K).map (Prod.map f g) := by
  calc
    (μ.map f) ⊗ₘ Kbar =
        (μ ⊗ₘ Kbar.comap f hf).map (Prod.map f id) := by
          exact compProd_comap_map_first μ Kbar f hf
    _ = (μ ⊗ₘ K.map g).map (Prod.map f id) := by rw [← hK]
    _ = ((μ ⊗ₘ K).map (Prod.map id g)).map (Prod.map f id) := by
          rw [← Measure.compProd_map hg]
    _ = (μ ⊗ₘ K).map
        ((Prod.map f id) ∘ (Prod.map id g)) := by
          rw [Measure.map_map
            (hf.prodMap measurable_id)
            (measurable_id.prodMap hg)]
    _ = (μ ⊗ₘ K).map (Prod.map f g) := by
          congr 1
          funext z
          rfl

namespace StrategicWorldModel

/-- Kernel intertwining lifts from the stationary state kernel to the
finite-history kernel used by Ionescu--Tulcea. -/
theorem stationaryHistoryKernel_intertwines
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (K : Kernel (JointState S X) (JointState S X))
    (Kbar : Kernel (JointState Sbar Xbar) (JointState Sbar Xbar))
    (hK : KernelIntertwines Q K Kbar)
    (n : ℕ) :
    (stationaryHistoryKernel K n).map Q.stateMap =
      (stationaryHistoryKernel Kbar n).comap
        (Q.prefixMap n) (Q.prefixMap_measurable n) := by
  ext h C hC
  rw [Kernel.map_apply' _ Q.stateMap_measurable _ hC,
      Kernel.comap_apply']
  unfold stationaryHistoryKernel
  rw [Kernel.comap_apply', Kernel.comap_apply']
  exact kernelIntertwines_apply_preimage Q K Kbar hK _ C hC

/-- The pushforward of a Markov path-law specification through an intertwining
compression satisfies the compressed model's transition-pair identity. -/
theorem map_pathLaw_has_transition_pair
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (M : StrategicWorldModel S X A)
    (Mbar : StrategicWorldModel Sbar Xbar Abar)
    (hK : KernelIntertwines Q M.inducedKernel Mbar.inducedKernel)
    (μ0 : Measure (JointState S X))
    [IsProbabilityMeasure μ0] :
    HasTransitionPair
      ((M.pathLaw μ0).map Q.pathMap)
      Mbar.inducedKernel := by
  intro n
  rw [Q.map_path_prefix (M.pathLaw μ0) n]
  have hLift := stationaryHistoryKernel_intertwines
    Q M.inducedKernel Mbar.inducedKernel hK n
  rw [compProd_map_both_of_intertwines
    ((M.pathLaw μ0).map (Preorder.frestrictLe n))
    (stationaryHistoryKernel M.inducedKernel n)
    (stationaryHistoryKernel Mbar.inducedKernel n)
    (Q.prefixMap n) Q.stateMap
    (Q.prefixMap_measurable n) Q.stateMap_measurable hLift]
  rw [pathLaw_has_transition_pair M μ0 n]
  exact (Q.map_path_transitionPair (M.pathLaw μ0) n).symm

/-- Initial-prefix compatibility of the pushed path law. -/
theorem map_pathLaw_prefix_zero
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (M : StrategicWorldModel S X A)
    (μ0 : Measure (JointState S X))
    [IsProbabilityMeasure μ0] :
    ((M.pathLaw μ0).map Q.pathMap).map (Preorder.frestrictLe 0) =
      (μ0.map Q.stateMap).map
        (MeasurableEquiv.piUnique
          (fun _ : Iic 0 => JointState Sbar Xbar)).symm := by
  rw [Q.map_path_prefix (M.pathLaw μ0) 0,
      pathLaw_prefix_zero M μ0,
      Measure.map_map
        (Q.prefixMap_measurable 0)
        (MeasurableEquiv.piUnique
          (fun _ : Iic 0 => JointState S X)).symm.measurable,
      Measure.map_map
        (MeasurableEquiv.piUnique
          (fun _ : Iic 0 => JointState Sbar Xbar)).symm.measurable
        Q.stateMap_measurable]
  apply Measure.map_congr
  filter_upwards [] with y
  funext i
  exact Subsingleton.elim _ _

/-- The coordinatewise pushforward of the canonical path law is the canonical
path law of the compressed model whenever the induced kernels intertwine. -/
theorem pathLaw_map_eq_of_kernelIntertwines
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (M : StrategicWorldModel S X A)
    (Mbar : StrategicWorldModel Sbar Xbar Abar)
    (hK : KernelIntertwines Q M.inducedKernel Mbar.inducedKernel)
    (μ0 : Measure (JointState S X))
    [IsProbabilityMeasure μ0] :
    (M.pathLaw μ0).map Q.pathMap =
      Mbar.pathLaw (μ0.map Q.stateMap) := by
  let ν : Measure (ℕ → JointState Sbar Xbar) :=
    (M.pathLaw μ0).map Q.pathMap
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  haveI : IsProbabilityMeasure (μ0.map Q.stateMap) := by
    infer_instance
  have hν :
      MarkovPathLawSpec Mbar (μ0.map Q.stateMap) ν := by
    refine ⟨inferInstance, ?_, ?_⟩
    · exact map_pathLaw_prefix_zero Q M μ0
    · exact map_pathLaw_has_transition_pair Q M Mbar hK μ0
  rcases pathLaw_existsUnique Mbar (μ0.map Q.stateMap) with
    ⟨canonical, hcanonical, hunique⟩
  have heq : ν = Mbar.pathLaw (μ0.map Q.stateMap) := by
    exact hunique ν hν
  exact heq

end StrategicWorldModel

namespace RegimeSpecification

/-- Probability-measure form of path-law descent. -/
theorem pathProbability_push_eq_of_kernelIntertwines
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (M : StrategicWorldModel S X A)
    (Mbar : StrategicWorldModel Sbar Xbar Abar)
    (hK : KernelIntertwines Q M.inducedKernel Mbar.inducedKernel)
    (μ0 : ProbabilityMeasure (JointState S X)) :
    Q.pushPath (pathProbability M μ0) =
      pathProbability Mbar (Q.pushInitial μ0) := by
  apply ProbabilityMeasure.toMeasure_injective
  simpa [TypeRespectingStateCompression.pushPath,
    TypeRespectingStateCompression.pushInitial,
    pathProbability] using
      StrategicWorldModel.pathLaw_map_eq_of_kernelIntertwines
        Q M Mbar hK μ0.toMeasure

end RegimeSpecification

end PermanssonLean
