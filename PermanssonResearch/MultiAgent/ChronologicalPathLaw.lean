import PermanssonLean.Quotient.PathLaw

/-! Time-dependent embeddings of a genuine chronological Ionescu--Tulcea law
into an original stationary typed model. The stage-by-stage measure equality
is proved before invoking the original canonical path-law uniqueness theorem. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultiAgent.Chronological

set_option autoImplicit false
open PermanssonLean

variable {S X S' X' A' : Type*}
variable [MeasurableSpace S] [MeasurableSpace X]
variable [MeasurableSpace S'] [MeasurableSpace X'] [MeasurableSpace A']

noncomputable def historyKernel
    (K : ℕ → Kernel (JointState S X) (JointState S X)) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → JointState S X) (JointState S X) :=
  StrategicWorldModel.stationaryHistoryKernel (K n) n

instance historyKernel_isMarkov
    (K : ℕ → Kernel (JointState S X) (JointState S X)) [∀ n, IsMarkovKernel (K n)] (n : ℕ) :
    IsMarkovKernel (historyKernel K n) := by unfold historyKernel; infer_instance

/-- The chronological law uses the declared time-n row, independently of the
clocked stationary model with which it will be compared. -/
noncomputable def law (K : ℕ → Kernel (JointState S X) (JointState S X))
    [∀ n, IsMarkovKernel (K n)] (μ : Measure (JointState S X)) :
    Measure (ℕ → JointState S X) := Kernel.trajMeasure μ (historyKernel K)

instance law_isProbability (K : ℕ → Kernel (JointState S X) (JointState S X))
    [∀ n, IsMarkovKernel (K n)] (μ : Measure (JointState S X)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (law K μ) := by unfold law; infer_instance

def pathMap (e : ℕ → JointState S X → JointState S' X')
    (w : ℕ → JointState S X) : ℕ → JointState S' X' := fun n => e n (w n)

def prefixMap (e : ℕ → JointState S X → JointState S' X') (n : ℕ)
    (h : (i : Finset.Iic n) → JointState S X) : (i : Finset.Iic n) → JointState S' X' :=
  fun i => e i.val (h i)

theorem measurable_pathMap (e : ℕ → JointState S X → JointState S' X')
    (he : ∀ n, Measurable (e n)) : Measurable (pathMap e) := by
  exact Measurable.of_eval (fun n => (he n).comp (measurable_pi_apply n))

theorem measurable_prefixMap (e : ℕ → JointState S X → JointState S' X')
    (he : ∀ n, Measurable (e n)) (n : ℕ) : Measurable (prefixMap e n) := by
  exact Measurable.of_eval (fun i => (he i.val).comp (measurable_pi_apply i))

theorem map_prefix (e : ℕ → JointState S X → JointState S' X')
    (he : ∀ n, Measurable (e n)) (ν : Measure (ℕ → JointState S X)) (n : ℕ) :
    (ν.map (pathMap e)).map (Preorder.frestrictLe n) =
      (ν.map (Preorder.frestrictLe n)).map (prefixMap e n) := by
  rw [Measure.map_map (Preorder.measurable_frestrictLe n) (measurable_pathMap e he),
    Measure.map_map (measurable_prefixMap e he n) (Preorder.measurable_frestrictLe n)]
  rfl

theorem map_pair (e : ℕ → JointState S X → JointState S' X')
    (he : ∀ n, Measurable (e n)) (ν : Measure (ℕ → JointState S X)) (n : ℕ) :
    (ν.map (pathMap e)).map (fun w => (Preorder.frestrictLe n w,w (n+1))) =
      (ν.map (fun w => (Preorder.frestrictLe n w,w (n+1)))).map
        (Prod.map (prefixMap e n) (e (n+1))) := by
  rw [Measure.map_map (by fun_prop) (measurable_pathMap e he),
    Measure.map_map ((measurable_prefixMap e he n).prodMap (he (n+1))) (by fun_prop)]
  rfl

/-- Actual stage embeddings imply equality with the ORIGINAL typed full path
law, for any initial probability law, not only a terminal statistic. -/
theorem map_law_eq_actual
    (K : ℕ → Kernel (JointState S X) (JointState S X)) [∀ n, IsMarkovKernel (K n)]
    (M : StrategicWorldModel S' X' A')
    (e : ℕ → JointState S X → JointState S' X') (he : ∀ n, Measurable (e n))
    (hK : ∀ n y, ((K n) y).map (e (n+1)) = M.inducedKernel (e n y))
    (μ : Measure (JointState S X)) [IsProbabilityMeasure μ] :
    (law K μ).map (pathMap e) = M.pathLaw (μ.map (e 0)) := by
  letI := StrategicWorldModel.inducedKernel_isMarkov M
  haveI : IsProbabilityMeasure (μ.map (e 0)) := inferInstance
  haveI : IsProbabilityMeasure ((law K μ).map (pathMap e)) := inferInstance
  apply (StrategicWorldModel.pathLaw_existsUnique M (μ.map (e 0))).unique
  · refine ⟨inferInstance,?_,?_⟩
    · rw [map_prefix e he]
      have h0 : (law K μ).map (Preorder.frestrictLe 0) =
          μ.map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => JointState S X)).symm := by
        unfold law Kernel.trajMeasure
        rw [Measure.map_comp _ _ (by fun_prop),Kernel.traj_map_frestrictLe]
        simp
      rw [h0,Measure.map_map (measurable_prefixMap e he 0) (MeasurableEquiv.measurable _),
        Measure.map_map (MeasurableEquiv.measurable _) (he 0)]
      congr 1
      funext y i
      have hi : i.val = 0 := by have := Finset.mem_Iic.mp i.property; omega
      simp [prefixMap,Function.comp_def,hi]
    · intro n
      rw [map_prefix e he]
      have hhist : (historyKernel K n).map (e (n+1)) =
          (StrategicWorldModel.stationaryHistoryKernel M.inducedKernel n).comap
            (prefixMap e n) (measurable_prefixMap e he n) := by
        apply Kernel.ext
        intro h
        rw [Kernel.map_apply _ (he (n+1)),Kernel.comap_apply]
        exact hK n (h ⟨n,Finset.mem_Iic.mpr le_rfl⟩)
      rw [compProd_map_both_of_intertwines _ _ _ _ _
        (measurable_prefixMap e he n) (he (n+1)) hhist]
      rw [show (law K μ).map (Preorder.frestrictLe n) ⊗ₘ historyKernel K n =
        (law K μ).map (fun w => (Preorder.frestrictLe n w,w (n+1))) by
          exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure]
      exact (map_pair e he (law K μ) n).symm
  · exact StrategicWorldModel.pathLaw_spec M _

end PermanssonResearch.MultiAgent.Chronological
