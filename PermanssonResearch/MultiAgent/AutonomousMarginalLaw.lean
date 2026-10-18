import PermanssonResearch.MultiAgent.AutonomousAEComparison
import PermanssonLean.StrategicWorld.WellPosedness

/-! Actual chronological marginal and path-law transport on general measurable
spaces. The kernel equality assumptions here are intermediate lemmas; the
autonomy theorem derives them from primitive mechanism agreement. -/

namespace PermanssonResearch.MultiAgent.Autonomous

open MeasureTheory ProbabilityTheory Set PermanssonLean
open scoped ENNReal ProbabilityTheory

noncomputable section

def stateLaw {Y : Type*} [MeasurableSpace Y] (K : Kernel Y Y)
    (μ : Measure Y) : ℕ → Measure Y
  | 0 => μ
  | n+1 => K ∘ₘ stateLaw K μ n

instance stateLaw_isProbability {Y : Type*} [MeasurableSpace Y]
    (K : Kernel Y Y) [IsMarkovKernel K] (μ : Measure Y) [IsProbabilityMeasure μ]
    (n : ℕ) : IsProbabilityMeasure (stateLaw K μ n) := by
  induction n with
  | zero => exact ‹IsProbabilityMeasure μ›
  | succ n ih =>
      letI := ih
      change IsProbabilityMeasure (K ∘ₘ stateLaw K μ n)
      infer_instance

theorem map_comp_of_rows {Y Q : Type*} [MeasurableSpace Y] [MeasurableSpace Q]
    (K : Kernel Y Y) (L : Kernel Q Q) (μ : Measure Y)
    (q : Y → Q) (hq : Measurable q)
    (h : ∀ᵐ y ∂μ, (K y).map q = L (q y)) :
    (K ∘ₘ μ).map q = L ∘ₘ μ.map q := by
  ext E hE
  rw [Measure.map_apply hq hE,
    Measure.bind_apply (hE.preimage hq) K.aemeasurable,
    Measure.bind_apply hE L.aemeasurable,
    lintegral_map (L.measurable_coe hE) hq]
  apply lintegral_congr_ae
  filter_upwards [h] with y hy
  have hh := congrArg (fun ν : Measure Q => ν E) hy
  simpa only [Measure.map_apply hq hE] using hh

theorem projected_stateLaw_eq {Y Q : Type*} [MeasurableSpace Y] [MeasurableSpace Q]
    (K : Kernel Y Y) (L : Kernel Q Q) (μ : Measure Y)
    (q : Y → Q) (hq : Measurable q)
    (h : ∀ n, ∀ᵐ y ∂stateLaw K μ n, (K y).map q = L (q y)) (n : ℕ) :
    (stateLaw K μ n).map q = stateLaw L (μ.map q) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (K ∘ₘ stateLaw K μ n).map q = L ∘ₘ stateLaw L (μ.map q) n
      rw [map_comp_of_rows K L _ q hq (h n), ih]

variable {S X A : Type*} [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

theorem actual_eval_zero (M : StrategicWorldModel S X A)
    (μ : Measure (JointState S X)) [IsProbabilityMeasure μ] :
    (M.pathLaw μ).map (fun w : ℕ → JointState S X => w 0) = μ := by
  let last : ((i : Finset.Iic 0) → JointState S X) → JointState S X :=
    fun h => h ⟨0,by simp⟩
  have h := congrArg (fun ν : Measure ((i : Finset.Iic 0) → JointState S X) => ν.map last)
    (StrategicWorldModel.pathLaw_prefix_zero M μ)
  have hlast : Measurable last := measurable_pi_apply _
  rw [Measure.map_map hlast (Preorder.measurable_frestrictLe 0),
    Measure.map_map hlast (MeasurableEquiv.measurable _)] at h
  change (M.pathLaw μ).map (fun w : ℕ → JointState S X => w 0) = μ.map id at h
  simpa using h

theorem actual_eval_succ (M : StrategicWorldModel S X A)
    (μ : Measure (JointState S X)) [IsProbabilityMeasure μ] (n : ℕ) :
    (M.pathLaw μ).map (fun w : ℕ → JointState S X => w (n+1)) =
      M.inducedKernel ∘ₘ (M.pathLaw μ).map (fun w : ℕ → JointState S X => w n) := by
  letI := StrategicWorldModel.inducedKernel_isMarkov M
  let Q := M.pathLaw μ
  let pairFn : (ℕ → JointState S X) → (((i : Finset.Iic n) → JointState S X) × JointState S X) :=
    fun w => (Preorder.frestrictLe n w,w (n+1))
  let last : ((i : Finset.Iic n) → JointState S X) → JointState S X :=
    fun h => h ⟨n,Finset.mem_Iic.mpr le_rfl⟩
  have hpair := StrategicWorldModel.pathLaw_has_transition_pair M μ n
  have hpairMeas : Measurable pairFn := by fun_prop
  have hlastMeas : Measurable last := measurable_pi_apply _
  ext C hC
  have hK : Measurable (fun z : JointState S X => M.inducedKernel z C) :=
    Kernel.measurable_coe _ hC
  calc
    (Q.map (fun w : ℕ → JointState S X => w (n+1))) C =
        Q ((fun w : ℕ → JointState S X => w (n+1)) ⁻¹' C) :=
      Measure.map_apply (measurable_pi_apply (n+1)) hC
    _ = (Q.map pairFn) (Set.univ ×ˢ C) := by
      rw [Measure.map_apply hpairMeas (MeasurableSet.univ.prod hC)]
      congr 1
      ext w
      simp [pairFn]
    _ = ((Q.map (Preorder.frestrictLe n)) ⊗ₘ
        StrategicWorldModel.stationaryHistoryKernel M.inducedKernel n) (Set.univ ×ˢ C) := by
      rw [hpair]
    _ = ∫⁻ h, M.inducedKernel (last h) C ∂(Q.map (Preorder.frestrictLe n)) := by
      rw [Measure.compProd_apply_prod MeasurableSet.univ hC]
      simp only [MeasureTheory.setLIntegral_univ]
      rfl
    _ = ∫⁻ w, M.inducedKernel (w n) C ∂Q := by
      change (∫⁻ h, ((fun z : JointState S X => M.inducedKernel z C) ∘ last) h
        ∂(Q.map (Preorder.frestrictLe n))) = _
      rw [lintegral_map (hK.comp hlastMeas) (Preorder.measurable_frestrictLe n)]
      rfl
    _ = (M.inducedKernel ∘ₘ Q.map (fun w : ℕ → JointState S X => w n)) C := by
      rw [Measure.bind_apply hC (Kernel.aemeasurable _),
        lintegral_map hK (measurable_pi_apply n)]

theorem stateLaw_eq_actual_marginal (M : StrategicWorldModel S X A)
    (μ : Measure (JointState S X)) [IsProbabilityMeasure μ] (n : ℕ) :
    stateLaw M.inducedKernel μ n =
      (M.pathLaw μ).map (fun w : ℕ → JointState S X => w n) := by
  induction n with
  | zero => exact (actual_eval_zero M μ).symm
  | succ n ih => rw [stateLaw, ih, actual_eval_succ]

theorem pathLaw_eq_of_rows_ae [StandardBorelSpace S] [StandardBorelSpace X]
    (M N : StrategicWorldModel S X A) (μ : Measure (JointState S X)) [IsProbabilityMeasure μ]
    (h : ∀ n, M.inducedKernel =ᵐ[stateLaw M.inducedKernel μ n] N.inducedKernel) :
    M.pathLaw μ = N.pathLaw μ := by
  letI := StrategicWorldModel.inducedKernel_isMarkov M
  letI := StrategicWorldModel.inducedKernel_isMarkov N
  have hstate (n : ℕ) : ∀ᵐ w ∂M.pathLaw μ, M.inducedKernel (w n) = N.inducedKernel (w n) := by
    have hm := h n
    rw [stateLaw_eq_actual_marginal] at hm
    exact ae_of_ae_map (measurable_pi_apply n).aemeasurable hm
  have htrans : StrategicWorldModel.HasTransitionPair (M.pathLaw μ) N.inducedKernel := by
    intro n
    have hprefix : ∀ᵐ v ∂(M.pathLaw μ).map (Preorder.frestrictLe n),
        M.inducedKernel (v ⟨n,Finset.mem_Iic.mpr le_rfl⟩) =
          N.inducedKernel (v ⟨n,Finset.mem_Iic.mpr le_rfl⟩) := by
      apply (ae_map_iff (Preorder.measurable_frestrictLe n).aemeasurable
        ((PermanssonResearch.Probability.measurableSet_kernel_equality
          M.inducedKernel N.inducedKernel).preimage (measurable_pi_apply _))).mpr
      exact hstate n
    have hhist : StrategicWorldModel.stationaryHistoryKernel M.inducedKernel n =ᵐ[
        (M.pathLaw μ).map (Preorder.frestrictLe n)]
        StrategicWorldModel.stationaryHistoryKernel N.inducedKernel n := by
      filter_upwards [hprefix] with v hv
      exact hv
    rw [← Measure.compProd_congr hhist]
    exact StrategicWorldModel.pathLaw_has_transition_pair M μ n
  apply (StrategicWorldModel.pathLaw_existsUnique N μ).unique
  · exact ⟨inferInstance, StrategicWorldModel.pathLaw_prefix_zero M μ, htrans⟩
  · exact StrategicWorldModel.pathLaw_spec N μ

end
end PermanssonResearch.MultiAgent.Autonomous
