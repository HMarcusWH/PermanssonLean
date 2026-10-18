import PermanssonResearch.MultiAgent.AutonomousSupportClosure

/-!
# Strict finite MA2 obstruction from full baseline-supported agreement

The reachable set is the positive support at some finite time of the ORIGINAL
baseline process. The full law conclusion is proved for the actual typed
opponent-locked models and every common player-1 mechanism replacement.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultiAgent.Autonomous

set_option autoImplicit false
open PermanssonLean

section GenericFinite

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y] [MeasurableSingletonClass Y]

noncomputable def finiteLaw (K : Kernel Y Y) (μ : Measure Y) : ℕ → Measure Y
  | 0 => μ
  | n+1 => K ∘ₘ finiteLaw K μ n

def reachable (K : Kernel Y Y) (μ : Measure Y) : Set Y :=
  {y | ∃ n : ℕ, 0 < finiteLaw K μ n {y}}

theorem reachable_initial (K : Kernel Y Y) (μ : Measure Y) (y : Y)
    (hy : 0 < μ {y}) : y ∈ reachable K μ := ⟨0,hy⟩

theorem reachable_closed (K : Kernel Y Y) (μ : Measure Y)
    (y : Y) (hy : y ∈ reachable K μ) (z : Y) (hz : 0 < K y {z}) :
    z ∈ reachable K μ := by
  classical
  obtain ⟨n,hn⟩ := hy
  refine ⟨n+1, ?_⟩
  rw [finiteLaw, Measure.bind_apply (measurableSet_singleton z) (Kernel.aemeasurable _),
    lintegral_fintype]
  exact lt_of_lt_of_le (positive_mul hz hn)
    (Finset.single_le_sum
      (f := fun t : Y => K t {z} * finiteLaw K μ n {t})
      (fun _ _ => bot_le) (Finset.mem_univ y))

theorem finiteLaw_ae_invariant (K : Kernel Y Y) (μ : Measure Y) (B : Set Y)
    (hB : MeasurableSet B) (hμ : ∀ᵐ y ∂μ, y ∈ B)
    (hK : ∀ y ∈ B, ∀ᵐ z ∂K y, z ∈ B) (n : ℕ) :
    ∀ᵐ y ∂finiteLaw K μ n, y ∈ B := by
  induction n with
  | zero => exact hμ
  | succ n ih =>
      apply Measure.ae_comp_of_ae_ae hB
      filter_upwards [ih] with y hy
      exact hK y hy

end GenericFinite

section TypedPathCongruence

variable {S X A : Type*} [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [Fintype S] [Fintype X] [MeasurableSingletonClass S] [MeasurableSingletonClass X]

theorem typed_eval_zero (M : StrategicWorldModel S X A)
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

/-- Chapman-Kolmogorov derived directly from the ORIGINAL typed transition
pair identity, without a second path-law construction. -/
theorem typed_eval_succ (M : StrategicWorldModel S X A)
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

/-- The reachable set is exactly positive probability at some actual typed
finite-time marginal, for an arbitrary initial probability measure. -/
theorem finiteLaw_eq_actual_marginal (M : StrategicWorldModel S X A)
    (μ : Measure (JointState S X)) [IsProbabilityMeasure μ] (n : ℕ) :
    finiteLaw M.inducedKernel μ n =
      (M.pathLaw μ).map (fun w : ℕ → JointState S X => w n) := by
  induction n with
  | zero => exact (typed_eval_zero M μ).symm
  | succ n ih => rw [finiteLaw, ih, typed_eval_succ]

theorem reachable_iff_actual_marginal (M : StrategicWorldModel S X A)
    (μ : Measure (JointState S X)) [IsProbabilityMeasure μ] (y : JointState S X) :
    y ∈ reachable M.inducedKernel μ ↔ ∃ n : ℕ,
      0 < ((M.pathLaw μ).map (fun w : ℕ → JointState S X => w n)) {y} := by
  simp only [reachable, Set.mem_setOf_eq, finiteLaw_eq_actual_marginal]

/-- Local transition equality on a proved invariant support transports the
full ORIGINAL typed path law. Neither global row equality nor a selected
observable equality is assumed. -/
theorem typed_pathLaw_eq_of_support
    (M N : StrategicWorldModel S X A) (μ : Measure (JointState S X)) [IsProbabilityMeasure μ]
    (B : Set (JointState S X)) (hB : MeasurableSet B)
    (hμ : ∀ᵐ y ∂μ, y ∈ B)
    (hK : ∀ y ∈ B, ∀ᵐ z ∂M.inducedKernel y, z ∈ B)
    (heq : ∀ y ∈ B, M.inducedKernel y = N.inducedKernel y) :
    M.pathLaw μ = N.pathLaw μ := by
  letI := StrategicWorldModel.inducedKernel_isMarkov M
  letI := StrategicWorldModel.inducedKernel_isMarkov N
  have hstate (n : ℕ) : ∀ᵐ w ∂M.pathLaw μ, w n ∈ B := by
    have hm := finiteLaw_ae_invariant M.inducedKernel μ B hB hμ hK n
    rw [finiteLaw_eq_actual_marginal M μ n] at hm
    exact ae_of_ae_map (measurable_pi_apply n).aemeasurable hm
  have htrans : StrategicWorldModel.HasTransitionPair (M.pathLaw μ) N.inducedKernel := by
    intro n
    have hprefix : ∀ᵐ h ∂(M.pathLaw μ).map (Preorder.frestrictLe n),
        h ⟨n,Finset.mem_Iic.mpr le_rfl⟩ ∈ B := by
      apply (ae_map_iff (Preorder.measurable_frestrictLe n).aemeasurable
        (hB.preimage (measurable_pi_apply _))).mpr
      exact hstate n
    have hhist : StrategicWorldModel.stationaryHistoryKernel M.inducedKernel n =ᵐ[
        (M.pathLaw μ).map (Preorder.frestrictLe n)]
        StrategicWorldModel.stationaryHistoryKernel N.inducedKernel n := by
      filter_upwards [hprefix] with h hh
      simp only [StrategicWorldModel.stationaryHistoryKernel, Kernel.comap_apply]
      exact heq _ hh
    rw [← Measure.compProd_congr hhist]
    exact StrategicWorldModel.pathLaw_has_transition_pair M μ n
  apply (StrategicWorldModel.pathLaw_existsUnique N μ).unique
  · exact ⟨inferInstance, StrategicWorldModel.pathLaw_prefix_zero M μ, htrans⟩
  · exact StrategicWorldModel.pathLaw_spec N μ

end TypedPathCongruence

section Obstruction

variable {S0 S1 S2 X A1 A2 : Type*}
variable [MeasurableSpace S0] [MeasurableSpace S1] [MeasurableSpace S2]
variable [MeasurableSpace X] [MeasurableSpace A1] [MeasurableSpace A2]
variable [Fintype S0] [Fintype S1] [Fintype S2] [Fintype X] [Fintype A1] [Fintype A2]
variable [MeasurableSingletonClass S0] [MeasurableSingletonClass S1]
variable [MeasurableSingletonClass S2] [MeasurableSingletonClass X]
variable [MeasurableSingletonClass A1] [MeasurableSingletonClass A2]

attribute [local instance] StrategicWorldModel.inducedKernel_isMarkov

def baselineSupport (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (μ : Measure (State S0 S1 S2 X)) : Set (State S0 S1 S2 X) :=
  reachable (G.toModel P).inducedKernel μ

/-- M-NOSEPARATION: any two strict autonomous anchors satisfying the FULL
baseline-supported mechanism agreement give identical entire counterfactual
path laws, for every common treated player-1 mechanism. -/
theorem strict_anchors_pathLaw_eq
    (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (μ : Measure (State S0 S1 S2 X)) [IsProbabilityMeasure μ]
    (a b : PlayerTwoMechanism S0 S1 S2 X A1 A2)
    (hG : IsExogenousCommon G) (ha : IsStrictlyNonReactive a) (hb : IsStrictlyNonReactive b)
    (haa : BaselineAgreement G P (baselineSupport G P μ) a)
    (hbb : BaselineAgreement G P (baselineSupport G P μ) b)
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2) :
    ((G.openLoop r a).toModel P).pathLaw μ = ((G.openLoop r b).toModel P).pathLaw μ := by
  classical
  let R := baselineSupport G P μ
  let B : Set (State S0 S1 S2 X) := {y | anchorKey y ∈ keySupport R}
  have hR : ∀ y ∈ R, ∀ z, 0 < (G.toModel P).inducedKernel y {z} → z ∈ R :=
    reachable_closed (G.toModel P).inducedKernel μ
  apply typed_pathLaw_eq_of_support _ _ μ B (Set.toFinite B).measurableSet
  · apply ae_iff_of_countable.mpr
    intro y hy
    exact ⟨y,reachable_initial _ _ y (pos_iff_ne_zero.mpr hy),rfl⟩
  · intro y hy
    exact key_support_ae G P R a hG ha haa hR r y hy
  · intro y hy
    exact supported_full_kernel_eq G P R a b ha hb haa hbb r y hy

/-- M-AUTONOMY: the exact projected key atom, obtained by summing the
ACTUAL product update, world draw and treated-player action. The right side
depends only on the old key and the declared autonomous opponent factors. -/
theorem autonomous_key_atom
    (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (a : PlayerTwoMechanism S0 S1 S2 X A1 A2) (d : Profile G a)
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2)
    (y : State S0 S1 S2 X) (q : S0 × S2) :
    ((((G.openLoop r a).toModel P).inducedKernel y).map anchorKey) {q} =
      d.common y.1.1 {q.1} * ∑ b2 : A2,
        d.action (anchorKey y) {b2} * d.update (anchorKey y,b2) {q.2} := by
  classical
  letI := G.common_isMarkov
  letI := r.action_isMarkov
  letI := r.update_isMarkov
  letI := a.action_isMarkov
  letI := a.update_isMarkov
  rw [Measure.map_apply measurable_anchorKey (measurableSet_singleton q),
    StrategicWorldModel.inducedKernel_apply _ _
      ((measurableSet_singleton q).preimage measurable_anchorKey)]
  have hset (x : X) :
      {s : GameState S0 S1 S2 | (s,x) ∈ anchorKey ⁻¹' ({q} : Set (S0 × S2))} =
        ({q.1} : Set S0) ×ˢ ((Set.univ : Set S1) ×ˢ ({q.2} : Set S2)) := by
    rcases q with ⟨q0,q2⟩
    ext s
    rcases s with ⟨s0,s1,s2⟩
    simp [anchorKey, Prod.mk.injEq]
  change (∫⁻ v : A1 × A2, ∫⁻ x : X,
    (G.openLoop r a).toGenerator.update ((y,v),x)
      {s : GameState S0 S1 S2 | (s,x) ∈ anchorKey ⁻¹' ({q} : Set (S0 × S2))}
      ∂P (y,v) ∂(G.openLoop r a).toGenerator.action y) = _
  simp_rw [hset, TwoPlayerGenerator.toGenerator_update_apply]
  simp only [TwoPlayerGenerator.openLoop, Measure.prod_prod, measure_univ, one_mul]
  simp_rw [d.common_apply, d.update_apply]
  simp only [commonUpdateKey, anchorUpdateKey]
  simp only [lintegral_const, measure_univ, mul_one]
  rw [TwoPlayerGenerator.toGenerator_action_apply]
  simp only [TwoPlayerGenerator.openLoop]
  rw [MeasureTheory.lintegral_prod _ (measurable_of_finite _).aemeasurable]
  simp_rw [d.action_apply]
  simp only [lintegral_const, measure_univ, mul_one]
  rw [lintegral_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b2 _
  ring

end Obstruction
end PermanssonResearch.MultiAgent.Autonomous
