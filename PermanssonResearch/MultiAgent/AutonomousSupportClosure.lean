import PermanssonResearch.MultiAgent.AutonomousKey

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultiAgent.Autonomous

set_option autoImplicit false
open PermanssonLean

variable {S0 S1 S2 X A1 A2 : Type*}
variable [MeasurableSpace S0] [MeasurableSpace S1] [MeasurableSpace S2]
variable [MeasurableSpace X] [MeasurableSpace A1] [MeasurableSpace A2]
variable [Fintype S0] [Fintype S1] [Fintype S2] [Fintype X] [Fintype A1] [Fintype A2]
variable [MeasurableSingletonClass S0] [MeasurableSingletonClass S1]
variable [MeasurableSingletonClass S2] [MeasurableSingletonClass X]
variable [MeasurableSingletonClass A1] [MeasurableSingletonClass A2]

/-- Full mechanism agreement with the BASELINE opponent on its state and
action/world-input support. The predicate contains no counterfactual-kernel
equality hypothesis and does not reduce update agreement to initial time. -/
structure BaselineAgreement
    (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X)
    (R : Set (State S0 S1 S2 X))
    (a : PlayerTwoMechanism S0 S1 S2 X A1 A2) : Prop where
  action : ∀ y ∈ R, a.action y = G.player2.action y
  update : ∀ y ∈ R, ∀ (b1 : A1) (b2 : A2) (x : X),
    0 < G.player1.action y {b1} * G.player2.action y {b2} * P (y,(b1,b2)) {x} →
      a.update ((y,(b1,b2)),x) = G.player2.update ((y,(b1,b2)),x)

def keySupport (R : Set (State S0 S1 S2 X)) : Set (S0 × S2) := anchorKey '' R

theorem positive_mul {p q : ℝ≥0∞} (hp : 0 < p) (hq : 0 < q) : 0 < p * q :=
  ENNReal.mul_pos_iff.mpr ⟨hp,hq⟩

theorem probability_has_positive_atom {Y : Type*} [MeasurableSpace Y]
    [Fintype Y] [MeasurableSingletonClass Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] : ∃ y : Y, 0 < μ {y} := by
  classical
  have hs : (∑ y : Y, μ {y}) = 1 := by
    simpa using (MeasureTheory.sum_measure_singleton (μ := μ) (s := Finset.univ))
  have hp : 0 < ∑ y : Y, μ {y} := by rw [hs]; exact zero_lt_one
  obtain ⟨y,_,hy⟩ := Finset.sum_pos_iff.mp hp
  exact ⟨y,hy⟩

variable (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
variable (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
variable (R : Set (State S0 S1 S2 X))
variable (a b : PlayerTwoMechanism S0 S1 S2 X A1 A2)

theorem supported_action_eq
    (ha : IsStrictlyNonReactive a) (hb : IsStrictlyNonReactive b)
    (haa : BaselineAgreement G P R a) (hbb : BaselineAgreement G P R b)
    (y : State S0 S1 S2 X) (hy : anchorKey y ∈ keySupport R) :
    a.action y = b.action y := by
  obtain ⟨y0,hy0,hkey⟩ := hy
  calc
    a.action y = a.action y0 := ha.action_eq hkey.symm
    _ = G.player2.action y0 := haa.action y0 hy0
    _ = b.action y0 := (hbb.action y0 hy0).symm
    _ = b.action y := hb.action_eq hkey

/-- A positive opponent action can be completed by a positive BASELINE
player-1 action and a positive physical draw. This transfers the stated
baseline input agreement to every treated input with the same own key/action. -/
theorem supported_update_eq
    (ha : IsStrictlyNonReactive a) (hb : IsStrictlyNonReactive b)
    (haa : BaselineAgreement G P R a) (hbb : BaselineAgreement G P R b)
    (y : State S0 S1 S2 X) (hy : anchorKey y ∈ keySupport R)
    (b1 : A1) (b2 : A2) (x : X) (hpos : 0 < a.action y {b2}) :
    a.update ((y,(b1,b2)),x) = b.update ((y,(b1,b2)),x) := by
  obtain ⟨y0,hy0,hkey⟩ := hy
  have hact : a.action y = G.player2.action y0 :=
    (ha.action_eq hkey.symm).trans (haa.action y0 hy0)
  have hpos2 : 0 < G.player2.action y0 {b2} := by rwa [← hact]
  letI := G.player1.action_isMarkov
  obtain ⟨b0,hpos1⟩ := probability_has_positive_atom (G.player1.action y0)
  obtain ⟨x0,hposx⟩ := probability_has_positive_atom (P (y0,(b0,b2)))
  have hinput : 0 < G.player1.action y0 {b0} * G.player2.action y0 {b2} *
      P (y0,(b0,b2)) {x0} := positive_mul (positive_mul hpos1 hpos2) hposx
  have hk : anchorUpdateKey ((y,(b1,b2)),x) = anchorUpdateKey ((y0,(b0,b2)),x0) := by
    change (anchorKey y,b2) = (anchorKey y0,b2)
    rw [hkey]
  calc
    a.update ((y,(b1,b2)),x) = a.update ((y0,(b0,b2)),x0) := ha.update_eq hk
    _ = G.player2.update ((y0,(b0,b2)),x0) := haa.update y0 hy0 b0 b2 x0 hinput
    _ = b.update ((y0,(b0,b2)),x0) := (hbb.update y0 hy0 b0 b2 x0 hinput).symm
    _ = b.update ((y,(b1,b2)),x) := (hb.update_eq hk).symm

/-- Full actual transition-row equality on the reachable KEY cylinder follows
from supported mechanism agreement, even at full states outside baseline
support. It is a conclusion, never a replacement hypothesis. -/
theorem supported_full_kernel_eq
    (ha : IsStrictlyNonReactive a) (hb : IsStrictlyNonReactive b)
    (haa : BaselineAgreement G P R a) (hbb : BaselineAgreement G P R b)
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2)
    (y : State S0 S1 S2 X) (hy : anchorKey y ∈ keySupport R) :
    ((G.openLoop r a).toModel P).inducedKernel y =
      ((G.openLoop r b).toModel P).inducedKernel y := by
  classical
  apply Measure.ext_of_singleton
  intro z
  rw [product_transition_atom, product_transition_atom]
  simp only [TwoPlayerGenerator.openLoop]
  apply Finset.sum_congr rfl
  intro b1 _
  apply Finset.sum_congr rfl
  intro b2 _
  have hac := supported_action_eq G P R a b ha hb haa hbb y hy
  by_cases hz : a.action y {b2} = 0
  · have hz' : b.action y {b2} = 0 := by rw [← hac]; exact hz
    simp [hz,hz']
  · rw [hac, supported_update_eq G P R a b ha hb haa hbb y hy b1 b2 z.2
      (pos_iff_ne_zero.mpr hz)]

noncomputable def transitionTerm (H : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (y z : State S0 S1 S2 X) (b1 : A1) (b2 : A2) : ℝ≥0∞ :=
  H.player1.action y {b1} * H.player2.action y {b2} * P (y,(b1,b2)) {z.2} *
    H.common ((y,(b1,b2)),z.2) {z.1.1} *
    H.player1.update ((y,(b1,b2)),z.2) {z.1.2.1} *
    H.player2.update ((y,(b1,b2)),z.2) {z.1.2.2}

/-- Baseline-support closure under the exact baseline kernel implies closure
of its key image under EVERY treated player-1 replacement and strict anchor
satisfying the stated baseline mechanism agreement. -/
theorem key_support_closed
    (hG : IsExogenousCommon G) (ha : IsStrictlyNonReactive a)
    (haa : BaselineAgreement G P R a)
    (hR : ∀ y ∈ R, ∀ z, 0 < (G.toModel P).inducedKernel y {z} → z ∈ R)
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2)
    (y : State S0 S1 S2 X) (hy : anchorKey y ∈ keySupport R)
    (z : State S0 S1 S2 X)
    (hp : 0 < ((G.openLoop r a).toModel P).inducedKernel y {z}) :
    anchorKey z ∈ keySupport R := by
  classical
  obtain ⟨y0,hy0,hkey⟩ := hy
  rw [product_transition_atom] at hp
  obtain ⟨b1,_,hp1⟩ := Finset.sum_pos_iff.mp hp
  obtain ⟨b2,_,hp2⟩ := Finset.sum_pos_iff.mp hp1
  simp only [TwoPlayerGenerator.openLoop, ENNReal.mul_pos_iff] at hp2
  rcases hp2 with ⟨⟨⟨⟨⟨_,hA2⟩,_⟩,hC⟩,_⟩,hU2⟩
  have hact : a.action y = G.player2.action y0 :=
    (ha.action_eq hkey.symm).trans (haa.action y0 hy0)
  have hA20 : 0 < G.player2.action y0 {b2} := by rwa [← hact]
  letI := G.player1.action_isMarkov
  letI := G.player1.update_isMarkov
  obtain ⟨b0,hA10⟩ := probability_has_positive_atom (G.player1.action y0)
  obtain ⟨x0,hP0⟩ := probability_has_positive_atom (P (y0,(b0,b2)))
  obtain ⟨s10,hU10⟩ := probability_has_positive_atom (G.player1.update ((y0,(b0,b2)),x0))
  have hinput : 0 < G.player1.action y0 {b0} * G.player2.action y0 {b2} *
      P (y0,(b0,b2)) {x0} := positive_mul (positive_mul hA10 hA20) hP0
  have hk : anchorUpdateKey ((y,(b1,b2)),z.2) = anchorUpdateKey ((y0,(b0,b2)),x0) := by
    change (anchorKey y,b2) = (anchorKey y0,b2)
    rw [hkey]
  have hu : a.update ((y,(b1,b2)),z.2) = G.player2.update ((y0,(b0,b2)),x0) :=
    (ha.update_eq hk).trans (haa.update y0 hy0 b0 b2 x0 hinput)
  have hU20 : 0 < G.player2.update ((y0,(b0,b2)),x0) {z.1.2.2} := by rwa [← hu]
  obtain ⟨c,hc⟩ := hG.common_factors
  have hk0 : commonUpdateKey ((y,(b1,b2)),z.2) =
      commonUpdateKey ((y0,(b0,b2)),x0) := by
    change y.1.1 = y0.1.1
    exact congrArg (fun q : S0 × S2 => q.1) hkey.symm
  have hcommon : G.common ((y,(b1,b2)),z.2) = G.common ((y0,(b0,b2)),x0) := by
    rw [hc, Kernel.comap_apply, Kernel.comap_apply, hk0]
  have hC0 : 0 < G.common ((y0,(b0,b2)),x0) {z.1.1} := by rwa [← hcommon]
  let z0 : State S0 S1 S2 X := ((z.1.1,(s10,z.1.2.2)),x0)
  have ht : 0 < transitionTerm P G y0 z0 b0 b2 :=
    positive_mul (positive_mul (positive_mul hinput hC0) hU10) hU20
  have hK0 : 0 < (G.toModel P).inducedKernel y0 {z0} := by
    rw [product_transition_atom]
    change 0 < ∑ t1 : A1, ∑ t2 : A2, transitionTerm P G y0 z0 t1 t2
    exact lt_of_lt_of_le ht (le_trans
      (Finset.single_le_sum (f := fun t2 : A2 => transitionTerm P G y0 z0 b0 t2)
        (fun _ _ => bot_le) (Finset.mem_univ b2))
      (Finset.single_le_sum (f := fun t1 : A1 => ∑ t2 : A2, transitionTerm P G y0 z0 t1 t2)
        (fun _ _ => bot_le) (Finset.mem_univ b0)))
  exact ⟨z0,hR y0 hy0 z0 hK0,rfl⟩

theorem key_support_ae
    (hG : IsExogenousCommon G) (ha : IsStrictlyNonReactive a)
    (haa : BaselineAgreement G P R a)
    (hR : ∀ y ∈ R, ∀ z, 0 < (G.toModel P).inducedKernel y {z} → z ∈ R)
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2)
    (y : State S0 S1 S2 X) (hy : anchorKey y ∈ keySupport R) :
    ∀ᵐ z ∂((G.openLoop r a).toModel P).inducedKernel y,
      anchorKey z ∈ keySupport R := by
  apply ae_iff_of_countable.mpr
  intro z hz
  exact key_support_closed G P R a hG ha haa hR r y hy z (pos_iff_ne_zero.mpr hz)

end PermanssonResearch.MultiAgent.Autonomous
