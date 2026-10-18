import PermanssonResearch.MultiAgent.Protocols

/-!
# Finite autonomous opponent keys: primitive-derived transition atoms

The factorization data below are extracted from the existing strict
nonreactivity and common-exogeneity predicates. They are mechanism identities,
not a premise asserting equality of the induced counterfactual kernels.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultiAgent.Autonomous

set_option autoImplicit false
open PermanssonLean

abbrev State (S0 S1 S2 X : Type*) := JointState (GameState S0 S1 S2) X
abbrev Input (S0 S1 S2 X A1 A2 : Type*) :=
  UpdateInput (GameState S0 S1 S2) X (A1 × A2)

variable {S0 S1 S2 X A1 A2 : Type*}
variable [MeasurableSpace S0] [MeasurableSpace S1] [MeasurableSpace S2]
variable [MeasurableSpace X] [MeasurableSpace A1] [MeasurableSpace A2]

/-- Exactly the original structural restrictions, with their factor kernels
retained as inspectable data. No equality of full transition rows is assumed. -/
structure Profile (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (a : PlayerTwoMechanism S0 S1 S2 X A1 A2) where
  common : Kernel S0 S0
  action : Kernel (S0 × S2) A2
  update : Kernel ((S0 × S2) × A2) S2
  common_eq : G.common = common.comap commonUpdateKey measurable_commonUpdateKey
  action_eq : a.action = action.comap anchorKey measurable_anchorKey
  update_eq : a.update = update.comap anchorUpdateKey measurable_anchorUpdateKey

noncomputable def Profile.ofRestrictions
    {G : TwoPlayerGenerator S0 S1 S2 X A1 A2}
    {a : PlayerTwoMechanism S0 S1 S2 X A1 A2}
    (hG : IsExogenousCommon G) (ha : IsStrictlyNonReactive a) : Profile G a where
  common := hG.common_factors.choose
  action := ha.action_factors.choose
  update := ha.update_factors.choose
  common_eq := hG.common_factors.choose_spec
  action_eq := ha.action_factors.choose_spec
  update_eq := ha.update_factors.choose_spec

variable {G : TwoPlayerGenerator S0 S1 S2 X A1 A2}
variable {a : PlayerTwoMechanism S0 S1 S2 X A1 A2}

theorem Profile.common_apply (d : Profile G a) (i : Input S0 S1 S2 X A1 A2) :
    G.common i = d.common (commonUpdateKey i) := by
  rw [d.common_eq, Kernel.comap_apply]

theorem Profile.action_apply (d : Profile G a) (y : State S0 S1 S2 X) :
    a.action y = d.action (anchorKey y) := by
  rw [d.action_eq, Kernel.comap_apply]

theorem Profile.update_apply (d : Profile G a) (i : Input S0 S1 S2 X A1 A2) :
    a.update i = d.update (anchorUpdateKey i) := by
  rw [d.update_eq, Kernel.comap_apply]

section Finite

variable [Fintype S0] [Fintype S1] [Fintype S2] [Fintype X] [Fintype A1] [Fintype A2]
variable [MeasurableSingletonClass S0] [MeasurableSingletonClass S1]
variable [MeasurableSingletonClass S2] [MeasurableSingletonClass X]
variable [MeasurableSingletonClass A1] [MeasurableSingletonClass A2]

theorem finite_inducedKernel_atom
    {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [Fintype S] [Fintype A] [MeasurableSingletonClass S] [MeasurableSingletonClass A]
    (M : StrategicWorldModel S X A) (y : JointState S X) (s : S) (x : X) :
    M.inducedKernel y {(s,x)} = ∑ b : A,
      M.generator.action y {b} * M.world (y,b) {x} * M.generator.update ((y,b),x) {s} := by
  classical
  rw [StrategicWorldModel.inducedKernel_apply _ _ (measurableSet_singleton (s,x))]
  have h (b : A) (x' : X) :
      M.generator.update ((y,b),x') {s' | (s',x') ∈ ({(s,x)} : Set (JointState S X))} =
        if x' = x then M.generator.update ((y,b),x) {s} else 0 := by
    by_cases hx : x' = x
    · subst x'
      simp
    · have he : {s' | (s',x') ∈ ({(s,x)} : Set (JointState S X))} = ∅ := by
        ext s'
        simp [Prod.mk.injEq, hx]
      simp [he, hx]
  simp_rw [h, lintegral_fintype]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem action_atom (H : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (y : State S0 S1 S2 X) (b1 : A1) (b2 : A2) :
    H.toGenerator.action y {(b1,b2)} = H.player1.action y {b1} * H.player2.action y {b2} := by
  letI := H.player2.action_isMarkov
  rw [TwoPlayerGenerator.toGenerator_action_apply, ← Set.singleton_prod_singleton,
    Measure.prod_prod]

theorem update_atom (H : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (i : Input S0 S1 S2 X A1 A2) (s0 : S0) (s1 : S1) (s2 : S2) :
    H.toGenerator.update i {(s0,(s1,s2))} =
      H.common i {s0} * (H.player1.update i {s1} * H.player2.update i {s2}) := by
  letI := H.player1.update_isMarkov
  letI := H.player2.update_isMarkov
  rw [TwoPlayerGenerator.toGenerator_update_apply, ← Set.singleton_prod_singleton,
    Measure.prod_prod, ← Set.singleton_prod_singleton, Measure.prod_prod]

/-- Complete finite alpha-P-U atom of the ACTUAL product model. -/
theorem product_transition_atom (H : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (y z : State S0 S1 S2 X) :
    (H.toModel P).inducedKernel y {z} = ∑ b1 : A1, ∑ b2 : A2,
      H.player1.action y {b1} * H.player2.action y {b2} * P (y,(b1,b2)) {z.2} *
        H.common ((y,(b1,b2)),z.2) {z.1.1} *
        H.player1.update ((y,(b1,b2)),z.2) {z.1.2.1} *
        H.player2.update ((y,(b1,b2)),z.2) {z.1.2.2} := by
  classical
  rcases z with ⟨⟨s0,s1,s2⟩,x⟩
  rw [finite_inducedKernel_atom]
  change (∑ b : A1 × A2,
    H.toGenerator.action y {b} * P (y,b) {x} * H.toGenerator.update ((y,b),x) {(s0,s1,s2)}) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b1 _
  apply Finset.sum_congr rfl
  intro b2 _
  rw [action_atom, update_atom]
  ring

end Finite
end PermanssonResearch.MultiAgent.Autonomous
