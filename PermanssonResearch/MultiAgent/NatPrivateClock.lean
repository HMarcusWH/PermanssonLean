import PermanssonResearch.MultiAgent.Protocols

/-! A genuinely nonfinite natural-number private-clock baseline. The phase belongs to player two's private
state and its update actually advances it. The original baseline's common
update and physical kernel are pulled back along the declared projection. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultiAgent.NatPrivateClock

set_option autoImplicit false
open PermanssonLean

variable {S0 S1 S2 X A1 A2 : Type*}
variable [MeasurableSpace S0] [MeasurableSpace S1] [MeasurableSpace S2]
variable [MeasurableSpace X] [MeasurableSpace A1] [MeasurableSpace A2]
variable [Countable S0] [Countable S1] [Countable S2] [Fintype X] [Fintype A1] [Fintype A2]
variable [MeasurableSingletonClass S0] [MeasurableSingletonClass S1]
variable [MeasurableSingletonClass S2] [MeasurableSingletonClass X]
variable [MeasurableSingletonClass A1] [MeasurableSingletonClass A2]

abbrev OldState := JointState (GameState S0 S1 S2) X
abbrev NewState := JointState (GameState S0 S1 (S2 × ℕ)) X

def lift (t : ℕ) (y : OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) :
    NewState (S0 := S0) (S1 := S1) (S2 := S2) (X := X)  :=
  ((y.1.1,(y.1.2.1,(y.1.2.2,t))),y.2)

def drop (y : NewState (S0 := S0) (S1 := S1) (S2 := S2) (X := X) ) :
    OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X) :=
  ((y.1.1,(y.1.2.1,y.1.2.2.1)),y.2)

def phase (y : NewState (S0 := S0) (S1 := S1) (S2 := S2) (X := X) ) : ℕ := y.1.2.2.2

def dropWorld (i : WorldInput (GameState S0 S1 (S2 × ℕ)) X (A1 × A2)) :
    WorldInput (GameState S0 S1 S2) X (A1 × A2) := (drop i.1,i.2)
def dropInput (i : UpdateInput (GameState S0 S1 (S2 × ℕ)) X (A1 × A2)) :
    UpdateInput (GameState S0 S1 S2) X (A1 × A2) := (dropWorld i.1,i.2)

@[simp] theorem drop_lift (t : ℕ) (y : OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) :
    drop (lift t y) = y := rfl
@[simp] theorem phase_lift (t : ℕ) (y : OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) :
    phase (lift t y) = t := rfl
@[simp] theorem lift_drop (y : NewState (S0 := S0) (S1 := S1) (S2 := S2) (X := X) ) :
    lift (phase y) (drop y) = y := rfl

noncomputable def rows {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    [Countable Y] [MeasurableSingletonClass Y] (f : Y → Measure Z) : Kernel Y Z where
  toFun := f
  measurable' := measurable_of_countable f

noncomputable def playerOne (r : PlayerOneMechanism S0 S1 S2 X A1 A2) :
    PlayerOneMechanism S0 S1 (S2 × ℕ) X A1 A2 where
  action := r.action.comap drop (measurable_of_countable _)
  update := r.update.comap dropInput (measurable_of_countable _)
  action_isMarkov := by letI := r.action_isMarkov; infer_instance
  update_isMarkov := by letI := r.update_isMarkov; infer_instance

/-- A declared sequence of opponent mechanisms is stationary on its own
enlarged private state. Its phase is advanced by the actual update kernel. -/
noncomputable def anchor (a : ℕ → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : ℕ → ℕ) :
    PlayerTwoMechanism S0 S1 (S2 × ℕ) X A1 A2 where
  action := rows (fun y => (a (phase y)).action (drop y))
  update := rows (fun i => ((a (phase i.1.1)).update (dropInput i)).prod
    (Measure.dirac (next (phase i.1.1))))
  action_isMarkov := ⟨fun y => by
    change IsProbabilityMeasure ((a (phase y)).action (drop y))
    letI := (a (phase y)).action_isMarkov
    infer_instance⟩
  update_isMarkov := ⟨fun i => by
    change IsProbabilityMeasure (((a (phase i.1.1)).update (dropInput i)).prod
      (Measure.dirac (next (phase i.1.1))))
    letI := (a (phase i.1.1)).update_isMarkov
    infer_instance⟩

/-- This is a NEW lifted baseline, whose private update includes the clock. -/
noncomputable def generator (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (a : ℕ → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : ℕ → ℕ) :
    TwoPlayerGenerator S0 S1 (S2 × ℕ) X A1 A2 where
  player1 := playerOne G.player1
  player2 := anchor a next
  common := G.common.comap dropInput (measurable_of_countable _)
  common_isMarkov := by letI := G.common_isMarkov; infer_instance

noncomputable def physical
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) :
    Kernel (WorldInput (GameState S0 S1 (S2 × ℕ)) X (A1 × A2)) X :=
  P.comap dropWorld (measurable_of_countable _)

instance physical_isMarkov
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P] :
    IsMarkovKernel (physical  P) := by unfold physical; infer_instance

theorem phase_update (a : ℕ → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : ℕ → ℕ)
    (i : UpdateInput (GameState S0 S1 (S2 × ℕ)) X (A1 × A2)) :
    (anchor a next).update i (Set.univ ×ˢ {next (phase i.1.1)}) = 1 := by
  letI := (a (phase i.1.1)).update_isMarkov
  change (((a (phase i.1.1)).update (dropInput i)).prod
    (Measure.dirac (next (phase i.1.1)))) (Set.univ ×ˢ {next (phase i.1.1)}) = 1
  simp [Measure.prod_prod]

theorem inherited_feasibility
    (a : ℕ → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : ℕ → ℕ)
    (legal : ℕ → OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X) → Set A2)
    (h : ∀ t y, (a t).action y (legal t y) = 1)
    (y : NewState (S0 := S0) (S1 := S1) (S2 := S2) (X := X) ) :
    (anchor a next).action y (legal (phase y) (drop y)) = 1 := h _ _

/-- Finite action/world integration does not require a finite strategic state.
In particular the next private state may contain the actual unbounded clock. -/
theorem inducedKernel_atom
    {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [Fintype A] [MeasurableSingletonClass S] [MeasurableSingletonClass A]
    (M : StrategicWorldModel S X A) (y : JointState S X) (s : S) (x : X) :
    M.inducedKernel y {(s,x)} = ∑ b : A,
      M.generator.action y {b} * M.world (y,b) {x} * M.generator.update ((y,b),x) {s} := by
  classical
  rw [StrategicWorldModel.inducedKernel_apply _ _ (measurableSet_singleton (s,x))]
  have h (b : A) (x' : X) :
      M.generator.update ((y,b),x') {s' | (s',x') ∈ ({(s,x)} : Set (JointState S X))} =
        if x' = x then M.generator.update ((y,b),x) {s} else 0 := by
    by_cases hx : x' = x
    · subst x'; simp
    · have he : {s' | (s',x') ∈ ({(s,x)} : Set (JointState S X))} = ∅ := by
        ext s'; simp [Prod.mk.injEq, hx]
      simp [he, hx]
  simp_rw [h, lintegral_fintype]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem product_transition_atom (H : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (y z : OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) :
    (H.toModel P).inducedKernel y {z} = ∑ b1 : A1, ∑ b2 : A2,
      H.player1.action y {b1} * H.player2.action y {b2} * P (y,(b1,b2)) {z.2} *
        H.common ((y,(b1,b2)),z.2) {z.1.1} *
        H.player1.update ((y,(b1,b2)),z.2) {z.1.2.1} *
        H.player2.update ((y,(b1,b2)),z.2) {z.1.2.2} := by
  classical
  rcases z with ⟨⟨s0,s1,s2⟩,x⟩
  rw [inducedKernel_atom]
  change (∑ b : A1 × A2,
    H.toGenerator.action y {b} * P (y,b) {x} * H.toGenerator.update ((y,b),x) {(s0,s1,s2)}) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b1 _
  apply Finset.sum_congr rfl
  intro b2 _
  letI := H.player1.action_isMarkov
  letI := H.player2.action_isMarkov
  letI := H.player1.update_isMarkov
  letI := H.player2.update_isMarkov
  rw [TwoPlayerGenerator.toGenerator_action_apply,
    TwoPlayerGenerator.toGenerator_update_apply,
    ← Set.singleton_prod_singleton, Measure.prod_prod,
    ← Set.singleton_prod_singleton, Measure.prod_prod,
    ← Set.singleton_prod_singleton, Measure.prod_prod]
  ring

theorem advancing_update
    (a : ℕ → PlayerTwoMechanism S0 S1 S2 X A1 A2)
    (i : UpdateInput (GameState S0 S1 (S2 × ℕ)) X (A1 × A2)) :
    (anchor a Nat.succ).update i (Set.univ ×ˢ {phase i.1.1 + 1}) = 1 :=
  phase_update a Nat.succ i

/-- Every full actual alpha/P/U atom has precisely the scheduled old-phase
row and the mandatory next phase. This formula includes the zero mass of an
incorrect clock update. -/
theorem actual_atom (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (a : ℕ → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : ℕ → ℕ)
    (t u : ℕ) (y z : OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) :
    ((generator G a next).toModel (physical P)).inducedKernel (lift t y) {lift u z} =
      if u = next t then ((G.openLoop G.player1 (a t)).toModel P).inducedKernel y {z}
      else 0 := by
  classical
  rw [product_transition_atom]
  change (∑ b1 : A1, ∑ b2 : A2,
    G.player1.action y {b1} * (a t).action y {b2} * P (y,(b1,b2)) {z.2} *
      G.common ((y,(b1,b2)),z.2) {z.1.1} *
      G.player1.update ((y,(b1,b2)),z.2) {z.1.2.1} *
      (((a t).update ((y,(b1,b2)),z.2)).prod (Measure.dirac (next t))) {(z.1.2.2,u)}) =
    if u = next t then ((G.openLoop G.player1 (a t)).toModel P).inducedKernel y {z} else 0
  letI := (a t).update_isMarkov
  have hprod (i : UpdateInput (GameState S0 S1 S2) X (A1 × A2)) :
      (((a t).update i).prod (Measure.dirac (next t))) {(z.1.2.2,u)} =
        (a t).update i {z.1.2.2} * (if u = next t then 1 else 0) := by
    rw [← Set.singleton_prod_singleton,Measure.prod_prod]
    rw [Measure.dirac_apply' _ (measurableSet_singleton u)]
    simp only [Set.indicator_apply,Set.mem_singleton_iff,Pi.one_apply]
    congr 1
    simp only [eq_comm]
  simp_rw [hprod]
  by_cases hu : u = next t
  · subst u
    simp only [ite_true,mul_one]
    rw [product_transition_atom]
    rfl
  · simp [hu, Ne.symm hu]

/-- Opponent-locking a lifted model keeps the lifted physical object exactly,
and the common update remains the declared baseline pullback. -/
theorem protocol_world_eq (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (a : ℕ → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : ℕ → ℕ)
    (r : PlayerOneMechanism S0 S1 (S2 × ℕ) X A1 A2)
    (b : PlayerTwoMechanism S0 S1 (S2 × ℕ) X A1 A2) :
    (((generator G a next).openLoop r b).toModel (physical P)).world = physical P := rfl

end PermanssonResearch.MultiAgent.NatPrivateClock
