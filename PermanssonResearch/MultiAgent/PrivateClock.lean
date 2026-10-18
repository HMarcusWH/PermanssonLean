import PermanssonResearch.MultiAgent.AutonomousKey

/-! A new finite-phase baseline. The phase belongs to player two's private
state and its update actually advances it. The original baseline's common
update and physical kernel are pulled back along the declared projection. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultiAgent.PrivateClock

set_option autoImplicit false
open PermanssonLean

variable {S0 S1 S2 X A1 A2 T : Type*}
variable [MeasurableSpace S0] [MeasurableSpace S1] [MeasurableSpace S2]
variable [MeasurableSpace X] [MeasurableSpace A1] [MeasurableSpace A2] [MeasurableSpace T]
variable [Fintype S0] [Fintype S1] [Fintype S2] [Fintype X] [Fintype A1] [Fintype A2]
variable [Fintype T]
variable [MeasurableSingletonClass S0] [MeasurableSingletonClass S1]
variable [MeasurableSingletonClass S2] [MeasurableSingletonClass X]
variable [MeasurableSingletonClass A1] [MeasurableSingletonClass A2] [MeasurableSingletonClass T]

abbrev OldState := JointState (GameState S0 S1 S2) X
abbrev NewState := JointState (GameState S0 S1 (S2 × T)) X

def lift (t : T) (y : OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) :
    NewState (S0 := S0) (S1 := S1) (S2 := S2) (X := X) (T := T) :=
  ((y.1.1,(y.1.2.1,(y.1.2.2,t))),y.2)

def drop (y : NewState (S0 := S0) (S1 := S1) (S2 := S2) (X := X) (T := T)) :
    OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X) :=
  ((y.1.1,(y.1.2.1,y.1.2.2.1)),y.2)

def phase (y : NewState (S0 := S0) (S1 := S1) (S2 := S2) (X := X) (T := T)) : T := y.1.2.2.2

def dropWorld (i : WorldInput (GameState S0 S1 (S2 × T)) X (A1 × A2)) :
    WorldInput (GameState S0 S1 S2) X (A1 × A2) := (drop i.1,i.2)
def dropInput (i : UpdateInput (GameState S0 S1 (S2 × T)) X (A1 × A2)) :
    UpdateInput (GameState S0 S1 S2) X (A1 × A2) := (dropWorld i.1,i.2)

@[simp] theorem drop_lift (t : T) (y : OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) :
    drop (lift t y) = y := rfl
@[simp] theorem phase_lift (t : T) (y : OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) :
    phase (lift t y) = t := rfl
@[simp] theorem lift_drop (y : NewState (S0 := S0) (S1 := S1) (S2 := S2) (X := X) (T := T)) :
    lift (phase y) (drop y) = y := rfl

noncomputable def rows {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    [Finite Y] [MeasurableSingletonClass Y] (f : Y → Measure Z) : Kernel Y Z where
  toFun := f
  measurable' := measurable_of_finite f

noncomputable def playerOne (r : PlayerOneMechanism S0 S1 S2 X A1 A2) :
    PlayerOneMechanism S0 S1 (S2 × T) X A1 A2 where
  action := r.action.comap drop (measurable_of_finite _)
  update := r.update.comap dropInput (measurable_of_finite _)
  action_isMarkov := by letI := r.action_isMarkov; infer_instance
  update_isMarkov := by letI := r.update_isMarkov; infer_instance

/-- A declared sequence of opponent mechanisms is stationary on its own
enlarged private state. Its phase is advanced by the actual update kernel. -/
noncomputable def anchor (a : T → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : T → T) :
    PlayerTwoMechanism S0 S1 (S2 × T) X A1 A2 where
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
    (a : T → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : T → T) :
    TwoPlayerGenerator S0 S1 (S2 × T) X A1 A2 where
  player1 := playerOne G.player1
  player2 := anchor a next
  common := G.common.comap dropInput (measurable_of_finite _)
  common_isMarkov := by letI := G.common_isMarkov; infer_instance

noncomputable def physical
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) :
    Kernel (WorldInput (GameState S0 S1 (S2 × T)) X (A1 × A2)) X :=
  P.comap dropWorld (measurable_of_finite _)

instance physical_isMarkov
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P] :
    IsMarkovKernel (physical (T := T) P) := by unfold physical; infer_instance

theorem phase_update (a : T → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : T → T)
    (i : UpdateInput (GameState S0 S1 (S2 × T)) X (A1 × A2)) :
    (anchor a next).update i (Set.univ ×ˢ {next (phase i.1.1)}) = 1 := by
  letI := (a (phase i.1.1)).update_isMarkov
  change (((a (phase i.1.1)).update (dropInput i)).prod
    (Measure.dirac (next (phase i.1.1)))) (Set.univ ×ˢ {next (phase i.1.1)}) = 1
  simp [Measure.prod_prod]

theorem inherited_feasibility
    (a : T → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : T → T)
    (legal : T → OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X) → Set A2)
    (h : ∀ t y, (a t).action y (legal t y) = 1)
    (y : NewState (S0 := S0) (S1 := S1) (S2 := S2) (X := X) (T := T)) :
    (anchor a next).action y (legal (phase y) (drop y)) = 1 := h _ _

/-- Every full actual alpha/P/U atom has precisely the scheduled old-phase
row and the mandatory next phase. This formula includes the zero mass of an
incorrect clock update. -/
theorem actual_atom [DecidableEq T] (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (a : T → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : T → T)
    (t u : T) (y z : OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) :
    ((generator G a next).toModel (physical P)).inducedKernel (lift t y) {lift u z} =
      if u = next t then ((G.openLoop G.player1 (a t)).toModel P).inducedKernel y {z}
      else 0 := by
  classical
  rw [Autonomous.product_transition_atom]
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
    rw [Autonomous.product_transition_atom]
    rfl
  · simp [hu, Ne.symm hu]

/-- Opponent-locking a lifted model keeps the lifted physical object exactly,
and the common update remains the declared baseline pullback. -/
theorem protocol_world_eq (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (a : T → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : T → T)
    (r : PlayerOneMechanism S0 S1 (S2 × T) X A1 A2)
    (b : PlayerTwoMechanism S0 S1 (S2 × T) X A1 A2) :
    (((generator G a next).openLoop r b).toModel (physical P)).world = physical P := rfl

end PermanssonResearch.MultiAgent.PrivateClock
