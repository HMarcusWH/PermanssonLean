import PermanssonResearch.MultiAgent.Protocols

/-! Natural private clocks on arbitrary measurable coordinates. Only the
schedule index is countable; original strategic, action and world spaces
have no countability, finiteness or measurable-singleton assumptions. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace PermanssonResearch.MultiAgent.MeasurableNatPrivateClock
open PermanssonLean
noncomputable section
set_option autoImplicit false

variable {S0 S1 S2 X A1 A2 : Type*}
variable [MeasurableSpace S0] [MeasurableSpace S1] [MeasurableSpace S2]
variable [MeasurableSpace X] [MeasurableSpace A1] [MeasurableSpace A2]

abbrev OldState := JointState (GameState S0 S1 S2) X
abbrev NewState := JointState (GameState S0 S1 (S2 × ℕ)) X

def liftStrategic (t : ℕ) (s : GameState S0 S1 S2) : GameState S0 S1 (S2 × ℕ) :=
  (s.1,(s.2.1,(s.2.2,t)))
def lift (t : ℕ) (y : OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) :
    NewState (S0 := S0) (S1 := S1) (S2 := S2) (X := X) := (liftStrategic t y.1,y.2)
def drop (y : NewState (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) :
    OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X) :=
  ((y.1.1,(y.1.2.1,y.1.2.2.1)),y.2)
def phase (y : NewState (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) : ℕ := y.1.2.2.2
def dropWorld (i : WorldInput (GameState S0 S1 (S2 × ℕ)) X (A1 × A2)) :
    WorldInput (GameState S0 S1 S2) X (A1 × A2) := (drop i.1,i.2)
def dropInput (i : UpdateInput (GameState S0 S1 (S2 × ℕ)) X (A1 × A2)) :
    UpdateInput (GameState S0 S1 S2) X (A1 × A2) := (dropWorld i.1,i.2)

theorem measurable_liftStrategic (t : ℕ) :
    Measurable (liftStrategic (S0 := S0) (S1 := S1) (S2 := S2) t) := by
  unfold liftStrategic; fun_prop
theorem measurable_lift (t : ℕ) :
    Measurable (lift (S0 := S0) (S1 := S1) (S2 := S2) (X := X) t) := by
  unfold lift liftStrategic; fun_prop
theorem measurable_drop :
    Measurable (drop (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) := by
  unfold drop; fun_prop
theorem measurable_phase :
    Measurable (phase (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) := by
  unfold phase; fun_prop
theorem measurable_dropWorld :
    Measurable (dropWorld (S0 := S0) (S1 := S1) (S2 := S2) (X := X) (A1 := A1) (A2 := A2)) := by
  unfold dropWorld drop; fun_prop
theorem measurable_dropInput :
    Measurable (dropInput (S0 := S0) (S1 := S1) (S2 := S2) (X := X) (A1 := A1) (A2 := A2)) := by
  unfold dropInput dropWorld drop; fun_prop

@[simp] theorem drop_lift (t : ℕ) (y : OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) :
    drop (lift t y) = y := rfl
@[simp] theorem phase_lift (t : ℕ) (y : OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) :
    phase (lift t y) = t := rfl

/-- A countable family of genuine kernels can be selected measurably by an
observed natural clock. The input coordinates themselves are arbitrary. -/
def selectKernel {Y Z W : Type*} [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace W]
    (κ : ℕ → Kernel Y Z) (τ : W → ℕ) (f : W → Y) (hτ : Measurable τ) (hf : Measurable f) :
    Kernel W Z where
  toFun w := κ (τ w) (f w)
  measurable' := by
    have hm : Measurable (fun p : ℕ × Y => κ p.1 p.2) :=
      measurable_from_prod_countable_right (fun t => (κ t).measurable)
    exact hm.comp (hτ.prodMk hf)

def playerOne (r : PlayerOneMechanism S0 S1 S2 X A1 A2) :
    PlayerOneMechanism S0 S1 (S2 × ℕ) X A1 A2 where
  action := r.action.comap drop measurable_drop
  update := r.update.comap dropInput measurable_dropInput
  action_isMarkov := by letI := r.action_isMarkov; infer_instance
  update_isMarkov := by letI := r.update_isMarkov; infer_instance

def anchor (a : ℕ → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : ℕ → ℕ) :
    PlayerTwoMechanism S0 S1 (S2 × ℕ) X A1 A2 where
  action := selectKernel (fun t => (a t).action) phase drop measurable_phase measurable_drop
  update := selectKernel (fun t => ((a t).update).map (fun s => (s,next t)))
    (fun i => phase i.1.1) dropInput
    (measurable_phase.comp (measurable_fst.comp measurable_fst)) measurable_dropInput
  action_isMarkov := ⟨fun y => by
    change IsProbabilityMeasure ((a (phase y)).action (drop y))
    letI := (a (phase y)).action_isMarkov
    infer_instance⟩
  update_isMarkov := ⟨fun i => by
    change IsProbabilityMeasure ((((a (phase i.1.1)).update).map
      (fun s => (s,next (phase i.1.1)))) (dropInput i))
    letI := (a (phase i.1.1)).update_isMarkov
    haveI := Kernel.IsMarkovKernel.map (a (phase i.1.1)).update
      (show Measurable (fun s : S2 => (s,next (phase i.1.1))) by fun_prop)
    infer_instance⟩

theorem anchor_action (a : ℕ → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : ℕ → ℕ)
    (y : NewState (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) :
    (anchor a next).action y = (a (phase y)).action (drop y) := rfl

theorem anchor_update (a : ℕ → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : ℕ → ℕ)
    (i : UpdateInput (GameState S0 S1 (S2 × ℕ)) X (A1 × A2)) :
    (anchor a next).update i = ((a (phase i.1.1)).update (dropInput i)).map
      (fun s => (s,next (phase i.1.1))) := by
  change (((a (phase i.1.1)).update).map
    (fun s => (s,next (phase i.1.1)))) (dropInput i) = _
  exact Kernel.map_apply _ (measurable_id.prodMk measurable_const) _

def generator (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (a : ℕ → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : ℕ → ℕ) :
    TwoPlayerGenerator S0 S1 (S2 × ℕ) X A1 A2 where
  player1 := playerOne G.player1
  player2 := anchor a next
  common := G.common.comap dropInput measurable_dropInput
  common_isMarkov := by letI := G.common_isMarkov; infer_instance

def physical (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) :
    Kernel (WorldInput (GameState S0 S1 (S2 × ℕ)) X (A1 × A2)) X :=
  P.comap dropWorld measurable_dropWorld

instance physical_isMarkov
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P] :
    IsMarkovKernel (physical P) := by unfold physical; infer_instance

theorem advancing_update (a : ℕ → PlayerTwoMechanism S0 S1 S2 X A1 A2)
    (i : UpdateInput (GameState S0 S1 (S2 × ℕ)) X (A1 × A2)) :
    (anchor a Nat.succ).update i (Set.univ ×ˢ {phase i.1.1+1}) = 1 := by
  letI := (a (phase i.1.1)).update_isMarkov
  rw [anchor_update,Measure.map_apply (by fun_prop) (MeasurableSet.univ.prod (measurableSet_singleton _))]
  simp

theorem inherited_feasibility (a : ℕ → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : ℕ → ℕ)
    (legal : ℕ → OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X) → Set A2)
    (h : ∀ t y, (a t).action y (legal t y) = 1)
    (y : NewState (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) :
    (anchor a next).action y (legal (phase y) (drop y)) = 1 := h _ _

theorem inherited_exogeneity (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (a : ℕ → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : ℕ → ℕ)
    (hG : IsExogenousCommon G) : IsExogenousCommon (generator G a next) := by
  obtain ⟨c,hc⟩ := hG.common_factors
  refine ⟨c,?_⟩
  apply Kernel.ext
  intro i
  change G.common (dropInput i) = c (commonUpdateKey i)
  rw [hc,Kernel.comap_apply]
  rfl

theorem inherited_strictness (a : ℕ → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : ℕ → ℕ)
    (ha : ∀ t, IsStrictlyNonReactive (a t)) : IsStrictlyNonReactive (anchor a next) := by
  classical
  let p : ℕ → Kernel (S0 × S2) A2 := fun t => Classical.choose (ha t).action_factors
  let u : ℕ → Kernel ((S0 × S2) × A2) S2 := fun t => Classical.choose (ha t).update_factors
  have hp t : (a t).action = (p t).comap anchorKey measurable_anchorKey :=
    Classical.choose_spec (ha t).action_factors
  have hu t : (a t).update = (u t).comap anchorUpdateKey measurable_anchorUpdateKey :=
    Classical.choose_spec (ha t).update_factors
  refine ⟨⟨selectKernel p (fun k : S0 × (S2 × ℕ) => k.2.2)
      (fun k => (k.1,k.2.1)) (by fun_prop) (by fun_prop),?_⟩,
    ⟨selectKernel (fun t => (u t).map (fun s => (s,next t)))
      (fun k : (S0 × (S2 × ℕ)) × A2 => k.1.2.2)
      (fun k => ((k.1.1,k.1.2.1),k.2)) (by fun_prop) (by fun_prop),?_⟩⟩
  · apply Kernel.ext
    intro y
    change (a (phase y)).action (drop y) = p (phase y) (anchorKey (drop y))
    rw [hp,Kernel.comap_apply]
  · apply Kernel.ext
    intro i
    rw [anchor_update]
    change (((a (phase i.1.1)).update (dropInput i)).map
      (fun s => (s,next (phase i.1.1)))) =
      (((u (phase i.1.1)).map (fun s => (s,next (phase i.1.1))))
        (anchorUpdateKey (dropInput i)))
    rw [Kernel.map_apply _ (by fun_prop),hu,Kernel.comap_apply]

end
end PermanssonResearch.MultiAgent.MeasurableNatPrivateClock
