import PermanssonResearch.MultiAgent.MeasurableNatPrivateClock
import PermanssonResearch.MultiAgent.ChronologicalPathLaw

/-! General measurable alpha/P/U row transport and full chronological path
projection for an actual natural private clock. No singleton-atom reduction
or finite action/world hypothesis is used. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace PermanssonResearch.MultiAgent.MeasurableNatPrivateClock
open PermanssonLean
noncomputable section
set_option autoImplicit false
attribute [local instance] StrategicWorldModel.inducedKernel_isMarkov
variable {S0 S1 S2 X A1 A2 : Type*}
variable [MeasurableSpace S0] [MeasurableSpace S1] [MeasurableSpace S2]
variable [MeasurableSpace X] [MeasurableSpace A1] [MeasurableSpace A2]

theorem product_attach_clock (μ0 : Measure S0) (μ1 : Measure S1) (μ2 : Measure S2)
    [IsProbabilityMeasure μ0] [IsProbabilityMeasure μ1] [IsProbabilityMeasure μ2] (t : ℕ) :
    μ0.prod (μ1.prod (μ2.map (fun s => (s,t)))) =
      (μ0.prod (μ1.prod μ2)).map (liftStrategic t) := by
  have hi : μ1.prod (μ2.map (fun s => (s,t))) =
      (μ1.prod μ2).map (Prod.map id (fun s => (s,t))) := by
    simpa only [Measure.map_id] using
      Measure.map_prod_map μ1 μ2 measurable_id (by fun_prop : Measurable (fun s : S2 => (s,t)))
  rw [hi]
  have ho := Measure.map_prod_map μ0 (μ1.prod μ2) measurable_id
    (show Measurable (Prod.map id (fun s : S2 => (s,t)) : S1 × S2 → S1 × (S2 × ℕ)) by fun_prop)
  have he : (Prod.map id (Prod.map id (fun s : S2 => (s,t))) :
      S0 × (S1 × S2) → S0 × (S1 × (S2 × ℕ))) = liftStrategic t := by funext s; rfl
  simpa only [Measure.map_id,he] using ho

theorem action_lift (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (a : ℕ → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : ℕ → ℕ)
    (t : ℕ) (y : OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) :
    (generator G a next).toGenerator.action (lift t y) =
      (G.openLoop G.player1 (a t)).toGenerator.action y := by
  rw [TwoPlayerGenerator.toGenerator_action_apply,TwoPlayerGenerator.toGenerator_action_apply]
  rfl

theorem update_lift (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (a : ℕ → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : ℕ → ℕ)
    (t : ℕ) (y : OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X))
    (b : A1 × A2) (x : X) :
    (generator G a next).toGenerator.update ((lift t y,b),x) =
      ((G.openLoop G.player1 (a t)).toGenerator.update ((y,b),x)).map (liftStrategic (next t)) := by
  letI := G.common_isMarkov
  letI := G.player1.update_isMarkov
  letI := (a t).update_isMarkov
  rw [TwoPlayerGenerator.toGenerator_update_apply,TwoPlayerGenerator.toGenerator_update_apply]
  change (G.common ((y,b),x)).prod ((G.player1.update ((y,b),x)).prod
    ((anchor a next).update ((lift t y,b),x))) = _
  rw [anchor_update]
  change (G.common ((y,b),x)).prod ((G.player1.update ((y,b),x)).prod
    (((a t).update ((y,b),x)).map (fun s => (s,next t)))) = _
  exact product_attach_clock _ _ _ (next t)

/-- Whole actual measures, rather than atom values: the lifted alpha/P/U
row is exactly the scheduled original row with the next clock attached. -/
theorem actual_row (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (a : ℕ → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : ℕ → ℕ)
    (t : ℕ) (y : OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) :
    ((((G.openLoop G.player1 (a t)).toModel P).inducedKernel y).map (lift (next t))) =
      ((generator G a next).toModel (physical P)).inducedKernel (lift t y) := by
  ext E hE
  rw [Measure.map_apply (measurable_lift _) hE,
    StrategicWorldModel.inducedKernel_apply _ _ (hE.preimage (measurable_lift _)),
    StrategicWorldModel.inducedKernel_apply _ _ hE]
  dsimp only [TwoPlayerGenerator.toModel]
  rw [action_lift]
  apply lintegral_congr
  intro b
  change (∫⁻ x, (G.openLoop G.player1 (a t)).toGenerator.update ((y,b),x)
    {s | (liftStrategic (next t) s,x) ∈ E} ∂P (y,b)) =
      ∫⁻ x, (generator G a next).toGenerator.update ((lift t y,b),x)
        {s | (s,x) ∈ E} ∂P (y,b)
  apply lintegral_congr
  intro x
  have hs : MeasurableSet {s : GameState S0 S1 (S2 × ℕ) | (s,x) ∈ E} :=
    hE.preimage (show Measurable (fun s : GameState S0 S1 (S2 × ℕ) => (s,x)) by fun_prop)
  rw [update_lift,Measure.map_apply (measurable_liftStrategic _) hs]
  rfl

def scheduledKernel (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (a : ℕ → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : ℕ → ℕ) (t n : ℕ) :
    Kernel (OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X))
      (OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) :=
  ((G.openLoop G.player1 (a (next^[n] t))).toModel P).inducedKernel

instance scheduledKernel_isMarkov (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (a : ℕ → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : ℕ → ℕ) (t n : ℕ) :
    IsMarkovKernel (scheduledKernel G P a next t n) :=
  StrategicWorldModel.inducedKernel_isMarkov _

/-- Projection of the ORIGINAL stationary path law of the new lifted model
is the independently constructed chronological law, for any initial law. -/
theorem actual_projection (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (a : ℕ → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : ℕ → ℕ) (t : ℕ)
    (μ : Measure (OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X))) [IsProbabilityMeasure μ] :
    (((generator G a next).toModel (physical P)).pathLaw (μ.map (lift t))).map
      (fun w n => drop (w n)) = Chronological.law (scheduledKernel G P a next t) μ := by
  let e : ℕ → OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X) →
      NewState (S0 := S0) (S1 := S1) (S2 := S2) (X := X) := fun n => lift (next^[n] t)
  have he : ∀ n, Measurable (e n) := fun _ => measurable_lift _
  have hstage : ∀ n y, (scheduledKernel G P a next t n y).map (e (n+1)) =
      ((generator G a next).toModel (physical P)).inducedKernel (e n y) := by
    intro n y
    simpa [scheduledKernel,e,Function.iterate_succ_apply'] using
      actual_row G P a next (next^[n] t) y
  have h := Chronological.map_law_eq_actual (scheduledKernel G P a next t)
    ((generator G a next).toModel (physical P)) e he hstage μ
  have hproj := congrArg (fun ν : Measure (ℕ → NewState (S0 := S0) (S1 := S1)
      (S2 := S2) (X := X)) => ν.map (fun w n => drop (w n))) h
  have hd : Measurable (fun w : ℕ → NewState (S0 := S0) (S1 := S1)
      (S2 := S2) (X := X) => fun n => drop (w n)) :=
    Measurable.of_eval (fun n => measurable_drop.comp (measurable_pi_apply n))
  rw [Measure.map_map hd (Chronological.measurable_pathMap e he)] at hproj
  have hcancel : (fun w : ℕ → NewState (S0 := S0) (S1 := S1) (S2 := S2)
      (X := X) => fun n => drop (w n)) ∘ Chronological.pathMap e = id := by
    funext w n
    rfl
  rw [hcancel,Measure.map_id] at hproj
  simpa [e] using hproj.symm

theorem openLoop_projection (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (a b : ℕ → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : ℕ → ℕ)
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2) (t : ℕ)
    (μ : Measure (OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X))) [IsProbabilityMeasure μ] :
    ((((generator G a next).openLoop (playerOne r) (anchor b next)).toModel
      (physical P)).pathLaw (μ.map (lift t))).map (fun w n => drop (w n)) =
      Chronological.law (scheduledKernel (G.closedLoop r) P b next t) μ :=
  actual_projection (G.closedLoop r) P b next t μ

theorem succ_iterate (t n : ℕ) : (Nat.succ^[n]) t = t+n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih]; omega

theorem natural_scheduled_row (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (a : ℕ → PlayerTwoMechanism S0 S1 S2 X A1 A2) (t n : ℕ) :
    scheduledKernel G P a Nat.succ t n =
      ((G.openLoop G.player1 (a (t+n))).toModel P).inducedKernel := by
  unfold scheduledKernel
  rw [succ_iterate]

theorem natural_projection (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (a : ℕ → PlayerTwoMechanism S0 S1 S2 X A1 A2) (t : ℕ)
    (μ : Measure (OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X))) [IsProbabilityMeasure μ] :
    (((generator G a Nat.succ).toModel (physical P)).pathLaw (μ.map (lift t))).map
      (fun w n => drop (w n)) = Chronological.law (scheduledKernel G P a Nat.succ t) μ :=
  actual_projection G P a Nat.succ t μ

theorem protocol_world_eq (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (a : ℕ → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : ℕ → ℕ)
    (r : PlayerOneMechanism S0 S1 (S2 × ℕ) X A1 A2)
    (b : PlayerTwoMechanism S0 S1 (S2 × ℕ) X A1 A2) :
    (((generator G a next).openLoop r b).toModel (physical P)).world = physical P := rfl

end
end PermanssonResearch.MultiAgent.MeasurableNatPrivateClock
