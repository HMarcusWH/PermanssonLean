import PermanssonResearch.MultiAgent.PrivateClock
import PermanssonResearch.MultiAgent.ChronologicalPathLaw

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

theorem measurable_drop :
    Measurable (drop (S0 := S0) (S1 := S1) (S2 := S2) (X := X) (T := T)) :=
  measurable_of_finite _

theorem inherited_exogeneity (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (a : T → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : T → T)
    (hG : IsExogenousCommon G) : IsExogenousCommon (generator G a next) := by
  obtain ⟨c,hc⟩ := hG.common_factors
  refine ⟨c,?_⟩
  apply Kernel.ext
  intro i
  change G.common (dropInput i) = c (commonUpdateKey i)
  rw [hc,Kernel.comap_apply]
  rfl

theorem inherited_strictness
    (a : T → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : T → T)
    (ha : ∀ t, IsStrictlyNonReactive (a t)) : IsStrictlyNonReactive (anchor a next) := by
  classical
  let p : T → Kernel (S0 × S2) A2 := fun t => Classical.choose (ha t).action_factors
  let u : T → Kernel ((S0 × S2) × A2) S2 := fun t => Classical.choose (ha t).update_factors
  have hp t : (a t).action = (p t).comap anchorKey measurable_anchorKey :=
    Classical.choose_spec (ha t).action_factors
  have hu t : (a t).update = (u t).comap anchorUpdateKey measurable_anchorUpdateKey :=
    Classical.choose_spec (ha t).update_factors
  refine ⟨⟨rows (fun k : S0 × (S2 × T) => p k.2.2 (k.1,k.2.1)),?_⟩,
    ⟨rows (fun k : (S0 × (S2 × T)) × A2 =>
      (u k.1.2.2 ((k.1.1,k.1.2.1),k.2)).prod (Measure.dirac (next k.1.2.2))),?_⟩⟩
  · apply Kernel.ext
    intro y
    change (a (phase y)).action (drop y) = p (phase y) (anchorKey (drop y))
    rw [hp,Kernel.comap_apply]
  · apply Kernel.ext
    intro i
    change ((a (phase i.1.1)).update (dropInput i)).prod
      (Measure.dirac (next (phase i.1.1))) =
      (u (phase i.1.1) (anchorUpdateKey (dropInput i))).prod
      (Measure.dirac (next (phase i.1.1)))
    rw [hu,Kernel.comap_apply]

/-- The full lifted row is the scheduled actual row with its next private
clock attached. Hence incorrect phase paths have exactly zero mass. -/
theorem actual_row (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (a : T → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : T → T)
    (t : T) (y : OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) :
    ((((G.openLoop G.player1 (a t)).toModel P).inducedKernel y).map (lift (next t))) =
      ((generator G a next).toModel (physical P)).inducedKernel (lift t y) := by
  classical
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton z)]
  have hz := actual_atom G P a next t (phase z) y (drop z)
  rw [lift_drop] at hz
  rw [hz]
  by_cases ht : phase z = next t
  · have hs : (lift (next t)) ⁻¹' ({z} : Set (NewState (S0 := S0) (S1 := S1)
        (S2 := S2) (X := X) (T := T))) = {drop z} := by
      ext w
      change lift (next t) w = z ↔ w = drop z
      constructor
      · intro h
        simpa using congrArg drop h
      · intro h
        subst w
        rw [← ht,lift_drop]
    simp [hs,ht]
  · have hs : (lift (next t)) ⁻¹' ({z} : Set (NewState (S0 := S0) (S1 := S1)
        (S2 := S2) (X := X) (T := T))) = ∅ := by
      ext w
      simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_empty_iff_false,iff_false]
      intro h
      have heq := congrArg phase h
      exact ht (by simpa using heq.symm)
    simp [hs,ht]

noncomputable def scheduledKernel (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (a : T → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : T → T) (t : T) (n : ℕ) :
    Kernel (OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X))
      (OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) :=
  ((G.openLoop G.player1 (a (next^[n] t))).toModel P).inducedKernel

instance scheduledKernel_isMarkov (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (a : T → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : T → T) (t : T) (n : ℕ) :
    IsMarkovKernel (scheduledKernel G P a next t n) :=
  StrategicWorldModel.inducedKernel_isMarkov _

/-- The original stationary full law on the NEW clocked baseline projects
exactly to the independently constructed chronological Ionescu--Tulcea law.
Consequently all finite prefixes, as well as the infinite laws, agree. -/
theorem actual_projection (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (a : T → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : T → T) (t : T)
    (μ : Measure (OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X))) [IsProbabilityMeasure μ] :
    (((generator G a next).toModel (physical P)).pathLaw (μ.map (lift t))).map
      (fun w n => drop (w n)) = Chronological.law (scheduledKernel G P a next t) μ := by
  let e : ℕ → JointState (GameState S0 S1 S2) X →
      JointState (GameState S0 S1 (S2 × T)) X := fun n => lift (next^[n] t)
  have he : ∀ n, Measurable (e n) := fun _ => measurable_of_finite _
  have hstage : ∀ n y, (scheduledKernel G P a next t n y).map (e (n+1)) =
      ((generator G a next).toModel (physical P)).inducedKernel (e n y) := by
    intro n y
    simpa [scheduledKernel,e,Function.iterate_succ_apply'] using
      actual_row G P a next (next^[n] t) y
  have h := Chronological.map_law_eq_actual (scheduledKernel G P a next t)
    ((generator G a next).toModel (physical P)) e he hstage μ
  have hproj := congrArg (fun ν : Measure (ℕ → NewState (S0 := S0) (S1 := S1)
      (S2 := S2) (X := X) (T := T)) => ν.map (fun w n => drop (w n))) h
  have hd : Measurable (fun w : ℕ → NewState (S0 := S0) (S1 := S1)
      (S2 := S2) (X := X) (T := T) => fun n => drop (w n)) :=
    Measurable.of_eval (fun n => measurable_drop.comp (measurable_pi_apply n))
  rw [Measure.map_map hd (Chronological.measurable_pathMap e he)] at hproj
  have hcancel : (fun w : ℕ → NewState (S0 := S0) (S1 := S1) (S2 := S2)
      (X := X) (T := T) => fun n => drop (w n)) ∘ Chronological.pathMap e = id := by
    funext w n
    rfl
  rw [hcancel,Measure.map_id] at hproj
  simpa [e] using hproj.symm

/-- The same bridge for an actual opponent-locked comparison on the lifted
baseline. Player one's common replacement and player two's scheduled anchor
are exactly the mechanisms consumed by the chronological rows. -/
theorem openLoop_projection (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (a b : T → PlayerTwoMechanism S0 S1 S2 X A1 A2) (next : T → T)
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2) (t : T)
    (μ : Measure (OldState (S0 := S0) (S1 := S1) (S2 := S2) (X := X))) [IsProbabilityMeasure μ] :
    ((((generator G a next).openLoop (playerOne r) (anchor b next)).toModel
      (physical P)).pathLaw (μ.map (lift t))).map (fun w n => drop (w n)) =
      Chronological.law (scheduledKernel (G.closedLoop r) P b next t) μ := by
  exact actual_projection (G.closedLoop r) P b next t μ

end PermanssonResearch.MultiAgent.PrivateClock
