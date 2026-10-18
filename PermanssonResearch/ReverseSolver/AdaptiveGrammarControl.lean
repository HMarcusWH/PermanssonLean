import PermanssonResearch.GrammarRobust.OverlapCanonicalBridge
import PermanssonResearch.ReverseSolver.MonitorOptimality
import PermanssonResearch.ReverseSolver.ChronologicalMonitorMeasure

/-! Adaptive finite menus of actual admissible alpha/world/update block models.
At each node the controller chooses the entire patch before the original
alpha -> P -> U stage. Its history may choose a different patch next time.
The rational atom certificate is explicit; no frozen intervention is inferred
from this time-dependent controlled law. -/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch.ReverseSolver.AdaptiveGrammarControl

open PermanssonLean PermanssonResearch.GrammarRobust
open ControlledKernel FiniteMonitor

variable {S X A C : Type*} [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace A] [DecidableEq C] [Fintype C] {n : ℕ}

structure CertifiedMenu (M : StrategicWorldModel S X A) (C : Type*)
    [DecidableEq C] (n : ℕ) where
  stateIndex : Fin n ≃ᵐ JointState S X
  states_nonempty : 0 < n
  baseline : RationalMarkovMatrix n
  baseline_atom_certificate : ∀ y z, M.inducedKernel
    (stateIndex y) {stateIndex z} = ENNReal.ofReal (baseline.entry y z : ℝ)
  selection : C → PatchSelection S X A
  admitted : PatchSelection S X A → Prop
  selection_admitted : ∀ c, admitted (selection c)
  compatible_action : ∀ c, ∀ p ∈ (selection c).1,
    ∀ q ∈ (selection c).1, p.Compatible q
  compatible_update : ∀ c, ∀ p ∈ (selection c).2,
    ∀ q ∈ (selection c).2, p.Compatible q
  options : Fin n → Finset C
  options_nonempty : ∀ y, (options y).Nonempty
  rational : C → RationalMarkovMatrix n
  atom_certificate : ∀ c y z,
    (overlapModel M (selection c).1 (selection c).2).inducedKernel
      (stateIndex y) {stateIndex z} = ENNReal.ofReal ((rational c).entry y z : ℝ)

variable (M : StrategicWorldModel S X A) (D : CertifiedMenu M C n)

noncomputable def blockModel (c : C) : StrategicWorldModel S X A :=
  overlapModel M (D.selection c).1 (D.selection c).2

noncomputable def blockIntervention (c : C) :
    AdmissibleStrategicIntervention (overlapFamily M D.admitted) :=
  overlapIntervention M D.admitted (D.selection c) (D.selection_admitted c)

theorem blockIntervention_apply (c : C) :
    (blockIntervention M D c).intervention.apply = blockModel M D c := rfl

theorem block_preserves_world (c : C) : (blockModel M D c).world = M.world := rfl

def system : FiniteControlSystem C n where
  states_nonempty := D.states_nonempty
  baseline := D.baseline
  options := D.options
  options_nonempty := D.options_nonempty
  matrix := D.rational

/-- The actual typed block row, after the selected alpha/P/U stage. -/
noncomputable def typedRow (c : C) (y z : Fin n) : ℝ :=
  ((blockModel M D c).inducedKernel (D.stateIndex y) {D.stateIndex z}).toReal

theorem typedRow_eq (c : C) (y z : Fin n) :
    typedRow M D c y z = ((system M D).matrix c).entry y z := by
  unfold typedRow blockModel
  rw [D.atom_certificate]
  apply ENNReal.toReal_ofReal
  exact_mod_cast (D.rational c).entry_nonneg y z

/-- Independent chronological word law built from the actual typed rows.
The behavioral control is sampled before each full block row. -/
noncomputable def typedTraceMass (σ : BehavioralPolicy (system M D)) :
    ℕ → TraceHistory C n → Fin n → List (C × Fin n) → ℝ
  | _, _, _, [] => 1
  | t, h, y, (c,z)::xs => σ.weight t h y c * typedRow M D c y z *
      typedTraceMass σ (t+1) (appendTrace h c z) z xs

theorem typedTraceMass_eq (σ : BehavioralPolicy (system M D))
    (t : ℕ) (h : TraceHistory C n) (y : Fin n) (xs : List (C × Fin n)) :
    typedTraceMass M D σ t h y xs = traceMass (system M D) σ t h y xs := by
  induction xs generalizing t h y with
  | nil => rfl
  | cons a xs ih =>
      rcases a with ⟨c,z⟩
      simp only [typedTraceMass, traceMass, typedRow_eq, ih]

theorem typedTraceMass_nonnegative (σ : BehavioralPolicy (system M D))
    (t : ℕ) (h : TraceHistory C n) (y : Fin n) (xs : List (C × Fin n)) :
    0 ≤ typedTraceMass M D σ t h y xs := by
  rw [typedTraceMass_eq]
  exact traceMass_nonnegative (system M D) σ t h y xs

theorem typedTraceMass_total_one (σ : BehavioralPolicy (system M D))
    (N t : ℕ) (h : TraceHistory C n) (y : Fin n) :
    ((traceWords C n N).map (typedTraceMass M D σ t h y)).sum = 1 := by
  have hfun : typedTraceMass M D σ t h y = traceMass (system M D) σ t h y :=
    funext (fun xs => typedTraceMass_eq M D σ t h y xs)
  rw [hfun]
  exact traceMass_total_one (system M D) σ N t h y

/-- Independently normalized finite history law, made directly from the
actual block singleton atoms. The measurable state indexing is explicit. -/
noncomputable def typedChronologicalLaw (σ : BehavioralPolicy (system M D))
    (N t : ℕ) (h : TraceHistory C n) (y : Fin n) :
    FiniteProbabilityLaw (List (C × Fin n)) where
  support := (traceWords C n N).toFinset
  atom xs := if xs ∈ (traceWords C n N).toFinset then typedTraceMass M D σ t h y xs else 0
  nonnegative xs := by split <;> simp [typedTraceMass_nonnegative]
  supported xs hx := by simp [hx]
  normalized := by
    simp only [Finset.sum_ite_mem, Finset.inter_self]
    rw [List.sum_toFinset _ (traceWords_nodup N)]
    exact typedTraceMass_total_one M D σ N t h y

theorem typedChronologicalLaw_eq (σ : BehavioralPolicy (system M D))
    (N t : ℕ) (h : TraceHistory C n) (y : Fin n) :
    typedChronologicalLaw M D σ N t h y = chronologicalLaw (system M D) σ N t h y := by
  simp only [typedChronologicalLaw, chronologicalLaw, typedTraceMass_eq]

noncomputable def typedTraceExpectation {Q : Type*} (monitor : Monitor C n Q)
    (σ : BehavioralPolicy (system M D)) (N : ℕ) (y : Fin n) : ℝ :=
  ((traceWords C n N).map (fun xs => typedTraceMass M D σ 0 (y,[]) y xs *
    (monitor.reward (run monitor 0 y (monitor.initial y) xs).1
      (run monitor 0 y (monitor.initial y) xs).2 : ℝ))).sum

theorem typedTraceExpectation_eq {Q : Type*} (monitor : Monitor C n Q)
    (σ : BehavioralPolicy (system M D)) (N : ℕ) (y : Fin n) :
    typedTraceExpectation M D monitor σ N y =
      traceExpectation (system M D) monitor σ N 0 (y,[]) y (monitor.initial y) := by
  simp only [typedTraceExpectation, traceExpectation, typedTraceMass_eq]

/-- D-MONITOR's actual upper bound and history-adapted attainer transport to
the typed block law, with precisely the same observation and control timing. -/
theorem adaptive_block_optimal_and_attained {Q : Type*}
    (monitor : Monitor C n Q) (N : ℕ) (y : Fin n) :
    (∀ σ : BehavioralPolicy (system M D),
      typedTraceExpectation M D monitor σ N y ≤
        (value (system M D) monitor N 0 y (monitor.initial y) : ℝ)) ∧
    (∃ σ : BehavioralPolicy (system M D),
      typedTraceExpectation M D monitor σ N y =
        (value (system M D) monitor N 0 y (monitor.initial y) : ℝ)) := by
  simp_rw [typedTraceExpectation_eq]
  exact monitor_optimal_and_attained (system M D) monitor N y

end PermanssonResearch.ReverseSolver.AdaptiveGrammarControl
