import PermanssonResearch.ReverseSolver.MonitorHistoryBridge

/-!
# Exact capped-streak monitor for retryable residence

`m` counts transitions after entry, so a success contains `m+1` target
observations. The monitor remembers success permanently while the physical
kernel continues running. The proof identifies its language with a literal
contiguous target block in the observed word.
-/

namespace PermanssonResearch.ReverseSolver.FiniteMonitor

open HistoryDependent
open PermanssonLean.ProbabilitySupport

variable {Y : Type*} (G : Y → Prop) [DecidablePred G]

private theorem hasRun_reverse (r : ℕ) (xs : List Y) :
    Residence.hasRun G r xs.reverse = Residence.hasRun G r xs := by
  apply Bool.eq_iff_iff.mpr
  simp only [Residence.hasRun_iff_block]
  constructor
  · rintro ⟨pre, block, post, he, hl, ha⟩
    refine ⟨post.reverse, block.reverse, pre.reverse, ?_, by simpa, ?_⟩
    · have hh := congrArg List.reverse he
      simpa [List.reverse_append, List.append_assoc] using hh
    · intro z hz
      exact ha z (by simpa using hz)
  · rintro ⟨pre, block, post, he, hl, ha⟩
    refine ⟨post.reverse, block.reverse, pre.reverse, ?_, by simpa, ?_⟩
    · simpa [he, List.reverse_append, List.append_assoc]
    · intro z hz
      exact ha z (by simpa using hz)

private theorem hasRun_snoc (r : ℕ) (xs : List Y) (z : Y) :
    Residence.hasRun G r (xs ++ [z]) =
      (Residence.startsRun G r (z :: xs.reverse) || Residence.hasRun G r xs) := by
  rw [← hasRun_reverse G r (xs ++ [z])]
  simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
    Residence.hasRun, hasRun_reverse]

/-- The capped streak has precisely `m+2` possible values, including zero. -/
abbrev ResidenceState (m : ℕ) := Fin (m+2) × Bool

def residenceStep (m : ℕ) (q : ResidenceState m) (z : Y) : ResidenceState m :=
  let k : Fin (m+2) := if G z then ⟨min (m+1) (q.1.val+1), by omega⟩ else 0
  (k, q.2 || decide (k.val=m+1))

def residenceScan (m : ℕ) (xs : List Y) : ResidenceState m :=
  xs.foldl (residenceStep G m) (0,false)

/-- The state stores the capped trailing target suffix and exactly the
completed-block predicate; no event is defined by its evaluator. -/
theorem residenceScan_invariant (m : ℕ) (xs : List Y) :
    (residenceScan G m xs).1.val =
      min (m+1) (Residence.leadingResidence G xs.reverse) ∧
    (residenceScan G m xs).2 = Residence.hasRun G (m+1) xs := by
  induction xs using List.reverseRecOn with
  | nil => simp [residenceScan, Residence.leadingResidence, Residence.hasRun,
      Residence.startsRun]
  | append_singleton xs z ih =>
      have hstep : residenceScan G m (xs ++ [z]) =
          residenceStep G m (residenceScan G m xs) z := by
        simp [residenceScan, List.foldl_append]
      rw [hstep, hasRun_snoc]
      constructor
      · by_cases hz : G z
        · simp only [residenceStep, hz, if_true, List.reverse_append,
            List.reverse_singleton, List.singleton_append, Residence.leadingResidence]
          rw [ih.1]
          omega
        · simp [residenceStep, hz, Residence.leadingResidence]
      · have hflag : decide ((residenceStep G m (residenceScan G m xs) z).1.val=m+1) =
            Residence.startsRun G (m+1) (z::xs.reverse) := by
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq, Residence.startsRun_iff_leading]
          by_cases hz : G z
          · simp only [residenceStep, hz, ite_true, Residence.leadingResidence, ih.1]
            omega
          · simp [residenceStep, hz, Residence.leadingResidence]
        change ((residenceScan G m xs).2 ||
          decide ((residenceStep G m (residenceScan G m xs) z).1.val=m+1)) = _
        rw [ih.2, hflag, Bool.or_comm]

/-- Literal contiguous-block equivalence for the compact monitor. -/
theorem residenceScan_success_iff_block (m : ℕ) (xs : List Y) :
    (residenceScan G m xs).2 = true ↔
      ∃ pre block post, xs = pre ++ block ++ post ∧
        block.length=m+1 ∧ ∀ z ∈ block, G z := by
  rw [(residenceScan_invariant G m xs).2, Residence.hasRun_iff_block]

def compactResidenceMonitor {n : ℕ} (G : Fin n → Prop) [DecidablePred G]
    (m : ℕ) : ObservationMonitor n (ResidenceState m) where
  initial y := residenceStep G m (0,false) y
  update _ q z := residenceStep G m q z
  accept q := q.2

/-- The online state reconstructed from an actual prefix is exactly its scan. -/
theorem compactResidence_summary {n i : ℕ} (G : Fin n → Prop) [DecidablePred G]
    (m : ℕ) (h : History n i) :
    summary (compactResidenceMonitor G m) i h = residenceScan G m (Residence.historyWord h) := by
  induction i with
  | zero =>
      simp [summary, compactResidenceMonitor, residenceScan, Residence.historyWord,
        last, stepsFromHistory, List.ofFn_zero]
  | succ i ih =>
      rw [summary]
      rw [ih]
      have hw : Residence.historyWord h =
          Residence.historyWord (observedPrefix h i i.le_succ) ++ [last h] := by
        unfold Residence.historyWord
        rw [stepsFromHistory_snoc]
        rfl
      rw [hw]
      simp [residenceScan, List.foldl_append, compactResidenceMonitor]

/-- At the original horizon `T+m`, compact success is exactly the accepted
literal entry-by-`T` event, with retries and time-zero observations included. -/
theorem compactResidence_event_eq {n : ℕ} (G : Fin n → Prop) [DecidablePred G]
    (m T : ℕ) : monitorEvent (compactResidenceMonitor G m) (T+m) =
      Residence.entryByResidenceEvent G m T := by
  ext h
  change (summary (compactResidenceMonitor G m) (T+m) h).2 = true ↔ _
  rw [compactResidence_summary, (residenceScan_invariant G m (Residence.historyWord h)).2]
  rfl

theorem residence_time_zero_and_zero_duration :
    (residenceScan (fun z : Bool => z=true) 0 [true]).2=true ∧
    (residenceScan (fun z : Bool => z=true) 0 [false]).2=false := by decide

theorem residence_success_survives_physical_exit :
    (residenceScan (fun z : Bool => z=true) 1 [true,true,false]).1.val=0 ∧
    (residenceScan (fun z : Bool => z=true) 1 [true,true,false]).2=true := by decide

end PermanssonResearch.ReverseSolver.FiniteMonitor
