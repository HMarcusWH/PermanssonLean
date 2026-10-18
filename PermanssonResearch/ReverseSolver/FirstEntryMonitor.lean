import PermanssonResearch.ReverseSolver.CompactResidenceMonitor

/-!
# First-ever entry residence, with permanent failure after an early exit

This is a distinct finite language from retryable residence. Counts in the
active phase range from one through `m`; `m+1` observations complete success.
-/

namespace PermanssonResearch.ReverseSolver.FiniteMonitor

open HistoryDependent
open PermanssonLean.ProbabilitySupport

variable {Y : Type*} (G : Y → Prop) [DecidablePred G]

inductive FirstState (m : ℕ) where
  | waiting
  | active (count : Fin m)
  | failed
  | succeeded
  deriving DecidableEq, Fintype

def firstStep (T m t : ℕ) : FirstState m → Y → FirstState m
  | .failed, _ => .failed
  | .succeeded, _ => .succeeded
  | .waiting, z =>
      if t ≤ T then
        if G z then if hm : m=0 then .succeeded else .active ⟨0, by omega⟩
        else .waiting
      else .failed
  | .active k, z =>
      if G z then if hk : k.val+1=m then .succeeded
        else .active ⟨k.val+1, by omega⟩
      else .failed

def firstRun (T m : ℕ) : ℕ → FirstState m → List Y → FirstState m
  | _, q, [] => q
  | t, q, z::xs => firstRun T m (t+1) (firstStep G T m t q z) xs

/-- Independently specified first-entry test. On the first target observation,
the initial run must complete; no later entry is considered. -/
def firstEntryTest (T r : ℕ) : ℕ → List Y → Bool
  | _, [] => false
  | t, z::xs => if t ≤ T then
      if G z then Residence.startsRun G r (z::xs) else firstEntryTest T r (t+1) xs
    else false

def firstCompletion (T m : ℕ) (t : ℕ) : FirstState m → List Y → Bool
  | .failed, _ => false
  | .succeeded, _ => true
  | .waiting, xs => firstEntryTest G T (m+1) t xs
  | .active k, xs => Residence.startsRun G (m-k.val) xs

/-- Literal first-entry semantics: every observation before the successful
block is outside the target, and its first observation meets the deadline. -/
theorem firstEntryTest_iff_block (T m t : ℕ) (xs : List Y) :
    firstEntryTest G T (m+1) t xs = true ↔
      ∃ pre block post, xs=pre++block++post ∧ t+pre.length≤T ∧
        (∀ z ∈ pre, ¬G z) ∧ block.length=m+1 ∧ ∀ z ∈ block, G z := by
  induction xs generalizing t with
  | nil =>
      simp only [firstEntryTest, Bool.false_eq_true, false_iff]
      rintro ⟨pre, block, post, he, _, _, hl, _⟩
      have hh := congrArg List.length he
      simp only [List.length_nil, List.length_append, hl] at hh
      omega
  | cons z xs ih =>
      constructor
      · intro hh
        by_cases ht : t≤T
        · by_cases hz : G z
          · have hr : Residence.startsRun G (m+1) (z::xs)=true := by
              simpa [firstEntryTest, ht, hz] using hh
            rcases (Residence.startsRun_iff_split G (m+1) _).mp hr with
              ⟨block, post, he, hl, ha⟩
            exact ⟨[], block, post, by simpa using he, by simpa using ht,
              by simp, hl, ha⟩
          · have hr : firstEntryTest G T (m+1) (t+1) xs=true := by
              simpa [firstEntryTest, ht, hz] using hh
            rcases (ih (t+1)).mp hr with ⟨pre, block, post, he, hd, hp, hl, ha⟩
            refine ⟨z::pre, block, post, by simp [he], by simpa [Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm] using hd, ?_, hl, ha⟩
            intro y hy
            rcases List.mem_cons.mp hy with heq | hy
            · simpa [heq] using hz
            · exact hp y hy
        · simp [firstEntryTest, ht] at hh
      · rintro ⟨pre, block, post, he, hd, hp, hl, ha⟩
        have ht : t≤T := by omega
        cases pre with
        | nil =>
            have hr : Residence.startsRun G (m+1) (z::xs)=true :=
              (Residence.startsRun_iff_split G (m+1) _).mpr
                ⟨block, post, by simpa using he, hl, ha⟩
            have hz : G z := by
              by_contra hn
              have hh := (Residence.startsRun_iff_leading G (m+1) (z::xs)).mp hr
              simp [Residence.leadingResidence, hn] at hh
            simp [firstEntryTest, ht, hz, hr]
        | cons p pre =>
            have hh := List.cons.inj he
            have hz : ¬G z := by simpa [hh.1] using hp p (by simp)
            have htail : firstEntryTest G T (m+1) (t+1) xs=true := (ih (t+1)).mpr
              ⟨pre, block, post, hh.2, by simpa [Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using hd, fun y hy => hp y (by simp [hy]), hl, ha⟩
            simp [firstEntryTest, ht, hz, htail]

/-- A finite phase state recognizes exactly its independently specified
first-entry or unfinished-initial-stay continuation language. -/
theorem firstRun_correct (T m t : ℕ) (q : FirstState m) (xs : List Y) :
    decide (firstRun G T m t q xs = .succeeded) = firstCompletion G T m t q xs := by
  induction xs generalizing t q with
  | nil =>
      cases q with
      | failed => simp [firstRun, firstCompletion]
      | succeeded => simp [firstRun, firstCompletion]
      | waiting => simp [firstRun, firstCompletion, firstEntryTest]
      | active k =>
          have hk : m-k.val ≠ 0 := by omega
          cases hr : m-k.val with
          | zero => exact False.elim (hk hr)
          | succ r => simp [firstRun, firstCompletion, hr, Residence.startsRun]
  | cons z xs ih =>
      rw [firstRun, ih]
      cases q with
      | failed => simp [firstStep, firstCompletion]
      | succeeded => simp [firstStep, firstCompletion]
      | waiting =>
          by_cases ht : t ≤ T
          · by_cases hz : G z
            · by_cases hm : m=0
              · subst m; simp [firstStep, firstCompletion, firstEntryTest, ht, hz,
                  Residence.startsRun]
              · simp [firstStep, firstCompletion, firstEntryTest, ht, hz, hm,
                  Residence.startsRun]
            · simp [firstStep, firstCompletion, firstEntryTest, ht, hz]
          · simp [firstStep, firstCompletion, firstEntryTest, ht]
      | active k =>
          have hrem : m-k.val = (m-(k.val+1))+1 := by omega
          by_cases hz : G z
          · by_cases hk : k.val+1=m
            · have hr : m-k.val=1 := by omega
              simp [firstStep, firstCompletion, hz, hk, hr, Residence.startsRun]
            · simp [firstStep, firstCompletion, hz, hk, hrem, Residence.startsRun]
          · simp [firstStep, firstCompletion, hz, hrem, Residence.startsRun]

def firstEntryMonitor {n : ℕ} (G : Fin n → Prop) [DecidablePred G]
    (T m : ℕ) : ObservationMonitor n (FirstState m) where
  initial y := firstStep G T m 0 .waiting y
  update t q z := firstStep G T m (t+1) q z
  accept q := decide (q=.succeeded)

theorem firstRun_append (T m t : ℕ) (q : FirstState m) (xs ys : List Y) :
    firstRun G T m t q (xs++ys) =
      firstRun G T m (t+xs.length) (firstRun G T m t q xs) ys := by
  induction xs generalizing t q with
  | nil => simp [firstRun]
  | cons z xs ih =>
      simpa [firstRun, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (t+1) (firstStep G T m t q z)

theorem firstEntry_summary {n i : ℕ} (G : Fin n → Prop) [DecidablePred G]
    (T m : ℕ) (h : History n i) :
    summary (firstEntryMonitor G T m) i h =
      firstRun G T m 0 .waiting (Residence.historyWord h) := by
  induction i with
  | zero =>
      simp [summary, firstEntryMonitor, Residence.historyWord, last,
        stepsFromHistory, List.ofFn_zero, firstRun]
  | succ i ih =>
      rw [summary, ih]
      have hw : Residence.historyWord h =
          Residence.historyWord (observedPrefix h i i.le_succ) ++ [last h] := by
        unfold Residence.historyWord
        rw [stepsFromHistory_snoc]
        rfl
      rw [hw, firstRun_append]
      simp [firstRun, firstEntryMonitor]

/-- The phase monitor recognizes the independent first-ever-entry test on the
actual state-prefix sample space. This event allows no retry. -/
theorem firstEntry_event_eq {n : ℕ} (G : Fin n → Prop) [DecidablePred G]
    (T m N : ℕ) : monitorEvent (firstEntryMonitor G T m) N =
      {h | firstEntryTest G T (m+1) 0 (Residence.historyWord h) = true} := by
  ext h
  change decide (summary (firstEntryMonitor G T m) N h=.succeeded)=true ↔ _
  rw [firstEntry_summary, firstRun_correct]
  rfl

/-- Required regression: retryable residence succeeds after an earlier failed
visit, whereas first-ever-entry residence fails permanently. -/
theorem first_entry_retry_counterexample :
    Residence.hasRun (fun z : Bool => z=true) 2 [true,false,true,true] = true ∧
    firstEntryTest (fun z : Bool => z=true) 2 2 0 [true,false,true,true] = false ∧
    firstRun (fun z : Bool => z=true) 2 1 0 .waiting [true,false,true,true] = .failed := by
  decide

end PermanssonResearch.ReverseSolver.FiniteMonitor
