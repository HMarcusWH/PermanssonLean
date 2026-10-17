import PermanssonResearch.ReverseSolver.HistoryPolicy
import PermanssonResearch.ReverseSolver.CanonicalWordEncoding
import Mathlib.Tactic

/-!
# D2: literal finite-path residence events

`m` counts POST-ENTRY transitions: success contains `m+1` consecutive target
observations. Time zero counts. The entry is the start of ANY successful run;
failed earlier visits may be retried. First-ever-entry residence is a different
objective. `entryByResidenceEvent G m T` observes through `T+m`; it is not the
completed-by-`T` event. No physical transition is made absorbing.
-/

namespace PermanssonResearch.ReverseSolver.Residence

open HistoryDependent
set_option autoImplicit false

variable {Y : Type*} (G : Y → Prop) [DecidablePred G]

/-- A literal target block beginning at the first observation. -/
def startsRun : ℕ → List Y → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | r + 1, z :: zs => decide (G z) && startsRun r zs

/-- Search all possible entry positions, allowing retries. -/
def hasRun (r : ℕ) : List Y → Bool
  | [] => startsRun G r []
  | z :: zs => startsRun G r (z :: zs) || hasRun r zs

/-- Current leading target residence in an explicitly supplied word. -/
def leadingResidence : List Y → ℕ
  | [] => 0
  | z :: zs => if G z then leadingResidence zs + 1 else 0

/-- Largest completed target residence in the observed word, in observations.
This transparent history calculation is not a claimed compressed controller. -/
def residenceCount : List Y → ℕ
  | [] => 0
  | z :: zs => max (leadingResidence G (z :: zs)) (residenceCount zs)

theorem startsRun_iff_leading (r : ℕ) (xs : List Y) :
    startsRun G r xs = true ↔ r ≤ leadingResidence G xs := by
  induction xs generalizing r with
  | nil => cases r <;> simp [startsRun, leadingResidence]
  | cons z zs ih =>
      cases r with
      | zero => simp [startsRun]
      | succ r =>
          by_cases hz : G z <;> simp [startsRun, leadingResidence, hz, ih]

theorem hasRun_iff_count (r : ℕ) (xs : List Y) :
    hasRun G r xs = true ↔ r ≤ residenceCount G xs := by
  induction xs with
  | nil => cases r <;> simp [hasRun, startsRun, residenceCount]
  | cons z zs ih =>
      simp only [hasRun, Bool.or_eq_true, startsRun_iff_leading, ih,
        residenceCount, le_max_iff]

theorem startsRun_iff_split (r : ℕ) (xs : List Y) :
    startsRun G r xs = true ↔
      ∃ block post, xs = block ++ post ∧ block.length = r ∧ ∀ z ∈ block, G z := by
  induction r generalizing xs with
  | zero =>
      constructor
      · intro _; exact ⟨[], xs, rfl, rfl, by simp⟩
      · intro _; rfl
  | succ r ih =>
      cases xs with
      | nil =>
          simp only [startsRun, Bool.false_eq_true, false_iff]
          rintro ⟨block, post, heq, hlen, _⟩
          have := congrArg List.length heq
          simp only [List.length_nil, List.length_append, hlen] at this
          omega
      | cons z zs =>
          constructor
          · intro hs
            have hh : G z ∧ startsRun G r zs = true := by simpa [startsRun] using hs
            obtain ⟨block, post, heq, hlen, hall⟩ := (ih zs).mp hh.2
            exact ⟨z :: block, post, by simp [heq], by simp [hlen], by
              intro y hy; rcases List.mem_cons.mp hy with h | h
              · simpa [h] using hh.1
              · exact hall y h⟩
          · rintro ⟨block, post, heq, hlen, hall⟩
            cases block with
            | nil => simp at hlen
            | cons b bs =>
                have he := List.cons.inj heq
                have hb : G z := by simpa [he.1] using hall b (by simp)
                have hr : startsRun G r zs = true := (ih zs).mpr
                  ⟨bs, post, he.2, by simpa using hlen,
                    fun y hy => hall y (by simp [hy])⟩
                simp [startsRun, hb, hr]

theorem hasRun_iff_suffix (r : ℕ) (xs : List Y) :
    hasRun G r xs = true ↔
      ∃ pre tail, xs = pre ++ tail ∧ startsRun G r tail = true := by
  induction xs with
  | nil =>
      constructor
      · intro h; exact ⟨[], [], rfl, h⟩
      · rintro ⟨pre, tail, heq, h⟩
        have hp := List.append_eq_nil_iff.mp heq.symm
        simpa [hasRun, hp.2] using h
  | cons z zs ih =>
      constructor
      · intro h
        have hh : startsRun G r (z :: zs) = true ∨ hasRun G r zs = true := by
          simpa only [hasRun, Bool.or_eq_true] using h
        rcases hh with h | h
        · exact ⟨[], z :: zs, rfl, h⟩
        · obtain ⟨pre, tail, heq, hs⟩ := ih.mp h
          exact ⟨z :: pre, tail, by simp [heq], hs⟩
      · rintro ⟨pre, tail, heq, hs⟩
        change (startsRun G r (z :: zs) || hasRun G r zs) = true
        simp only [Bool.or_eq_true]
        cases pre with
        | nil =>
            have hh : tail = z :: zs := by simpa using heq.symm
            exact Or.inl (hh ▸ hs)
        | cons b bs =>
            have he := List.cons.inj heq
            exact Or.inr (ih.mpr ⟨bs, tail, he.2, hs⟩)

/-- Independent event semantics: a genuine contiguous target block, with
no reference to the residence counter or evaluator. -/
theorem hasRun_iff_block (r : ℕ) (xs : List Y) :
    hasRun G r xs = true ↔
      ∃ pre block post, xs = pre ++ block ++ post ∧
        block.length = r ∧ ∀ z ∈ block, G z := by
  rw [hasRun_iff_suffix]
  constructor
  · rintro ⟨pre, tail, heq, hs⟩
    obtain ⟨block, post, ht, hlen, hall⟩ := (startsRun_iff_split G r tail).mp hs
    exact ⟨pre, block, post, by simpa [ht, List.append_assoc] using heq, hlen, hall⟩
  · rintro ⟨pre, block, post, heq, hlen, hall⟩
    exact ⟨pre, block ++ post, by simpa [List.append_assoc] using heq,
      (startsRun_iff_split G r _).mpr ⟨block, post, rfl, hlen, hall⟩⟩

/-- Correct initialization: initial target membership contributes ONE
observation, hence zero completed post-entry transitions. -/
theorem residenceCount_singleton (z : Y) :
    residenceCount G [z] = if G z then 1 else 0 := by
  by_cases hz : G z <;> simp [residenceCount, leadingResidence, hz]

/-- The actual chronological observations, including the fixed initial point. -/
def historyWord {n i : ℕ} (h : History n i) : List (Fin n) :=
  h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le i)⟩ :: List.ofFn (stepsFromHistory i h)

@[simp] theorem historyWord_length {n i : ℕ} (h : History n i) :
    (historyWord h).length = i + 1 := by simp [historyWord]

/-- Completed-by-D residence event on the REAL finite-prefix sample space. -/
def residenceEvent {n : ℕ} (G : Fin n → Prop) [DecidablePred G] (m D : ℕ) :
    Set (History n D) := {h | hasRun G (m+1) (historyWord h) = true}

/-- Entry-by-T with m post-entry transitions observes through T+m. -/
def entryByResidenceEvent {n : ℕ} (G : Fin n → Prop) [DecidablePred G]
    (m T : ℕ) : Set (History n (T+m)) := residenceEvent G m (T+m)

theorem mem_entryByResidenceEvent_iff {n : ℕ} (G : Fin n → Prop)
    [DecidablePred G] (m T : ℕ) (h : History n (T+m)) :
    h ∈ entryByResidenceEvent G m T ↔
      ∃ pre block post, historyWord h = pre ++ block ++ post ∧
        pre.length ≤ T ∧ block.length = m+1 ∧ ∀ z ∈ block, G z := by
  change hasRun G (m+1) (historyWord h) = true ↔ _
  rw [hasRun_iff_block]
  constructor
  · rintro ⟨pre, block, post, heq, hlen, hall⟩
    have htotal := congrArg List.length heq
    simp only [historyWord_length, List.length_append, hlen] at htotal
    exact ⟨pre, block, post, heq, by omega, hlen, hall⟩
  · rintro ⟨pre, block, post, heq, _, hlen, hall⟩
    exact ⟨pre, block, post, heq, hlen, hall⟩

/-- A hit followed immediately by exit is not stay-1. -/
theorem hit_does_not_imply_stay :
    true ∈ ([false, true, false] : List Bool) ∧
      hasRun (fun z : Bool => z = true) 2 [false, true, false] = false := by
  decide

end PermanssonResearch.ReverseSolver.Residence
