import PermanssonResearch.ReverseSolver.CompactResidenceMonitor
import Mathlib.Data.List.TakeWhile

/-!
# Residence completed before danger

Danger has precedence until success, including at time zero and simultaneous
target/danger observations. A later dangerous observation does not undo an
already completed target block. The physical state continues transitioning.
-/

namespace PermanssonResearch.ReverseSolver.FiniteMonitor

open HistoryDependent
open PermanssonLean.ProbabilitySupport

variable {Y : Type*} (G D : Y → Prop) [DecidablePred G] [DecidablePred D]

abbrev AvoidState (m : ℕ) := ResidenceState m × Bool

def avoidStep (m : ℕ) (q : AvoidState m) (z : Y) : AvoidState m :=
  if q.1.2 then q
  else if q.2 || decide (D z) then (q.1,true)
  else (residenceStep G m q.1 z,false)

def avoidRun (m : ℕ) : AvoidState m → List Y → AvoidState m
  | q, [] => q
  | q, z::xs => avoidRun m (avoidStep G D m q z) xs

def safePrefix (xs : List Y) : List Y := xs.takeWhile (fun z => !decide (D z))

private theorem residenceFold_success (m : ℕ) (q : ResidenceState m)
    (hq : q.2=true) (xs : List Y) : (xs.foldl (residenceStep G m) q).2=true := by
  induction xs generalizing q with
  | nil => exact hq
  | cons z xs ih =>
      apply ih
      simp [residenceStep, hq]

private theorem avoidRun_success (m : ℕ) (q : AvoidState m)
    (hq : q.1.2=true) (xs : List Y) : avoidRun G D m q xs=q := by
  induction xs with
  | nil => rfl
  | cons z xs ih => simpa [avoidRun, avoidStep, hq] using ih

private theorem avoidRun_failed (m : ℕ) (q : ResidenceState m)
    (hq : q.2=false) (xs : List Y) : avoidRun G D m (q,true) xs=(q,true) := by
  induction xs with
  | nil => rfl
  | cons z xs ih => simpa [avoidRun, avoidStep, hq] using ih

/-- The monitor reads precisely the physical observations before the first
danger, while retaining any success completed in that safe prefix. -/
theorem avoidRun_safePrefix (m : ℕ) (q : ResidenceState m) (xs : List Y) :
    (avoidRun G D m (q,false) xs).1.2 =
      ((safePrefix D xs).foldl (residenceStep G m) q).2 := by
  induction xs generalizing q with
  | nil => rfl
  | cons z xs ih =>
      by_cases hq : q.2=true
      · rw [avoidRun_success G D m (q,false) hq]
        rw [residenceFold_success G m q hq]
        exact hq
      · have hqf : q.2=false := Bool.eq_false_iff.mpr hq
        by_cases hz : D z
        · have hstep : avoidStep G D m (q,false) z=(q,true) := by
            simp [avoidStep, hqf, hz]
          rw [avoidRun, hstep, avoidRun_failed G D m q hqf]
          simp [safePrefix, hz]
        · simpa [avoidRun, avoidStep, hqf, hz, safePrefix] using
            ih (residenceStep G m q z)

/-- Independent literal event: a contiguous target block, preceded and
accompanied exclusively by safe observations. Danger after the block is free. -/
theorem safePrefix_hasRun_iff_block (m : ℕ) (xs : List Y) :
    Residence.hasRun G (m+1) (safePrefix D xs)=true ↔
      ∃ pre block post, xs=pre++block++post ∧ block.length=m+1 ∧
        (∀ z ∈ block, G z) ∧ ∀ z ∈ pre++block, ¬D z := by
  rw [Residence.hasRun_iff_block]
  constructor
  · rintro ⟨pre, block, post, he, hl, hg⟩
    let rest := xs.dropWhile (fun z => !decide (D z))
    have hx : safePrefix D xs ++ rest=xs := List.takeWhile_append_dropWhile
    refine ⟨pre, block, post++rest, ?_, hl, hg, ?_⟩
    · rw [← hx, he]
      simp [List.append_assoc]
    · intro z hz
      have hz' : z ∈ safePrefix D xs := by rw [he]; simp only [List.mem_append] at *; tauto
      have hs := List.mem_takeWhile_imp hz'
      simpa [safePrefix] using hs
  · rintro ⟨pre, block, post, he, hl, hg, hs⟩
    have hsafe : ∀ z ∈ pre++block, (!decide (D z))=true := by
      intro z hz
      simp [hs z hz]
    have hp : safePrefix D xs=(pre++block)++safePrefix D post := by
      rw [he]
      exact List.takeWhile_append_of_pos hsafe
    exact ⟨pre, block, safePrefix D post, by simpa only [List.append_assoc] using hp, hl, hg⟩

theorem avoidScan_success_iff_block (m : ℕ) (xs : List Y) :
    (avoidRun G D m ((0,false),false) xs).1.2=true ↔
      ∃ pre block post, xs=pre++block++post ∧ block.length=m+1 ∧
        (∀ z ∈ block, G z) ∧ ∀ z ∈ pre++block, ¬D z := by
  rw [avoidRun_safePrefix]
  change (residenceScan G m (safePrefix D xs)).2=true ↔ _
  rw [(residenceScan_invariant G m _).2, safePrefix_hasRun_iff_block]

def avoidResidenceMonitor {n : ℕ} (G D : Fin n → Prop)
    [DecidablePred G] [DecidablePred D] (m : ℕ) : ObservationMonitor n (AvoidState m) where
  initial y := avoidStep G D m ((0,false),false) y
  update _ q z := avoidStep G D m q z
  accept q := q.1.2

theorem danger_precedes_simultaneous_success :
    (avoidRun (fun b : Bool => b=true) (fun b : Bool => b=true)
      0 ((0,false),false) [true]).1.2=false := by decide

theorem danger_after_success_does_not_undo :
    (avoidRun (fun b : Bool => b=true) (fun b : Bool => b=false)
      0 ((0,false),false) [true,false]).1.2=true := by decide

end PermanssonResearch.ReverseSolver.FiniteMonitor
