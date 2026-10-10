import PermanssonResearch.ReverseSolver.HistoryStatusBridge
import PermanssonResearch.ReverseSolver.HistoryPathAtoms
import Mathlib.Tactic

/-!
# D1-D1: independent continuation weights equal genuine rational history atoms

The fold carries the dependent observed prefix as its state. It consumes
exactly the successors that appear in a genuine time-zero-anchored history;
at every step the policy receives the same original deadline and past.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace HistoryDependent

open Bellman ControlledKernel
open PermanssonLean.ProbabilitySupport
universe uC

/-- A state prefix packaged with its actual elapsed time. -/
abbrev PackedHistory (n : ℕ) := Σ i : ℕ, History n i

/-- One exact forward step on an observed-prefix/weight accumulator. -/
def packedStep {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys) (D : ℕ)
    (p : PackedHistory n × ℚ) (z : Fin n) : PackedHistory n × ℚ :=
  (⟨p.1.1 + 1, appendHistory p.1.2 z⟩,
    p.2 * selectedEntry sys σ D p.1.1 p.1.2 z)

/-- The independent completionMass equals the weight accumulated by the
explicitly chronological prefix state machine on each successor list. -/
theorem packed_mass_eq_completion
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys) (D : ℕ) :
    ∀ (xs : List (Fin n)) (i : ℕ) (h : History n i) (q : ℚ),
      ((xs.foldl (packedStep sys σ D) (⟨⟨i, h⟩, q⟩))).2 =
      q * completionMass sys σ D i h xs := by
  intro xs
  induction xs with
  | nil =>
      intro i h q
      simp [completionMass]
  | cons z zs ih =>
      intro i h q
      simp only [List.foldl_cons]
      change ((zs.foldl (packedStep sys σ D)
        (⟨⟨i+1, appendHistory h z⟩,
          q * selectedEntry sys σ D i h z⟩))).2 = _
      rw [ih (i+1) (appendHistory h z)
          (q * selectedEntry sys σ D i h z)]
      simp [completionMass, mul_assoc]

/-- Extracting the last successor commutes with the preceding prefix. -/
theorem stepsFromHistory_snoc {n t : ℕ}
    (w : History n (t+1)) :
    List.ofFn (stepsFromHistory (t+1) w) =
      List.ofFn (stepsFromHistory t
        (observedPrefix w t t.le_succ)) ++
      [w ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩] := by
  rw [List.ofFn_succ']
  have hfirst : (fun j : Fin t =>
        stepsFromHistory (t+1) w j.castSucc) =
        stepsFromHistory t (observedPrefix w t t.le_succ) := by
    funext j
    rfl
  have hlast : stepsFromHistory (t+1) w (Fin.last t) =
      w ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩ := rfl
  rw [hfirst, hlast, List.concat_eq_append]

/-- Prefix and its actual final successor reconstruct the whole history. -/
theorem appendHistory_reconstruct {n t : ℕ}
    (w : History n (t+1)) :
    appendHistory (observedPrefix w t t.le_succ)
      (w ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩) = w := by
  funext j
  by_cases hj : (j : ℕ) ≤ t
  · simp [appendHistory, observedPrefix, hj]
  · have hlast : (j : ℕ) = t+1 := by
      have hb := Finset.mem_Iic.mp j.property
      omega
    have heq : j = ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩ :=
      Subtype.ext hlast
    simp [appendHistory, heq]

/-- Folding actual successors recovers the full history and path product. -/
theorem packed_fold_eq_rationalPathWeight
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys) (D : ℕ) :
    ∀ (t : ℕ) (w : History n t),
      (List.ofFn (stepsFromHistory t w)).foldl (packedStep sys σ D)
        (⟨⟨0, singletonPrefix
          (w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le t)⟩)⟩, 1⟩) =
      (⟨⟨t, w⟩, rationalPathWeight sys σ D t w⟩) := by
  intro t
  induction t with
  | zero =>
      intro w
      have hw : singletonPrefix
          (w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 0)⟩) = w := by
        funext j
        have hj : j = ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 0)⟩ := by
          apply Subtype.ext
          exact Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp j.property)
        simp [singletonPrefix, hj]
      simp [List.ofFn_zero, rationalPathWeight, hw]
  | succ t ih =>
      intro w
      let pre := observedPrefix w t t.le_succ
      have hstart : (w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le (t+1))⟩) =
          pre ⟨0, Finset.mem_Iic.mpr (Nat.zero_le t)⟩ := rfl
      rw [stepsFromHistory_snoc, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [hstart, ih pre]
      rw [rationalPathWeight_succ]
      have hrec : appendHistory pre (w ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩) = w :=
        appendHistory_reconstruct w
      simp [packedStep, pre, hrec]
      rfl

/-- Independent forward successor-word weight equals genuine path atom. -/
theorem completionMass_eq_rationalPathWeight
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D t : ℕ) (w : History n t) :
    completionMass sys σ D 0
      (singletonPrefix (w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le t)⟩))
      (List.ofFn (stepsFromHistory t w)) =
      rationalPathWeight sys σ D t w := by
  have h := packed_mass_eq_completion sys σ D
    (List.ofFn (stepsFromHistory t w)) 0
    (singletonPrefix (w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le t)⟩)) 1
  have hp := congrArg Prod.snd
    (packed_fold_eq_rationalPathWeight sys σ D t w)
  simpa using h.symm.trans hp

end HistoryDependent
end ReverseSolver
end PermanssonResearch
