import PermanssonResearch.ReverseSolver.RationalGraphCorrectness
import Mathlib.Tactic

/-!
# C10 — Floyd–Warshall graph completeness, not just soundness

The finite Boolean reachability table has exact reflexive/transitive
closure semantics for positive rational edges. All pivots are processed;
no positive graph path is omitted because of algorithmic ordering.
This is a graph theorem, not yet the separate probabilistic Dirichlet
uniqueness or canonical class-weight theorem.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

open RationalTypedSupportBridge

/-- A single Floyd–Warshall update adds the possibility of routing
through the chosen pivot. -/
private theorem step_iff {n : ℕ}
    (R : Fin n → Fin n → Bool) (k x z : Fin n) :
    reachStep R k x z = true ↔
      R x z = true ∨ (R x k = true ∧ R k z = true) := by
  simp only [reachStep, Bool.or_eq_true, Bool.and_eq_true]

private theorem step_keeps {n : ℕ}
    (R : Fin n → Fin n → Bool) (k x z : Fin n)
    (h : R x z = true) : reachStep R k x z = true :=
  (step_iff R k x z).mpr (Or.inl h)

/-- The table knows how to compose two paths via a specified pivot. -/
private def PivotClosed {n : ℕ}
    (R : Fin n → Fin n → Bool) (pivot : Fin n) : Prop :=
  ∀ x z, R x pivot = true → R pivot z = true → R x z = true

/-- A pivot, once processed, becomes closed for two-path composition. -/
private theorem step_closes_pivot {n : ℕ}
    (R : Fin n → Fin n → Bool) (k : Fin n) :
    PivotClosed (reachStep R k) k := by
  intro x z hx hz
  have hxk : R x k = true := by
    rcases (step_iff R k x k).mp hx with hxk | hxk
    · exact hxk
    · exact hxk.1
  have hkz : R k z = true := by
    rcases (step_iff R k k z).mp hz with hkz | hkz
    · exact hkz
    · exact hkz.2
  exact (step_iff R k x z).mpr (Or.inr ⟨hxk, hkz⟩)

/-- A newly processed pivot preserves every previously processed pivot. -/
private theorem step_preserves_pivot {n : ℕ}
    (R : Fin n → Fin n → Bool) (i k : Fin n)
    (hi : PivotClosed R i) : PivotClosed (reachStep R k) i := by
  intro x z hx hz
  rcases (step_iff R k x i).mp hx with hxi | ⟨hxk, hki⟩
  · rcases (step_iff R k i z).mp hz with hiz | ⟨hik, hkz⟩
    · exact (step_iff R k x z).mpr (Or.inl (hi x z hxi hiz))
    · exact (step_iff R k x z).mpr
        (Or.inr ⟨hi x k hxi hik, hkz⟩)
  · rcases (step_iff R k i z).mp hz with hiz | ⟨hik, hkz⟩
    · exact (step_iff R k x z).mpr
        (Or.inr ⟨hxk, hi k z hki hiz⟩)
    · exact (step_iff R k x z).mpr (Or.inr ⟨hxk, hkz⟩)

/-- Every pivot in the processed list remains closed after every
subsequent table update. -/
private theorem fold_closed_pivots {n : ℕ} :
    ∀ (todo done : List (Fin n)) (R : Fin n → Fin n → Bool),
      (∀ p ∈ done, PivotClosed R p) →
      ∀ p ∈ done ++ todo,
        PivotClosed (todo.foldl (fun R k => reachStep R k) R) p := by
  intro todo
  induction todo with
  | nil =>
      intro done R hDone p hp
      exact hDone p (by simpa using hp)
  | cons k rest ih =>
      intro done R hDone p hp
      have hNext : ∀ q ∈ k :: done,
          PivotClosed (reachStep R k) q := by
        intro q hq
        rcases (List.mem_cons.mp hq) with hq | hq
        · subst q
          exact step_closes_pivot R k
        · exact step_preserves_pivot R q k (hDone q hq)
      have hMem : p ∈ (k :: done) ++ rest := by
        simp only [List.mem_append, List.mem_cons] at hp ⊢
        tauto
      simpa only [List.foldl_cons] using
        ih (k :: done) (reachStep R k) hNext p hMem

/-- The full finite Floyd table is reflexive and still contains every
one-step strictly positive edge in the original rational kernel. -/
private theorem fold_preserves {n : ℕ}
    (todo : List (Fin n)) (R : Fin n → Fin n → Bool)
    (x z : Fin n) (h : R x z = true) :
    (todo.foldl (fun R k => reachStep R k) R) x z = true := by
  induction todo generalizing R with
  | nil => simpa using h
  | cons k rest ih =>
      exact ih (reachStep R k) (step_keeps R k x z h)

theorem reachesB_refl {n : ℕ}
    (K : RationalMarkovMatrix n) (x : Fin n) :
    reachesB K x x = true :=
  fold_preserves (List.finRange n) (reachSeed K) x x
    (self_seed K x)

theorem reachesB_of_edge {n : ℕ}
    (K : RationalMarkovMatrix n) (x z : Fin n)
    (h : 0 < K.entry x z) :
    reachesB K x z = true :=
  fold_preserves (List.finRange n) (reachSeed K) x z
    (positive_seed K x z h)

/-- All n pivots occur in the explicit finite-range fold. Hence the
resulting relation is transitive in its *actual Boolean computation*. -/
theorem reachesB_trans {n : ℕ}
    (K : RationalMarkovMatrix n) (x y z : Fin n)
    (hxy : reachesB K x y = true)
    (hyz : reachesB K y z = true) :
    reachesB K x z = true := by
  have hPivot := fold_closed_pivots
    (List.finRange n) [] (reachSeed K)
    (by intro p hp; simp at hp) y (by simp)
  exact hPivot x z hxy hyz

/-- Generic complete finite-graph correctness; the reverse direction
from abstract reachability is by induction on the actual edge path. -/
theorem reachesB_complete {n : ℕ}
    (K : RationalMarkovMatrix n) (x z : Fin n)
    (h : RationalReachable K x z) :
    reachesB K x z = true := by
  induction h with
  | refl => exact reachesB_refl K _
  | @tail a b hab hedge ih =>
      exact reachesB_trans K _ _ _ ih
        (reachesB_of_edge K _ _ hedge)

/-- Full executable iff between the Boolean closure and the frozen C9
rational-path definition, with no epsilon threshold or proof oracle. -/
theorem reachesB_iff_rationalReachable {n : ℕ}
    (K : RationalMarkovMatrix n) (x z : Fin n) :
    reachesB K x z = true ↔ RationalReachable K x z :=
  ⟨reachesB_sound K x z, reachesB_complete K x z⟩

end C10
end ReverseSolver
end PermanssonResearch