import PermanssonResearch.ReverseSolver.RationalBSCC
import PermanssonResearch.ReverseSolver.RationalTypedSupportBridge
import Mathlib.Tactic

/-!
# C10 — sound executable graph paths and genuine typed transport

The Floyd–Warshall Boolean reachability evaluator cannot report a false
positive: every reported path is an authentic exact-positive-edge path.
The converse (no missing reachable paths), and equivalence of the proposed
bottom component enumeration to the native recurrent-class partition, are
separate C10 completeness obligations.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

open RationalTypedSupportBridge
open PermanssonResearch.MultipleLimit.KernelCommunication
open FiniteStrategicRealization

/-- A numerical seed is a real positive rational edge or the reflexive path. -/
private theorem reachSeed_sound {n : ℕ}
    (K : RationalMarkovMatrix n) (x z : Fin n)
    (h : reachSeed K x z = true) :
    RationalReachable K x z := by
  unfold reachSeed at h
  rcases (orB_eq_true_iff _ _).mp h with hself | hedge
  · have heq : x = z := of_decide_eq_true hself
    subst z
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single
      ((edgeB_true_iff K x z).mp hedge)

/-- Allowing one intermediate state cannot invent a path not already
present in the genuine transitive closure. -/
private theorem reachStep_sound {n : ℕ}
    (K : RationalMarkovMatrix n)
    (R : Fin n → Fin n → Bool)
    (hR : ∀ x z, R x z = true → RationalReachable K x z)
    (k x z : Fin n)
    (h : reachStep R k x z = true) :
    RationalReachable K x z := by
  unfold reachStep at h
  rcases (orB_eq_true_iff _ _).mp h with hdirect | hvia
  · exact hR x z hdirect
  · obtain ⟨hxk, hkz⟩ := Bool.and_eq_true.mp hvia
    exact Relation.ReflTransGen.trans (hR x k hxk) (hR k z hkz)

/-- Soundness survives every intermediate-vertex update in the explicit
finite Floyd–Warshall fold. -/
private theorem foldedReach_sound {n : ℕ}
    (K : RationalMarkovMatrix n) :
    ∀ (ks : List (Fin n)) (R : Fin n → Fin n → Bool),
      (∀ x z, R x z = true → RationalReachable K x z) →
      ∀ x z,
        (ks.foldl (fun R k => reachStep R k) R) x z = true →
          RationalReachable K x z := by
  intro ks
  induction ks with
  | nil =>
      intro R hR x z h
      exact hR x z (by simpa only [List.foldl_nil] using h)
  | cons k tail ih =>
      intro R hR x z h
      have hnext : ∀ a b, reachStep R k a b = true →
          RationalReachable K a b :=
        fun a b hab => reachStep_sound K R hR k a b hab
      exact ih (reachStep R k) hnext x z (by
        simpa only [List.foldl_cons] using h)

/-- Every Boolean `true` from the executable closure is a genuine
path through strictly positive rational transitions. -/
theorem reachesB_sound {n : ℕ}
    (K : RationalMarkovMatrix n) (x z : Fin n)
    (h : reachesB K x z = true) :
    RationalReachable K x z := by
  exact foldedReach_sound K (List.finRange n) (reachSeed K)
    (reachSeed_sound K) x z h

/-- No numerical support query can fabricate an alpha/P/U path in
the frozen D0 constructed strategic-world family. -/
theorem reachesB_typed_sound {n : ℕ}
    (baseline L : RationalMarkovMatrix n) (x z : Fin n)
    (h : reachesB L x z = true) :
    Reachable
      (rationalStrategicIntervention baseline L).intervention.apply.inducedKernel
      (decode x) (decode z) :=
  (rationalTyped_reachable_iff baseline L x z).mp
    (reachesB_sound L x z h)

end C10
end ReverseSolver
end PermanssonResearch