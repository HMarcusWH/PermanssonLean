import PermanssonResearch.ReverseSolver.CanonicalVectorSuccess
import Mathlib.Tactic

/-!
# D0-C: the canonical hitting event as a finite-vector witness

This is the literal event under the frozen `successPrefixEvent` definition,
translated by the Finset.Iic T ≃ Fin(T+1) time equivalence, not a redefined
probabilistic objective.
-/

namespace PermanssonResearch
namespace ReverseSolver

/-- For every finite indexed history, successPrefixEvent is exactly a
goal-time witness with no forbidden visit at any strictly earlier time. -/
theorem successPrefixEvent_iff_vectorSuccess {n : ℕ}
    (target : RationalHittingTarget n) (T : ℕ)
    (w : ((i : Finset.Iic T) → Fin n)) :
    w ∈ successPrefixEvent (rationalTargetAsFrozen target) T ↔
      finiteVectorSuccess target T
        (fun k => w ((historyTimeEquiv T).symm k)) := by
  classical
  unfold finiteVectorSuccess successPrefixEvent
  constructor
  · intro h
    rcases Set.mem_iUnion.mp h with ⟨t, ht⟩
    rcases ht with ⟨hg, hd⟩
    refine ⟨historyTimeEquiv T t, ?_, ?_⟩
    · simpa [rationalTargetAsFrozen] using hg
    · intro u hu
      have hlt :
          (((historyTimeEquiv T).symm u : Finset.Iic T) : ℕ) < (t : ℕ) := by
        simpa [historyTimeEquiv] using hu
      have hnot := (Set.mem_iInter.mp hd) ((historyTimeEquiv T).symm u)
      simpa [rationalTargetAsFrozen] using hnot hlt
  · rintro ⟨t, hg, hd⟩
    refine Set.mem_iUnion.mpr
      ⟨(historyTimeEquiv T).symm t, ?_⟩
    refine ⟨?_, Set.mem_iInter.mpr ?_⟩
    · simpa [rationalTargetAsFrozen] using hg
    · intro u
      change ((u : ℕ) < ((historyTimeEquiv T).symm t : ℕ)) →
        w u ∉ (rationalTargetAsFrozen target).forbidden
      intro hu
      have hlt : historyTimeEquiv T u < t := by
        simpa [historyTimeEquiv] using hu
      simpa [rationalTargetAsFrozen] using hd (historyTimeEquiv T u) hlt

/-- Under the fixed-start encoding the canonical event is the same
finite-vector event, including the initial state. -/
theorem successPrefixEvent_historyFromSteps_iff {n : ℕ}
    (target : RationalHittingTarget n) (T : ℕ)
    (y : Fin n) (steps : Fin T → Fin n) :
    historyFromSteps T y steps ∈
      successPrefixEvent (rationalTargetAsFrozen target) T ↔
    finiteVectorSuccess target T (Fin.cons y steps) := by
  simpa [historyFromSteps] using
    (successPrefixEvent_iff_vectorSuccess target T
      (historyFromSteps T y steps))

end ReverseSolver
end PermanssonResearch
