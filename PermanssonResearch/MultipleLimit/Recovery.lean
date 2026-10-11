import PermanssonResearch.MultipleLimit.RandomLimit
import PermanssonResearch.GrammarRobust.BooleanOccupation
import Mathlib.Tactic

/-!
# Lane C1 — conservative recovery of the frozen one-target Exact GR

The absorbing family is not generally an Exact GR: the old specification
demands one fixed target on its whole admissible basin. Under an actual
canonical path-law a.s. eventual absorption condition AND equality of every
attained terminal descriptor law with that frozen target, the old limiting
occupation clause is recovered. The original non-convergence gates must
be independently supplied; they are not assumed away or redefined.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PermanssonResearch
namespace MultipleLimit

open PermanssonLean PermanssonLean.RegimeSpecification
open PermanssonResearch.GrammarRobust.BooleanBaseline
open PermanssonLean.PeriodicExactGR

/-- Conditional conservative recovery, with *all* original Exact GR gates
still required. The almost-sure premise concerns the actual canonical path
law of the model M, not a separate fabricated probability measure. -/
theorem recover_exactGR_of_common_absorbing_target
    (M : StrategicWorldModel Bool Bool Bool) (m : Measure Y)
    (h41 : Assumption41 M GrammarRobust.BooleanBaseline.spec m)
    (hinv : IsExactlyInvariant M GrammarRobust.BooleanBaseline.spec)
    (habs : ∀ μ : ProbabilityMeasure Y,
      IsAdmissibleInitialLaw GrammarRobust.BooleanBaseline.spec μ →
        ∀ᵐ w ∂M.pathLaw μ.toMeasure,
          ∃ a : Y, EventuallyAt w a ∧
            terminalLaw a = GrammarRobust.BooleanBaseline.target) :
    IsExactGeneratedRegime M GrammarRobust.BooleanBaseline.spec m := by
  refine ⟨canonicalProcessWellPosed M, h41, hinv, ?_⟩
  intro μ hμ
  unfold IsLimitingOccupationLaw
  change ∀ᵐ w ∂M.pathLaw μ.toMeasure,
    Tendsto
      (fun n : ℕ => empiricalOccupation
        GrammarRobust.BooleanBaseline.spec w (n+1) (Nat.succ_pos n))
      atTop (𝓝 GrammarRobust.BooleanBaseline.target)
  filter_upwards [habs μ hμ] with w hw
  rcases hw with ⟨a, ha, hν⟩
  have h := occupation_eventually_at w a ha
  have hs : (fun n : ℕ => empiricalOccupation
      GrammarRobust.BooleanBaseline.spec w (n+1) (Nat.succ_pos n)) =
    (fun n : ℕ => empiricalOccupation
      PermanssonLean.PeriodicExactGR.spec w (n+1) (Nat.succ_pos n)) := by
    funext n
    rfl
  rw [hs, ← hν]
  exact h

end MultipleLimit
end PermanssonResearch
