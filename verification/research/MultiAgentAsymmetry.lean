import PermanssonResearch.MultiAgent.PlayerSwapTransport

open MeasureTheory ProbabilityTheory Set PermanssonLean
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultiAgent.PlayerSwapTests

/-- Deliberately asymmetric: the physical outcome is the first player's action. -/
noncomputable def asymmetricPhysical :
    Kernel (WorldInput (GameState Unit Unit Unit) Bool (Bool × Bool)) Bool :=
  Kernel.deterministic (fun i => i.2.1) (by fun_prop)

/-- Reindexing players must reindex this INPUT. Reusing the old input would
give the opposite outcome on this test case. -/
example :
    PlayerSwap.physical asymmetricPhysical ((((),((),())),false),(false,true)) {true} = 1 ∧
      asymmetricPhysical ((((),((),())),false),(false,true)) {true} = 0 := by
  simp [PlayerSwap.physical,Kernel.comap_apply,PlayerSwap.worldInput,
    asymmetricPhysical,Kernel.deterministic_apply,Measure.dirac_apply]

end PermanssonResearch.MultiAgent.PlayerSwapTests
