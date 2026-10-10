import PermanssonResearch.GrammarRobust.Refinement
import PermanssonResearch.GrammarRobust.BlockConstitution

/-!
# Lane B — genuine coarse/fine process transport

Unlike a relabeling theorem, component counts may differ.  The equality of
the expanded physical atom sets is derived from the partition refiner.
Consequently the complete typed models agree, and so do their actual induced
kernels and infinite-horizon canonical path laws.
-/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch
namespace GrammarRobust

universe uS uX uA uI uJ uF uC

theorem Coarsening.blockModel_lift_eq
    {S : Type uS} {X : Type uX} {A : Type uA}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    {IA : Type uI} {IU : Type uJ}
    {Fine : Type uF} {Coarse : Type uC}
    [Fintype IA] [Fintype IU] [DecidableEq IA] [DecidableEq IU]
    [Fintype Fine] [Fintype Coarse]
    [DecidableEq Coarse]
    [LinearOrder IA] [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU)
    {fine : PartitionGrammar IA IU Fine}
    {coarse : PartitionGrammar IA IU Coarse}
    (ρ : Coarsening fine coarse) (D : Finset Coarse) :
    blockModel M bank fine (ρ.lift D) =
      blockModel M bank coarse D := by
  exact blockModel_eq_of_expand_eq M bank fine coarse
    (ρ.lift D) D (ρ.expand_lift D)

theorem Coarsening.inducedKernel_lift_eq
    {S : Type uS} {X : Type uX} {A : Type uA}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    {IA : Type uI} {IU : Type uJ}
    {Fine : Type uF} {Coarse : Type uC}
    [Fintype IA] [Fintype IU] [DecidableEq IA] [DecidableEq IU]
    [Fintype Fine] [Fintype Coarse]
    [DecidableEq Coarse]
    [LinearOrder IA] [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU)
    {fine : PartitionGrammar IA IU Fine}
    {coarse : PartitionGrammar IA IU Coarse}
    (ρ : Coarsening fine coarse) (D : Finset Coarse) :
    (blockModel M bank fine (ρ.lift D)).inducedKernel =
      (blockModel M bank coarse D).inducedKernel := by
  rw [ρ.blockModel_lift_eq M bank D]

theorem Coarsening.pathLaw_lift_eq
    {S : Type uS} {X : Type uX} {A : Type uA}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    {IA : Type uI} {IU : Type uJ}
    {Fine : Type uF} {Coarse : Type uC}
    [Fintype IA] [Fintype IU] [DecidableEq IA] [DecidableEq IU]
    [Fintype Fine] [Fintype Coarse]
    [DecidableEq Coarse]
    [LinearOrder IA] [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU)
    {fine : PartitionGrammar IA IU Fine}
    {coarse : PartitionGrammar IA IU Coarse}
    (ρ : Coarsening fine coarse) (D : Finset Coarse)
    (μ : Measure (PermanssonLean.JointState S X)) :
    (blockModel M bank fine (ρ.lift D)).pathLaw μ =
      (blockModel M bank coarse D).pathLaw μ := by
  rw [ρ.blockModel_lift_eq M bank D]

end GrammarRobust
end PermanssonResearch
