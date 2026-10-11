import PermanssonLean.StrategicWorld.PathLaw
import PermanssonLean.Probability.FinitePrefixTV
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic

/-!
# Lane C2 — generic Ionescu–Tulcea path law and arbitrary-initial mixtures

Unlike C1's Bool×Bool witness, this module is generic in a measurable
state type Y and a genuine stationary Markov kernel K. No finite-state,
rational, irreducibility, stationarity of the initial law, or
aperiodicity hypothesis is required for the path-law construction.

The trajectory is *the actual* mathlib canonical infinite-path measure.
The point-initial finite-prefix and all-initial mixture theorems are
derived from that measure, not assumed as interfaces.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteCanonicalPath

universe uY uS uX uA
variable {Y : Type uY} [MeasurableSpace Y]

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- Generic canonical homogeneous Markov trajectory for an initial law. -/
noncomputable def canonicalPathLaw
    (K : Kernel Y Y) [IsMarkovKernel K]
    (μ : Measure Y) [IsProbabilityMeasure μ] :
    Measure (ℕ → Y) :=
  Kernel.trajMeasure μ
    (fun n => PermanssonLean.ProbabilitySupport.stationaryPrefixKernel K n)

instance canonicalPathLaw_isProbability
    (K : Kernel Y Y) [IsMarkovKernel K]
    (μ : Measure Y) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (canonicalPathLaw K μ) := by
  unfold canonicalPathLaw
  infer_instance

section PointStarts

variable [MeasurableSingletonClass Y]

/-- A Dirac-initial infinite trajectory is the canonical trajectory
kernel at the genuine time-zero singleton history. -/
theorem canonicalPathLaw_dirac_eq_traj
    (K : Kernel Y Y) [IsMarkovKernel K] (y : Y) :
    canonicalPathLaw K (Measure.dirac y) =
      Kernel.traj
        (fun n => PermanssonLean.ProbabilitySupport.stationaryPrefixKernel K n)
        0 (PermanssonLean.ProbabilitySupport.singletonPrefix y) := by
  unfold canonicalPathLaw Kernel.trajMeasure
  rw [Measure.map_dirac y]
  rw [Measure.dirac_bind (Kernel.measurable _)]
  rfl

/-- Equality of the finite-prefix marginal of the REAL infinite
canonical path measure with the existing generic finitePrefixLaw. -/
theorem canonicalPathLaw_prefix_dirac
    (K : Kernel Y Y) [IsMarkovKernel K] (y : Y) (T : ℕ) :
    (canonicalPathLaw K (Measure.dirac y)).map
      (Preorder.frestrictLe T) =
    PermanssonLean.ProbabilitySupport.finitePrefixLaw K y T := by
  rw [canonicalPathLaw_dirac_eq_traj]
  have h := Kernel.traj_map_frestrictLe_apply
    (X := fun _ : ℕ => Y)
    (κ := fun n => PermanssonLean.ProbabilitySupport.stationaryPrefixKernel K n)
    0 T (PermanssonLean.ProbabilitySupport.singletonPrefix y)
  simpa only [PermanssonLean.ProbabilitySupport.finitePrefixLaw] using h

end PointStarts

section FiniteMixture

variable [Fintype Y] [MeasurableSingletonClass Y]

/-- A genuine initial-state mixture identity for arbitrary finite Y,
arbitrary stationary Markov K, and every measurable infinite-path event.
This generalizes C1's typed Bool-specific initial-mixture calculation. -/
theorem canonicalPathLaw_event_initial_mixture
    (K : Kernel Y Y) [IsMarkovKernel K]
    (μ : ProbabilityMeasure Y)
    (E : Set (ℕ → Y)) (hE : MeasurableSet E) :
    canonicalPathLaw K μ.toMeasure E =
      ∑ y : Y, μ.toMeasure {y} *
        (canonicalPathLaw K (Measure.dirac y)) E := by
  classical
  simp_rw [canonicalPathLaw_dirac_eq_traj K]
  unfold canonicalPathLaw
  unfold Kernel.trajMeasure
  rw [Measure.bind_apply hE (Kernel.aemeasurable _)]
  rw [lintegral_map (Kernel.measurable_coe _ hE)
    ((MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Y)).symm.measurable)]
  rw [lintegral_fintype]
  apply Finset.sum_congr rfl
  intro y _
  rw [mul_comm]
  rfl

/-- Complete equality of *infinite-path measures* for any initial
probability distribution, not a statement about simulated finite words. -/
theorem canonicalPathLaw_initial_mixture
    (K : Kernel Y Y) [IsMarkovKernel K]
    (μ : ProbabilityMeasure Y) :
    canonicalPathLaw K μ.toMeasure =
      ∑ y : Y, μ.toMeasure {y} • canonicalPathLaw K (Measure.dirac y) := by
  classical
  ext E hE
  simp only [Measure.finsetSum_apply, Measure.smul_apply]
  exact canonicalPathLaw_event_initial_mixture K μ E hE

end FiniteMixture

/-- The generic stochastic-chain path law is definitionally the ORIGINAL
typed alpha/P/U strategic-world model's canonical path law at its
induced kernel. Thus no second, unverified probability space appears. -/
theorem typed_pathLaw_eq_canonical
    {S : Type uS} {X : Type uX} {A : Type uA}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (μ : Measure (PermanssonLean.JointState S X))
    [IsProbabilityMeasure μ] :
    M.pathLaw μ =
      canonicalPathLaw M.inducedKernel μ := by
  letI : IsMarkovKernel M.inducedKernel :=
    PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov M
  rfl

end FiniteCanonicalPath
end MultipleLimit
end PermanssonResearch
