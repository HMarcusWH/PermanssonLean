import PermanssonResearch.MultipleLimit.UniformClassEntry
import PermanssonResearch.MultipleLimit.CanonicalKernelMarginals
import PermanssonResearch.MultipleLimit.GenericNoHitNull
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

/-!
# Lane C2 — unconditional canonical almost-sure recurrent-union hitting

This is the complete genuine Markov-chain implication for *entry into
some closed recurrent communicating class*, for arbitrary finite
homogeneous probability kernels on nonempty, discrete measurable
state types, with no periodicity or rationality restriction.

The proof composes:
  genuine positive kernel-power support,
  finite graph terminal-class decomposition,
  closed-set monotonicity and a uniform finite-block entrance bound,
  the authentic infinite Ionescu–Tulcea time-n marginals,
  the canonical Markov semigroup geometric survival theorem,
  geometric no-hit -> a.s. hitting,
  the fully proved arbitrary-initial-law canonical mixture theorem.

This theorem is NOT the separate claim that occupations converge a.s.
to their class stationary law. Random class choice and subsequent a.s.
classwise occupation convergence remain forthcoming.
-/

open Filter MeasureTheory ProbabilityTheory Finset
open scoped ENNReal Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace CanonicalClassEntry

open KernelCommunication
open RecurrentClassDecomposition
open UniformClassEntry
open CanonicalKernelMarginals
open FiniteCanonicalPath
open GenericNoHitNull

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y]
variable [Nonempty Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

private theorem recurrent_measurable :
    MeasurableSet (RecurrentStates K) :=
  (Set.toFinite (RecurrentStates K)).measurableSet

/-- For every fixed finite Markov kernel, the complement of its
recurrent-class union has a genuine common finite-block survival
probability q < 1, derived from that kernel's transition powers. -/
theorem exists_geometric_recurrent_block :
    ∃ N : ℕ, ∃ q : ℝ≥0∞, q < 1 ∧
      (∀ z ∈ RecurrentStates K,
        (K ^ N) z (RecurrentStates K)ᶜ = 0) ∧
      (∀ z ∉ RecurrentStates K,
        (K ^ N) z (RecurrentStates K)ᶜ ≤ q) := by
  classical
  obtain ⟨N, ε, hε, hbound⟩ := exists_uniform_positive_recurrent_block K
  let A := RecurrentStates K
  have hA : MeasurableSet A := recurrent_measurable K
  let q : ℝ≥0∞ := 1 - ε
  have hq : q < 1 := by
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hε.ne'
  refine ⟨N, q, hq, ?_, ?_⟩
  · intro z hz
    letI : IsMarkovKernel (K ^ N) := inferInstance
    have hmono := closedKernel_power_mass_monotone K A
      (recurrentStates_closed K) z
    have hzero : (K ^ 0) z A = 1 := by
      change (Kernel.id : Kernel Y Y) z A = 1
      rw [Kernel.id_apply]
      simp [Measure.dirac_apply' _ hA, hz]
    have hunit : (K ^ N) z A = 1 :=
      le_antisymm (prob_le_one) (hzero ▸ hmono (Nat.zero_le N))
    rw [prob_compl_eq_one_sub hA, hunit]
    simp
  · intro z hz
    letI : IsMarkovKernel (K ^ N) := inferInstance
    exact prob_compl_le_one_sub_of_le_prob (hbound z) hA

/-- The original Ionescu–Tulcea infinite path law, started at ANY
finite state, almost surely enters the recurrent-class union.
No graph-to-path or mean-to-a.s. gap is present. -/
theorem canonical_point_ae_enters_recurrent
    (y : Y) :
    ∀ᵐ w ∂canonicalPathLaw K (Measure.dirac y),
      ∃ n : ℕ, w n ∈ RecurrentStates K := by
  obtain ⟨N, q, hq, hinside, houtside⟩ :=
    exists_geometric_recurrent_block K
  have hA := recurrent_measurable K
  have hMarginal :
      ∀ n : ℕ,
        (canonicalPathLaw K (Measure.dirac y)).map
          (fun w : ℕ → Y => w n) = (K ^ n) y :=
    canonical_eval_eq_kernel_pow K y
  have htail :=
    KernelCanonicalBlockBridge.canonical_geometric_noHit
      K (canonicalPathLaw K (Measure.dirac y)) y
      (RecurrentStates K) hA hMarginal N q hinside houtside
  exact ae_eventually_hits_of_geometric
    (canonicalPathLaw K (Measure.dirac y))
    (RecurrentStates K) N q hq htail

private theorem measurable_neverHit_recurrent :
    MeasurableSet (NeverHit (RecurrentStates K) : Set (ℕ → Y)) := by
  have hset :
      (NeverHit (RecurrentStates K) : Set (ℕ → Y)) =
        ⋂ n : ℕ, (fun w : ℕ → Y => w n) ⁻¹'
          (RecurrentStates K)ᶜ := by
    ext w
    simp [NeverHit]
  rw [hset]
  exact MeasurableSet.iInter (fun n =>
    (recurrent_measurable K).compl.preimage (measurable_pi_apply n))

/-- The **same genuine canonical infinite Markov chain** started from
EVERY initial probability measure almost surely hits the recurrent union.
No reliance on initial Dirac starts remains in the headline theorem. -/
theorem canonical_ae_enters_recurrent
    (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      ∃ n : ℕ, w n ∈ RecurrentStates K := by
  have hpoint : ∀ y : Y,
      (canonicalPathLaw K (Measure.dirac y))
        (NeverHit (RecurrentStates K)) = 0 := by
    intro y
    have h := canonical_point_ae_enters_recurrent K y
    rw [ae_iff] at h
    simpa [NeverHit] using h
  have hmass :
      (canonicalPathLaw K μ.toMeasure)
        (NeverHit (RecurrentStates K)) = 0 := by
    rw [canonicalPathLaw_initial_mixture K μ]
    simp [Measure.finsetSum_apply, Measure.smul_apply, hpoint]
  rw [ae_iff]
  simpa [NeverHit] using hmass

/-- The generic theorem applies immediately to the TRUE original
strategic-world alpha/P/U path measure, when its joint state space is
finite and discrete: only its existing induced Markov property is used.
No specially engineered rational surrogate is required. -/
theorem typed_ae_enters_recurrent
    {S X A : Type*} [MeasurableSpace S] [MeasurableSpace X]
    [MeasurableSpace A] [Fintype (PermanssonLean.JointState S X)]
    [MeasurableSingletonClass (PermanssonLean.JointState S X)]
    [Nonempty (PermanssonLean.JointState S X)]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (μ : ProbabilityMeasure (PermanssonLean.JointState S X)) :
    ∀ᵐ w ∂M.pathLaw μ.toMeasure,
      ∃ n : ℕ, w n ∈ RecurrentStates M.inducedKernel := by
  letI : IsMarkovKernel M.inducedKernel :=
    PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov M
  rw [FiniteCanonicalPath.typed_pathLaw_eq_canonical M μ.toMeasure]
  exact canonical_ae_enters_recurrent M.inducedKernel μ

end CanonicalClassEntry
end MultipleLimit
end PermanssonResearch
