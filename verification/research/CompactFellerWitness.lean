import PermanssonResearch.MultipleLimit.CompactFellerDistance

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PermanssonResearch.CompactFellerTests

noncomputable section

open MultipleLimit.CompactFeller MultipleLimit.FiniteCanonicalPath
open MultipleLimit.FiniteStateOccupation MultipleLimit.CanonicalBoundedInnovations

/-- A continuum of physical states, rather than a finite encoded chain. -/
abbrev Interval := Set.Icc (0 : ℝ) 1

def zero : Interval := ⟨0,by constructor <;> norm_num⟩
def one : Interval := ⟨1,by constructor <;> norm_num⟩

instance : Nonempty Interval := ⟨zero⟩
instance : CompactSpace Interval := isCompact_iff_compactSpace.mp isCompact_Icc

def reset : Kernel Interval Interval := Kernel.const _ (Measure.dirac zero)
instance : IsMarkovKernel reset := by unfold reset; infer_instance

def zeroLaw : ProbabilityMeasure Interval := ⟨Measure.dirac zero,by infer_instance⟩
def oneLaw : ProbabilityMeasure Interval := ⟨Measure.dirac one,by infer_instance⟩

theorem reset_feller : IsFeller reset := by
  intro f
  have he : predict reset f = (fun _ : Interval => f zero) := by
    funext y
    simp [predict,reset]
  rw [he]
  exact continuous_const

theorem reset_comp (ν : ProbabilityMeasure Interval) : reset ∘ₘ ν.toMeasure = Measure.dirac zero := by
  change ν.toMeasure.bind (fun _ => Measure.dirac zero) = _
  rw [Measure.bind_const]
  simp

/-- The general theorem applies to the actual infinite law on a nonfinite
compact state space, from every initial probability. -/
example (μ : ProbabilityMeasure Interval) :
    ∀ᵐ w ∂canonicalPathLaw reset μ.toMeasure,
      Tendsto (fun n => empiricalOccupation w (n+1) (Nat.succ_pos n)) atTop (𝓝 zeroLaw) := by
  apply empirical_unique_invariant_ae reset reset_feller μ zeroLaw
  intro ν hν
  exact ProbabilityMeasure.toMeasure_injective (hν.symm.trans (reset_comp ν))

def identityKernel : Kernel Interval Interval := Kernel.deterministic id measurable_id
instance : IsMarkovKernel identityKernel := by unfold identityKernel; infer_instance

/-- Multiple invariant physical laws cannot be replaced by a falsely
asserted single common law. -/
example : identityKernel ∘ₘ zeroLaw.toMeasure = zeroLaw.toMeasure ∧
    identityKernel ∘ₘ oneLaw.toMeasure = oneLaw.toMeasure ∧ zeroLaw ≠ oneLaw := by
  have hid (ν : ProbabilityMeasure Interval) : identityKernel ∘ₘ ν.toMeasure = ν.toMeasure := by
    rw [identityKernel,Measure.deterministic_comp_eq_map]
    simp
  refine ⟨hid zeroLaw,hid oneLaw,?_⟩
  intro h
  have hp := congrArg (fun ν : ProbabilityMeasure Interval => ν.toMeasure {zero}) h
  have hz : zero ≠ one := by intro he; have he' := congrArg Subtype.val he; norm_num [zero,one] at he'
  simpa [zeroLaw,oneLaw,hz,Ne.symm hz] using hp

end
end PermanssonResearch.CompactFellerTests
