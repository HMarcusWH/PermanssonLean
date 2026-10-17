import PermanssonResearch.Quotient.ApproxPrefix
import Mathlib.Tactic

/-!
# E1.4 — approximate-quotient adversaries (Lean witnesses)

**Leakage (spec §7 destructive example, AQ3).** On `Y = Q = Bool` with the identity
quotient, the fine kernel `K(y,·) = δ_false` and the coarse kernel
`K̄_ε(y,·) = (1−ε)δ_false + εδ_true` have one-step quotient defect at most `ε`
(`leaky_hasQuotientDefect`), for every `ε ∈ [0,1]`. Yet `{false}` is exactly
invariant for `K` and NOT invariant for `K̄_ε` whenever `ε > 0`
(`fine_region_invariant`, `coarse_region_leaks`). What is PROVED here is
kernel-level: arbitrarily small quotient defect does not transfer exact
one-step invariance of a region. Since `IsExactGeneratedRegime` requires
`IsExactlyInvariant`, this blocks any inference from small defect to Exact-GR
or PR status — but that last step is an interpretation, not a Lean theorem over
`StrategicWorldModel`/`IsExactGeneratedRegime` (none is provided here). The
finite-prefix margin statements of E1.2–E1.3 are unaffected.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.Quotient.Adversaries

set_option autoImplicit false

open PermanssonLean.ProbabilitySupport PermanssonResearch.Probability

/-- `(1−ε)δ_false + εδ_true`. -/
noncomputable def leakyLaw (ε : ℝ) : Measure Bool :=
  ENNReal.ofReal (1 - ε) • Measure.dirac false + ENNReal.ofReal ε • Measure.dirac true

theorem leakyLaw_isProbability {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    IsProbabilityMeasure (leakyLaw ε) := by
  constructor
  simp only [leakyLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) h0]
  simp

/-- Fine kernel: always jump to `false`. -/
noncomputable def fineKernel : Kernel Bool Bool := Kernel.const Bool (Measure.dirac false)

instance fineKernel_isMarkov : IsMarkovKernel fineKernel := by
  unfold fineKernel; infer_instance

/-- Coarse kernel: leak to `true` with probability `ε`. -/
noncomputable def leakyKernel (ε : ℝ) : Kernel Bool Bool := Kernel.const Bool (leakyLaw ε)

theorem leakyKernel_isMarkov {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    IsMarkovKernel (leakyKernel ε) := by
  haveI := leakyLaw_isProbability h0 h1
  unfold leakyKernel; infer_instance

/-- Event-wise comparison of `δ_false` and the leaky law. -/
theorem dirac_false_le_leaky {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (s : Set Bool) :
    Measure.dirac false s ≤ leakyLaw ε s + ENNReal.ofReal ε ∧
      leakyLaw ε s ≤ Measure.dirac false s + ENNReal.ofReal ε := by
  have hsum : ENNReal.ofReal (1 - ε) + ENNReal.ofReal ε = 1 := by
    rw [← ENNReal.ofReal_add (by linarith) h0]; simp
  have hle1 : ENNReal.ofReal (1 - ε) ≤ 1 := by
    rw [← hsum]; exact le_self_add
  simp only [leakyLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (Set.Finite.measurableSet (Set.toFinite s))]
  have hle1' : ENNReal.ofReal (1 - ε) ≤ ENNReal.ofReal ε + 1 :=
    hle1.trans le_add_self
  by_cases hf : false ∈ s <;> by_cases ht : true ∈ s <;>
    simp [hf, ht, Set.indicator, hsum, hle1', add_comm, le_add_right]

/-- **Small defect.** The identity-quotient defect between `K` and `K̄_ε` is ≤ ε. -/
theorem leaky_hasQuotientDefect {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    HasQuotientDefect id fineKernel (leakyKernel ε) ε := by
  haveI := leakyLaw_isProbability h0 h1
  intro y
  have hmap : (fineKernel y).map id = Measure.dirac false := by
    simp [fineKernel, Measure.map_id]
  rw [hmap]
  change eventTotalVariation (Measure.dirac false) (leakyLaw ε) ≤ ε
  exact eventTotalVariation_le_of_forall _ _ h0 fun s _ => dirac_false_le_leaky h0 h1 s

/-- `{false}` is exactly invariant for the fine kernel. -/
theorem fine_region_invariant (y : Bool) :
    fineKernel y {false}ᶜ = 0 := by
  simp [fineKernel]

/-- `{false}` is NOT invariant for the coarse kernel for any `ε > 0`. -/
theorem coarse_region_leaks {ε : ℝ} (hpos : 0 < ε) (y : Bool) :
    leakyKernel ε y {false}ᶜ = ENNReal.ofReal ε ∧ leakyKernel ε y {false}ᶜ ≠ 0 := by
  have hc : ({false}ᶜ : Set Bool) = {true} := by
    ext b; cases b <;> simp
  have hval : leakyKernel ε y {false}ᶜ = ENNReal.ofReal ε := by
    rw [hc]
    simp [leakyKernel, leakyLaw, Measure.add_apply, Measure.smul_apply]
  exact ⟨hval, by rw [hval]; exact (ENNReal.ofReal_pos.mpr hpos).ne'⟩

/-- **Firewall.** For every `ε ∈ (0,1]`, the identity-quotient pair
`(fineKernel, leakyKernel ε)` has defect `≤ ε`, the fine region `{false}` is
one-step invariant, and from every state the coarse model leaves it in one step
with probability exactly `ε` (in particular `≠ 0`). -/
theorem small_defect_does_not_preserve_invariance {ε : ℝ} (hpos : 0 < ε) (h1 : ε ≤ 1) :
    HasQuotientDefect id fineKernel (leakyKernel ε) ε ∧
      (∀ y, fineKernel y {false}ᶜ = 0) ∧
      (∀ y, leakyKernel ε y {false}ᶜ = ENNReal.ofReal ε ∧
        leakyKernel ε y {false}ᶜ ≠ 0) :=
  ⟨leaky_hasQuotientDefect hpos.le h1, fine_region_invariant,
    fun y => coarse_region_leaks hpos y⟩

end PermanssonResearch.Quotient.Adversaries
