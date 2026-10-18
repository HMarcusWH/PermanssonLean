import PermanssonResearch.Probability.SummableTransportLimit
import Mathlib.Analysis.SpecificLimits.Normed

/-! Completeness of the actual first-moment transport metric on a complete
separable Borel metric space, using constructed countable coupling gluing. -/

open MeasureTheory Filter TopologicalSpace
open scoped Topology
namespace PermanssonResearch.Probability.FirstMomentProbability
set_option autoImplicit false

variable {Y : Type*} [MetricSpace Y] [CompleteSpace Y] [MeasurableSpace Y]
variable [BorelSpace Y] [SeparableSpace Y] {y₀ : Y}

theorem exists_coupling_cost_lt {μ ν : FirstMomentProbability y₀} {b : ℝ}
    (h : dist μ ν < b) : ∃ γ : IntegrableCoupling μ.measure ν.measure, γ.cost < b := by
  obtain ⟨η⟩ := firstMoment_coupling_nonempty μ.measure ν.measure y₀ μ.firstMoment ν.firstMoment
  have hne : (couplingCosts μ.measure ν.measure).Nonempty := ⟨η.cost,η,rfl⟩
  obtain ⟨c,⟨γ,rfl⟩,hc⟩ := exists_lt_of_csInf_lt hne h
  exact ⟨γ,hc⟩

theorem cauchySeq_has_limit (μ : ℕ → FirstMomentProbability y₀) (hμ : CauchySeq μ) :
    ∃ ν : FirstMomentProbability y₀, Tendsto μ atTop (𝓝 ν) := by
  classical
  obtain ⟨f,hf,hbound⟩ := Metric.exists_subseq_bounded_of_cauchySeq μ hμ
    (fun n => (1/2 : ℝ)^n) (fun n => pow_pos (by norm_num) n)
  have hstep (n : ℕ) : dist (μ (f n)) (μ (f (n+1))) < (1/2 : ℝ)^n := by
    rw [dist_comm]
    exact hbound n (f (n+1)) (hf.monotone (Nat.le_succ n))
  choose γ hγ using fun n => exists_coupling_cost_lt (hstep n)
  have hgeom : Summable (fun n : ℕ => (1/2 : ℝ)^n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hs : Summable (fun n => (γ n).cost) :=
    Summable.of_nonneg_of_le (fun n => (γ n).cost_nonneg) (fun n => (hγ n).le) hgeom
  obtain ⟨ν,_,hν⟩ := exists_limit_of_summable_couplings (fun n => μ (f n)) γ hs
  exact ⟨ν,tendsto_nhds_of_cauchySeq_of_subseq hμ hf.tendsto_atTop hν⟩

noncomputable instance completeSpace : CompleteSpace (FirstMomentProbability y₀) :=
  Metric.complete_of_cauchySeq_tendsto cauchySeq_has_limit

end PermanssonResearch.Probability.FirstMomentProbability
