import PermanssonResearch.Probability.LocalizedHistoryTV
import Mathlib.Tactic

/-!
Q-LOCAL next-build: a *visit-dependent* bound for actual history measures.
The defect budget is piecewise `eta` on a measurable good set and `1` elsewhere.
The bad-visit mass is measured under the left/true history distribution.
No independence, arbitrary-integrability, or baseline-only intervention premise.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.Probability

open PermanssonLean.ProbabilitySupport

variable {H Z : Type*} [MeasurableSpace H] [MeasurableSpace Z]

/-- The explicit bounded defect majorant.  Its bad-history value is one,
not an unbounded user-provided raw error estimate. -/
noncomputable def goodHistoryMajorant (E : Set H) (eta : ℝ) (h : H) : ℝ := by
  classical
  exact if h ∈ E then eta else 1

lemma goodHistoryMajorant_measurable {E : Set H} (hE : MeasurableSet E)
    (eta : ℝ) : Measurable (goodHistoryMajorant E eta) := by
  unfold goodHistoryMajorant
  classical
  exact Measurable.ite hE measurable_const measurable_const

lemma goodHistoryMajorant_nonneg {E : Set H} {eta : ℝ}
    (heta : 0 ≤ eta) (h : H) : 0 ≤ goodHistoryMajorant E eta h := by
  classical
  by_cases hh : h ∈ E <;> simp [goodHistoryMajorant, hh, heta]

/-- The majorant is normalized when the declared good-row bound is. -/
lemma goodHistoryMajorant_le_one {E : Set H} {eta : ℝ}
    (heta1 : eta ≤ 1) (h : H) : goodHistoryMajorant E eta h ≤ 1 := by
  classical
  by_cases hh : h ∈ E <;> simp [goodHistoryMajorant, hh, heta1]

/-- Elementary measurable good-history/visit estimate. It does not postulate
an averaged defect: it derives it from the two pointwise bounds and the actual
bad-visit probability of the specified source law. -/
theorem goodHistory_lintegral_le
    (mu : Measure H) [IsProbabilityMeasure mu]
    (E : Set H) (hE : MeasurableSet E)
    {eta v : ℝ} (heta : 0 ≤ eta) (hv : 0 ≤ v)
    (hvisit : mu Eᶜ ≤ ENNReal.ofReal v) :
    ∫⁻ h, ENNReal.ofReal (goodHistoryMajorant E eta h) ∂mu ≤
      ENNReal.ofReal (eta + v) := by
  classical
  have hdom (h : H) :
      ENNReal.ofReal (goodHistoryMajorant E eta h) ≤
        E.indicator (fun _ : H => ENNReal.ofReal eta) h +
          Eᶜ.indicator (fun _ : H => (1 : ℝ≥0∞)) h := by
    by_cases hh : h ∈ E
    · simp [goodHistoryMajorant, hh]
    · simp [goodHistoryMajorant, hh]
  calc
    ∫⁻ h, ENNReal.ofReal (goodHistoryMajorant E eta h) ∂mu ≤
        ∫⁻ h, (E.indicator (fun _ : H => ENNReal.ofReal eta) h +
          Eᶜ.indicator (fun _ : H => (1 : ℝ≥0∞)) h) ∂mu :=
      lintegral_mono hdom
    _ = ENNReal.ofReal eta * mu E + mu Eᶜ := by
      rw [lintegral_add_left (measurable_const.indicator hE),
        lintegral_indicator_const hE,
        lintegral_indicator_const hE.compl]
      simp
    _ ≤ ENNReal.ofReal eta + ENNReal.ofReal v := by
      have hprob : mu E ≤ (1 : ℝ≥0∞) := prob_le_one
      have hmul : ENNReal.ofReal eta * mu E ≤ ENNReal.ofReal eta * (1 : ℝ≥0∞) := by
        gcongr <;> exact hprob
      calc
        ENNReal.ofReal eta * mu E + mu Eᶜ ≤
            ENNReal.ofReal eta * 1 + mu Eᶜ := add_le_add hmul (le_refl _)
        _ ≤ ENNReal.ofReal eta * 1 + ENNReal.ofReal v :=
          add_le_add (le_refl _) hvisit
        _ = ENNReal.ofReal eta + ENNReal.ofReal v := by simp
    _ = ENNReal.ofReal (eta + v) := (ENNReal.ofReal_add heta hv).symm

/-- Given actual good-set row bounds and actual bad-visit masses, propagate
localized TV with explicit time-zero initial mismatch. -/
theorem historyEvolution_tv_le_goodVisits
    (mu nu : Measure H) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (K L : ℕ → Kernel H Z) [∀ n, IsMarkovKernel (K n)]
      [∀ n, IsMarkovKernel (L n)]
    (append : ℕ → H × Z → H) (happend : ∀ n, Measurable (append n))
    (E : ℕ → Set H) (hE : ∀ n, MeasurableSet (E n))
    (eta v : ℕ → ℝ)
    (heta : ∀ n, 0 ≤ eta n) (hv : ∀ n, 0 ≤ v n)
    (hgood : ∀ n h, h ∈ E n →
      eventTotalVariation (K n h) (L n h) ≤ eta n)
    (hbad : ∀ n, historyEvolution mu K append n (E n)ᶜ ≤
      ENNReal.ofReal (v n))
    {eps : ℝ} (heps : eventTotalVariation mu nu ≤ eps) (T : ℕ) :
    eventTotalVariation (historyEvolution mu K append T)
        (historyEvolution nu L append T) ≤
      min 1 (eps + ∑ t ∈ Finset.range T, (eta t + v t)) := by
  classical
  apply historyEvolution_tv_le_sum mu nu K L append happend
      (fun n h => goodHistoryMajorant (E n) (eta n) h)
      (fun n => goodHistoryMajorant_measurable (hE n) (eta n))
      (fun n h => goodHistoryMajorant_nonneg (heta n) h)
      (fun n => eta n + v n)
      (fun n => add_nonneg (heta n) (hv n))
      (fun n h => ?_) (fun n => ?_) heps T
  · by_cases hh : h ∈ E n
    · simpa [goodHistoryMajorant, hh] using hgood n h hh
    · simp only [goodHistoryMajorant, if_neg hh]
      exact eventTotalVariation_le_one _ _
  · letI := historyEvolution_isProbability mu K append happend n
    exact goodHistory_lintegral_le
      (historyEvolution mu K append n) (E n) (hE n)
      (heta n) (hv n) (hbad n)

end PermanssonResearch.Probability
