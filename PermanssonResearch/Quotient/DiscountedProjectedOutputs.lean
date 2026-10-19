import PermanssonResearch.Quotient.NonstationaryProjectedTransport
import PermanssonResearch.Probability.DiscountedInitialBudget
import Mathlib.Tactic

/-!
# NEXT-04 — discounted expectations of actual projected history laws

The source-to-canonical identities hP/hQ are explicit premises and must
be proved for each physical model. The underlying finite-history TV
bound is derived from actual kernels, common sublaw and initial mass,
not postulated. No projected Markov, Exact GR/PR, external identification
or original constitutive-margin inference follows from this result.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

namespace PermanssonResearch.Quotient.DiscountedProjected

open PermanssonResearch.Quotient.NonstationaryProjected
open PermanssonResearch.Probability
open PermanssonResearch.Probability.DependentHistory
open PermanssonLean.ProbabilitySupport

set_option autoImplicit false
universe u v

variable {H : ℕ → Type u} {G : ℕ → Type v}
variable [∀ n, MeasurableSpace (H n)] [∀ n, MeasurableSpace (G n)]

/-- Coordinatewise projection of a genuine dependent path. -/
def projectedPath (q : ∀ n, H n → G n) :
    (∀ n, H n) → (∀ n, G n) :=
  fun w n => q n (w n)

theorem projectedPath_measurable
    (q : ∀ n, H n → G n) (hq : ∀ n, Measurable (q n)) :
    Measurable (projectedPath q) := by
  refine Measurable.of_eval fun n => ?_
  exact (hq n).comp (measurable_pi_apply n)

/-- Actual n-th marginal after projection, using the explicitly identified
fine canonical evolution rather than assuming a new Markov process. -/
theorem projectedPath_marginal
    (P : Measure (∀ n, H n))
    (μ : Measure (H 0))
    (K : ∀ n, Kernel (H n) (H (n+1)))
    (q : ∀ n, H n → G n) (hq : ∀ n, Measurable (q n))
    (hP : ∀ n, P.map (fun w => w n) = evolution μ K n)
    (n : ℕ) :
    (P.map (projectedPath q)).map (fun w => w n) =
      (evolution μ K n).map (q n) := by
  calc
    (P.map (projectedPath q)).map (fun w => w n) =
        (P.map (fun w => w n)).map (q n) := by
      rw [Measure.map_map (measurable_pi_apply n)
            (projectedPath_measurable q hq),
          Measure.map_map (hq n) (measurable_pi_apply n)]
      rfl
    _ = (evolution μ K n).map (q n) := by rw [hP n]

/-- A genuinely chronological fine/coarse kernel coupling plus exact
path marginals controls discounted normalized output scores. Initial
uncertainty contributes at n=0. No property is inferred for an unbound
external model or an unspecified constitutive comparison set. -/
theorem discounted_projected_output_error
    (P : Measure (∀ n, H n)) [IsProbabilityMeasure P]
    (Q : Measure (∀ n, G n)) [IsProbabilityMeasure Q]
    (μ ξ : Measure (H 0)) [IsProbabilityMeasure μ]
    (ν : Measure (G 0)) [IsProbabilityMeasure ν]
    (K R : ∀ n, Kernel (H n) (H (n+1)))
    (L : ∀ n, Kernel (G n) (G (n+1)))
    [∀ n, IsMarkovKernel (K n)] [∀ n, IsFiniteKernel (R n)]
    [∀ n, IsMarkovKernel (L n)]
    (q : ∀ n, H n → G n) (hq : ∀ n, Measurable (q n))
    (hξμ : ξ ≤ μ) (hξν : ξ.map (q 0) ≤ ν)
    (hRK : ∀ n, R n ≤ K n)
    (hproj : ∀ n, (R n).map (q (n+1)) ≤ (L n).comap (q n) (hq n))
    (η : ℕ → ℝ) (hη0 : ∀ n, 0 ≤ η n) (hη1 : ∀ n, η n ≤ 1)
    (hmass : ∀ n h, ENNReal.ofReal (1-η n) ≤ R n h Set.univ)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hξmass : ENNReal.ofReal (1-ε) ≤ ξ Set.univ)
    (hP : ∀ n, P.map (fun w => w n) = evolution μ K n)
    (hQ : ∀ n, Q.map (fun w => w n) = evolution ν L n)
    (g : ∀ n, G n → ℝ) (hg : ∀ n, Measurable (g n))
    (hg0 : ∀ n y, 0 ≤ g n y) (hg1 : ∀ n y, g n y ≤ 1)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    |(∫ w, summablePathScore (fun n => (1-β)*β^n)
          (fun n w => g n (w n)) w ∂(P.map (projectedPath q))) -
       ∫ w, summablePathScore (fun n => (1-β)*β^n)
          (fun n w => g n (w n)) w ∂Q| ≤
      ∑' n, (1-β)*β^n*(1-(1-ε)*retained η n) := by
  let Pq : Measure (∀ n, G n) := P.map (projectedPath q)
  haveI : IsProbabilityMeasure Pq := by
    dsimp [Pq]
    exact (Measure.isProbabilityMeasure_map_iff
      (projectedPath_measurable q hq).aemeasurable).mpr inferInstance
  have hPq (n : ℕ) :
      Pq.map (fun w => w n) = (evolution μ K n).map (q n) :=
    projectedPath_marginal P μ K q hq hP n
  have htv (n : ℕ) :
      eventTotalVariation (Pq.map (fun w => w n))
        (Q.map (fun w => w n)) ≤ 1-(1-ε)*retained η n := by
    rw [hPq n, hQ n]
    exact projected_evolution_tv_le_product μ ξ ν K R L
      q hq hξμ hξν hRK hproj η hη1 hmass hε1 hξmass n
  have he0 (n : ℕ) : 0 ≤ 1-(1-ε)*retained η n := by
    have hprod : (1-ε)*retained η n ≤ 1 := calc
      _ ≤ (1-ε)*1 :=
        mul_le_mul_of_nonneg_left (retained_le_one η hη0 hη1 n)
          (sub_nonneg.mpr hε1)
      _ ≤ 1 := by linarith
    exact sub_nonneg.mpr hprod
  have he1 (n : ℕ) : 1-(1-ε)*retained η n ≤ 1 := by
    exact sub_le_self _ (mul_nonneg (sub_nonneg.mpr hε1)
      (retained_nonneg η hη1 n))
  have hw (n : ℕ) : 0 ≤ (1-β)*β^n :=
    mul_nonneg (sub_nonneg.mpr (le_of_lt hβ1)) (pow_nonneg hβ0 n)
  have hws : Summable (fun n : ℕ => (1-β)*β^n) :=
    (summable_geometric_of_lt_one hβ0 hβ1).mul_left (1-β)
  have hbound := summable_output_score_error Pq Q
    (fun n (w : ∀ k, G k) => w n) (fun n => measurable_pi_apply n)
    g hg hg0 hg1 (fun n => (1-β)*β^n) hw hws
    (fun n => 1-(1-ε)*retained η n) he0 he1 htv
  simpa only [Pq] using hbound

end PermanssonResearch.Quotient.DiscountedProjected
