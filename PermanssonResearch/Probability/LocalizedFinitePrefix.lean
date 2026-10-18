import PermanssonResearch.Probability.GoodHistoryVisit
import PermanssonResearch.Probability.SummablePathScores
import PermanssonResearch.Quotient.ApproxPrefix
import PermanssonResearch.ConstitutiveQuasi.Definition
import Mathlib.Tactic

/-!
Q-LOCAL finite-prefix bridge. The prefix laws below are the existing real
Ionescu--Tulcea finite trajectories. Each time-t bad-set mass belongs to the
FIRST kernel's actual evolving prefix law and not to an arbitrary proxy law.
Time T means T transitions and the T+1 coordinates 0..T.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

namespace PermanssonResearch.Probability

open PermanssonLean.ProbabilitySupport
open PermanssonResearch.Quotient
open PermanssonResearch.ConstitutiveQuasi

variable {Y : Type*} [MeasurableSpace Y]

/-- Actual canonical finite-prefix TV from time-indexed expected row budgets.
The proof uses the existing `finitePrefixLaw_succ` identity, not a presumed
identification with a different stochastic history process. -/
theorem finitePrefixLaw_tv_le_averaged
    (K L : Kernel Y Y) [IsMarkovKernel K] [IsMarkovKernel L]
    (y : Y) (d : (n : ℕ) → ((i : Finset.Iic n) → Y) → ℝ)
    (hd : ∀ n, Measurable (d n)) (hd0 : ∀ n w, 0 ≤ d n w)
    (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n)
    (hrows : ∀ n w,
      eventTotalVariation (K (w ⟨n, Finset.mem_Iic.mpr le_rfl⟩))
        (L (w ⟨n, Finset.mem_Iic.mpr le_rfl⟩)) ≤ d n w)
    (haverage : ∀ n,
      (∫⁻ w, ENNReal.ofReal (d n w) ∂finitePrefixLaw K y n) ≤
        ENNReal.ofReal (e n))
    (T : ℕ) :
    eventTotalVariation (finitePrefixLaw K y T) (finitePrefixLaw L y T) ≤
      min 1 (∑ t ∈ Finset.range T, e t) := by
  have hsum : ∀ n,
      eventTotalVariation (finitePrefixLaw K y n) (finitePrefixLaw L y n) ≤
        ∑ t ∈ Finset.range n, e t := by
    intro n
    induction n with
    | zero =>
      rw [finitePrefixLaw_zero_eq K L y, eventTotalVariation_self]
      simp
    | succ n ih =>
      let mu := finitePrefixLaw K y n
      let nu := finitePrefixLaw L y n
      have hrow : ∀ w,
          eventTotalVariation ((stationaryPrefixKernel K n) w)
            ((stationaryPrefixKernel L n) w) ≤ d n w := by
        intro w
        change eventTotalVariation
          (K (w ⟨n, Finset.mem_Iic.mpr le_rfl⟩))
          (L (w ⟨n, Finset.mem_Iic.mpr le_rfl⟩)) ≤ d n w
        exact hrows n w
      have hstep := eventTV_compProd_averaged mu
        (stationaryPrefixKernel K n) (stationaryPrefixKernel L n)
        (d n) (hd n) (hd0 n) (he n) hrow (haverage n)
      have hleft := eventTotalVariation_compProd_left_le
        mu nu (stationaryPrefixKernel L n)
      have htri := eventTotalVariation_triangle
        (mu ⊗ₘ stationaryPrefixKernel K n)
        (mu ⊗ₘ stationaryPrefixKernel L n)
        (nu ⊗ₘ stationaryPrefixKernel L n)
      have hmap := eventTotalVariation_map_le
        (mu ⊗ₘ stationaryPrefixKernel K n)
        (nu ⊗ₘ stationaryPrefixKernel L n)
        (measurable_appendLast n)
      rw [finitePrefixLaw_succ K y n, finitePrefixLaw_succ L y n,
        Finset.sum_range_succ]
      calc
        eventTotalVariation
          ((mu ⊗ₘ stationaryPrefixKernel K n).map (appendLast n))
          ((nu ⊗ₘ stationaryPrefixKernel L n).map (appendLast n)) ≤
          eventTotalVariation (mu ⊗ₘ stationaryPrefixKernel K n)
            (nu ⊗ₘ stationaryPrefixKernel L n) := hmap
        _ ≤ e n + eventTotalVariation mu nu :=
          htri.trans (add_le_add hstep hleft)
        _ ≤ (∑ t ∈ Finset.range n, e t) + e n := by
          linarith [ih]
  exact le_min (eventTotalVariation_le_one _ _) (hsum T)

/-- Genuine good-history visits provide the time-dependent source-law
row-error budget, at every horizon and every initial state. -/
theorem finitePrefixLaw_tv_le_goodVisits
    (K L : Kernel Y Y) [IsMarkovKernel K] [IsMarkovKernel L]
    (y : Y)
    (E : (n : ℕ) → Set ((i : Finset.Iic n) → Y))
    (hE : ∀ n, MeasurableSet (E n))
    (eta v : ℕ → ℝ) (heta : ∀ n, 0 ≤ eta n) (hv : ∀ n, 0 ≤ v n)
    (hgood : ∀ n w, w ∈ E n →
      eventTotalVariation (K (w ⟨n, Finset.mem_Iic.mpr le_rfl⟩))
        (L (w ⟨n, Finset.mem_Iic.mpr le_rfl⟩)) ≤ eta n)
    (hvisit : ∀ n,
      finitePrefixLaw K y n (E n)ᶜ ≤ ENNReal.ofReal (v n))
    (T : ℕ) :
    eventTotalVariation (finitePrefixLaw K y T) (finitePrefixLaw L y T) ≤
      min 1 (∑ t ∈ Finset.range T, (eta t + v t)) := by
  classical
  refine finitePrefixLaw_tv_le_averaged K L y
    (fun n w => goodHistoryMajorant (E n) (eta n) w)
    (fun n => goodHistoryMajorant_measurable (hE n) (eta n))
    (fun n w => goodHistoryMajorant_nonneg (heta n) w)
    (fun n => eta n + v n) (fun n => add_nonneg (heta n) (hv n))
    ?_ ?_ T
  · intro n w
    by_cases hw : w ∈ E n
    · simpa [goodHistoryMajorant, hw] using hgood n w hw
    · simp only [goodHistoryMajorant, if_neg hw]
      exact eventTotalVariation_le_one _ _
  · intro n
    exact goodHistory_lintegral_le (finitePrefixLaw K y n)
      (E n) (hE n) (heta n) (hv n) (hvisit n)

/-- Normalized finite-prefix scores inherit the LOCAL, visit-dependent
error; no global row bound and no comparison-set shrinking. -/
theorem finitePathExpectation_abs_le_goodVisits
    (K L : Kernel Y Y) [IsMarkovKernel K] [IsMarkovKernel L]
    (y : Y)
    (E : (n : ℕ) → Set ((i : Finset.Iic n) → Y))
    (hE : ∀ n, MeasurableSet (E n))
    (eta v : ℕ → ℝ) (heta : ∀ n, 0 ≤ eta n) (hv : ∀ n, 0 ≤ v n)
    (hgood : ∀ n w, w ∈ E n →
      eventTotalVariation (K (w ⟨n, Finset.mem_Iic.mpr le_rfl⟩))
        (L (w ⟨n, Finset.mem_Iic.mpr le_rfl⟩)) ≤ eta n)
    (hvisit : ∀ n,
      finitePrefixLaw K y n (E n)ᶜ ≤ ENNReal.ofReal (v n))
    (T : ℕ) (f : FinitePathProperty Y T) :
    |f.fromKernel T K y - f.fromKernel T L y| ≤
      min 1 (∑ t ∈ Finset.range T, (eta t + v t)) := by
  have hscore := bounded_score_integral_error
    (finitePrefixLaw K y T) (finitePrefixLaw L y T)
    f.score f.measurable_score f.score_nonneg f.score_le_one
  exact hscore.trans
    (finitePrefixLaw_tv_le_goodVisits K L y E hE eta v
      heta hv hgood hvisit T)

/-- The existing point-started finite-prefix law, packaged as a kernel in its
initial state. This reuses the same `partialTraj`, not a new transition law. -/
noncomputable def canonicalPrefixKernel
    (K : Kernel Y Y) (T : ℕ) : Kernel Y ((i : Finset.Iic T) → Y) :=
  (Kernel.partialTraj (X := fun _ : ℕ => Y)
    (fun n => stationaryPrefixKernel K n) 0 T).comap
      singletonPrefix (by
        exact Measurable.of_eval (fun _ => measurable_id))

instance canonicalPrefixKernel_isMarkov
    (K : Kernel Y Y) [IsMarkovKernel K] (T : ℕ) :
    IsMarkovKernel (canonicalPrefixKernel K T) := by
  unfold canonicalPrefixKernel
  infer_instance

@[simp] theorem canonicalPrefixKernel_apply
    (K : Kernel Y Y) (y : Y) (T : ℕ) :
    canonicalPrefixKernel K T y = finitePrefixLaw K y T := rfl

/-- An explicit mixture of the *actual* canonical point-started prefix laws.
This is the approximate computation's declared initial distribution. No
empirical identification or full-path mixed-law equality is presumed. -/
noncomputable def mixedFinitePrefixLaw
    (K : Kernel Y Y) (mu : Measure Y) (T : ℕ) :
    Measure ((i : Finset.Iic T) → Y) :=
  (mu ⊗ₘ canonicalPrefixKernel K T).map Prod.snd

instance mixedFinitePrefixLaw_isProbability
    (K : Kernel Y Y) [IsMarkovKernel K]
    (mu : Measure Y) [IsProbabilityMeasure mu] (T : ℕ) :
    IsProbabilityMeasure (mixedFinitePrefixLaw K mu T) := by
  unfold mixedFinitePrefixLaw
  exact (Measure.isProbabilityMeasure_map_iff measurable_snd.aemeasurable).mpr
    inferInstance

/-- The mixture reduces to the original point-start law at a Dirac input. -/
@[simp] theorem mixedFinitePrefixLaw_dirac
    (K : Kernel Y Y) [IsMarkovKernel K] (y : Y) (T : ℕ) :
    mixedFinitePrefixLaw K (Measure.dirac y) T = finitePrefixLaw K y T := by
  ext C hC
  rw [mixedFinitePrefixLaw, Measure.map_apply measurable_snd hC,
    Measure.compProd_apply (measurable_snd hC)]
  change (∫⁻ z, canonicalPrefixKernel K T z C ∂Measure.dirac y) =
    finitePrefixLaw K y T C
  rw [lintegral_dirac' _ ((canonicalPrefixKernel K T).measurable_coe hC)]
  rfl

/-- Initial-law uncertainty passes through a fixed canonical trajectory kernel
by data processing. It is charged even at zero transitions. -/
theorem mixedFinitePrefixLaw_tv_le_initial
    (K : Kernel Y Y) [IsMarkovKernel K]
    (mu nu : Measure Y) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (T : ℕ) :
    eventTotalVariation (mixedFinitePrefixLaw K mu T) (mixedFinitePrefixLaw K nu T) ≤
      eventTotalVariation mu nu := by
  exact (eventTotalVariation_map_le
    (mu ⊗ₘ canonicalPrefixKernel K T) (nu ⊗ₘ canonicalPrefixKernel K T)
    measurable_snd).trans
      (eventTotalVariation_compProd_left_le mu nu (canonicalPrefixKernel K T))

/-- Localized row/visit uncertainty plus a separately certified approximate
initial distribution. The true process remains point-started at `y`. -/
theorem finitePrefixLaw_tv_le_goodVisits_initial
    (K L : Kernel Y Y) [IsMarkovKernel K] [IsMarkovKernel L]
    (y : Y) (nu : Measure Y) [IsProbabilityMeasure nu]
    (E : (n : ℕ) → Set ((i : Finset.Iic n) → Y))
    (hE : ∀ n, MeasurableSet (E n))
    (eta v : ℕ → ℝ) (heta : ∀ n, 0 ≤ eta n) (hv : ∀ n, 0 ≤ v n)
    (hgood : ∀ n w, w ∈ E n →
      eventTotalVariation (K (w ⟨n, Finset.mem_Iic.mpr le_rfl⟩))
        (L (w ⟨n, Finset.mem_Iic.mpr le_rfl⟩)) ≤ eta n)
    (hvisit : ∀ n,
      finitePrefixLaw K y n (E n)ᶜ ≤ ENNReal.ofReal (v n))
    {eps : ℝ} (hinitial : eventTotalVariation (Measure.dirac y) nu ≤ eps)
    (T : ℕ) :
    eventTotalVariation (finitePrefixLaw K y T) (mixedFinitePrefixLaw L nu T) ≤
      min 1 (eps + ∑ t ∈ Finset.range T, (eta t + v t)) := by
  have hlocal := (finitePrefixLaw_tv_le_goodVisits K L y E hE eta v
    heta hv hgood hvisit T).trans (min_le_right _ _)
  have hinit := (mixedFinitePrefixLaw_tv_le_initial L (Measure.dirac y) nu T).trans
    hinitial
  rw [mixedFinitePrefixLaw_dirac] at hinit
  have htri := eventTotalVariation_triangle
    (finitePrefixLaw K y T) (finitePrefixLaw L y T) (mixedFinitePrefixLaw L nu T)
  refine le_min (eventTotalVariation_le_one _ _) ?_
  linarith

/-- The actual normalized score inherits both model-local and initial-law
error. Report rounding is not included here and must be added separately. -/
theorem finitePathExpectation_abs_le_goodVisits_initial
    (K L : Kernel Y Y) [IsMarkovKernel K] [IsMarkovKernel L]
    (y : Y) (nu : Measure Y) [IsProbabilityMeasure nu]
    (E : (n : ℕ) → Set ((i : Finset.Iic n) → Y))
    (hE : ∀ n, MeasurableSet (E n))
    (eta v : ℕ → ℝ) (heta : ∀ n, 0 ≤ eta n) (hv : ∀ n, 0 ≤ v n)
    (hgood : ∀ n w, w ∈ E n →
      eventTotalVariation (K (w ⟨n, Finset.mem_Iic.mpr le_rfl⟩))
        (L (w ⟨n, Finset.mem_Iic.mpr le_rfl⟩)) ≤ eta n)
    (hvisit : ∀ n,
      finitePrefixLaw K y n (E n)ᶜ ≤ ENNReal.ofReal (v n))
    {eps : ℝ} (hinitial : eventTotalVariation (Measure.dirac y) nu ≤ eps)
    (T : ℕ) (f : FinitePathProperty Y T) :
    |f.fromKernel T K y - f.expected T (mixedFinitePrefixLaw L nu T)| ≤
      min 1 (eps + ∑ t ∈ Finset.range T, (eta t + v t)) := by
  exact (bounded_score_integral_error
    (finitePrefixLaw K y T) (mixedFinitePrefixLaw L nu T)
    f.score f.measurable_score f.score_nonneg f.score_le_one).trans
      (finitePrefixLaw_tv_le_goodVisits_initial K L y nu E hE eta v
        heta hv hgood hvisit hinitial T)

end PermanssonResearch.Probability

