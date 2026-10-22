import PermanssonResearch.Quotient.Q05ActualOriginalMarginWitnessFixture
import PermanssonResearch.Quotient.DiscountedCanonicalMarginClosure
import PermanssonResearch.Quotient.DiscountedOriginalMargin
import Mathlib.Tactic

/-!
# Q-05: actual-source PointWitness and original constitutive-margin interface

The previous typed source has a real common finite subkernel for both actual
baseline and intervention. Its exact mass, eta and geometric budget are proved
there. The *remaining* obligations are the two genuine kernel domination
statements. They are explicit hypotheses here, not numerical substitutes,
unreviewed axioms, or fabricated proof data.

Under those full all-state inequalities, this theorem constructs actual
PointWitness objects for both legal strategic interventions and invokes the
existing original full-B₁ constitutiveMargin theorem with the exact image of
the predeclared, path-law-nontrivial two-start comparison set. It does NOT prove
the two domination hypotheses, canonical-score numerical equalities, Exact
GR/PR preservation, or empirical identification.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.Quotient.Q05ActualOriginalMarginAdapter

open PermanssonLean
open PermanssonLean.RegimeSpecification
open PermanssonResearch.Quotient.Q05ActualOriginalMarginWitnessFixture
open PermanssonResearch.Quotient.DiscountedCanonicalMarginClosure
open PermanssonResearch.Quotient.DiscountedOriginalMargin
open PermanssonResearch.Probability.DependentHistory

set_option autoImplicit false

/-- The independently mandatory, ACTUAL induced-kernel domination contracts
for all four source models, not just the two frozen comparison starts. -/
structure VerifiedSourceDomination where
  fine : ∀ t : Bool,
    commonSourceKernel t ≤ (fineModel t).inducedKernel
  projected : ∀ t : Bool,
    (commonSourceKernel t).map compression.stateMap ≤
      (coarseModel t).inducedKernel.comap
        compression.stateMap compression.stateMap_measurable

/-- For a genuinely finite state carrier, eventwise domination is entailed
by domination of EVERY singleton atom; no special event is skipped. -/
theorem finiteMeasureLeOfAtoms
    {Z : Type*} [Fintype Z] [MeasurableSpace Z]
    [MeasurableSingletonClass Z]
    (μ ν : Measure Z)
    (hatom : ∀ z : Z, μ {z} ≤ ν {z}) : μ ≤ ν := by
  classical
  apply Measure.le_iff.mpr
  intro E hE
  let selected : Finset Z := Finset.univ.filter (fun z => z ∈ E)
  have hselected : (selected : Set Z) = E := by
    ext z
    simp [selected]
  calc
    μ E = μ (selected : Set Z) := by rw [hselected]
    _ = ∑ z ∈ selected, μ {z} :=
      (Measure.sum_measure_singleton).symm
    _ ≤ ∑ z ∈ selected, ν {z} :=
      Finset.sum_le_sum (fun z _ => hatom z)
    _ = ν (selected : Set Z) :=
      Measure.sum_measure_singleton
    _ = ν E := by rw [hselected]

/-- An exact original-kernel atom contract: every fine atom AND every
projected coarse atom must dominate its actual common source row. Unlike a
norm bound, it is an all-state, all-atom, both-protocol specification. -/
structure VerifiedSourceAtomDomination where
  fine : ∀ (t : Bool) (y z : FineState),
    (commonSourceKernel t) y {z} ≤
      (fineModel t).inducedKernel y {z}
  projected : ∀ (t : Bool) (y : FineState) (z : CoarseState),
    ((commonSourceKernel t) y).map compression.stateMap {z} ≤
      (coarseModel t).inducedKernel (compression.stateMap y) {z}

/-- Complete row domination follows from the source's actual finite atom
inequalities. This avoids treating a few sampled histories or a positive
reported total-variation estimate as full kernel order. -/
theorem sourceDominationOfAtoms
    (h : VerifiedSourceAtomDomination) : VerifiedSourceDomination := by
  refine ⟨?_, ?_⟩
  · intro t
    change ∀ y, (commonSourceKernel t) y ≤ (fineModel t).inducedKernel y
    intro y
    exact finiteMeasureLeOfAtoms _ _ (h.fine t y)
  · intro t
    change ∀ y,
      ((commonSourceKernel t).map compression.stateMap) y ≤
        ((coarseModel t).inducedKernel.comap
          compression.stateMap compression.stateMap_measurable) y
    intro y
    rw [Kernel.map_apply _ compression.stateMap_measurable,
        Kernel.comap_apply]
    exact finiteMeasureLeOfAtoms _ _ (h.projected t y)

/-- All the other PointWitness fields are derived from the source, not assumed.
The two domination premises above are the precise open mathematical tasks. -/
noncomputable def sourcePointWitness
    (h : VerifiedSourceDomination) (t : Bool) :
    PointWitness compression (fineModel t) (coarseModel t) where
  R := commonSourceKernel t
  R_finite := commonSourceKernel_isFinite t
  R_sub := h.fine t
  R_projected := h.projected t
  eta := commonEta
  eta_nonneg := by intro n; norm_num [commonEta]
  eta_le_one := by intro n; norm_num [commonEta]
  retention := fun n y => commonSourceKernel_retention t n y

/-- Once the eight finite-row atom obligations are discharged, their
ALL-event consequences provide the genuine original PointWitness. -/
noncomputable def sourcePointWitnessOfAtoms
    (h : VerifiedSourceAtomDomination) (t : Bool) :
    PointWitness compression (fineModel t) (coarseModel t) :=
  sourcePointWitness (sourceDominationOfAtoms h) t

/-- This is the literal *admitted* joint strategic intervention, not a
separate model silently substituted for the intervention. -/
theorem fineJ_is_treated_source :
    fineJ.intervention.apply = fineModel true := rfl

theorem coarseJ_is_treated_source :
    coarseJ.intervention.apply = coarseModel true := rfl

/-- The score is a genuine fixed, bounded, measurable full-path integrand.
It reads the physical coordinate and never accesses latent fine memory. -/
def observedWorldScore : ℕ → CoarseState → ℝ :=
  fun _ z => if z.2 then 1 else 0

theorem observedWorldScore_measurable (n : ℕ) :
    Measurable (observedWorldScore n) := Measurable.of_discrete

theorem observedWorldScore_bounded (n : ℕ) (z : CoarseState) :
    0 ≤ observedWorldScore n z ∧ observedWorldScore n z ≤ 1 := by
  rcases z with ⟨s, x⟩
  cases x <;> norm_num [observedWorldScore]

/-- The real source subkernel retains exactly the discounted mass needed
for both baseline and intervention, at *all* original comparison states. -/
theorem sourcePointWitness_budget
    (h : VerifiedSourceDomination) (t : Bool) :
    (∑' n : ℕ, (1-(1/3 : ℝ))*(1/3 : ℝ)^n*
      (1-retained (sourcePointWitness h t).eta n)) = 1/41 := by
  change (∑' n : ℕ, (1-(1/3 : ℝ))*(1/3 : ℝ)^n*
      (1-retained commonEta n)) = 1/41
  exact commonEta_discounted_budget

/-- Conditional source-derived full original B₁ margin.
The only unresolved *hypotheses* are genuine all-row kernel domination,
which are declared in VerifiedSourceDomination. Neither manuscript approval
nor Exact GR follows from this quantitative margin bound. -/
theorem original_margin_of_verified_source_domination
    (h : VerifiedSourceDomination) :
    |constitutiveMargin (fineModel false) fineSpec fineFamily
        (projectedDiscountedProperty compression (1/3 : ℝ) observedWorldScore)
        fineComparisonSet fineJ -
      constitutiveMargin (coarseModel false) coarseSpec coarseFamily
        (discountedWholePathProperty (1/3 : ℝ) observedWorldScore)
        coarseComparisonSet coarseJ| ≤ (2/41 : ℝ) := by
  let W0 : ∀ y ∈ fineComparisonSet.states,
      PointWitness compression (fineModel false) (coarseModel false) :=
    fun _ _ => sourcePointWitness h false
  let WJ : ∀ y ∈ fineComparisonSet.states,
      PointWitness compression fineJ.intervention.apply
        coarseJ.intervention.apply := fun _ _ => by
    rw [fineJ_is_treated_source, coarseJ_is_treated_source]
    exact sourcePointWitness h true
  have hg : ∀ n, Measurable (observedWorldScore n) :=
    observedWorldScore_measurable
  have hg0 : ∀ n z, 0 ≤ observedWorldScore n z :=
    fun n z => (observedWorldScore_bounded n z).1
  have hg1 : ∀ n z, observedWorldScore n z ≤ 1 :=
    fun n z => (observedWorldScore_bounded n z).2
  have hb0 : ∀ y (hy : y ∈ fineComparisonSet.states),
      (∑' n, (1-(1/3 : ℝ))*(1/3 : ℝ)^n*
        (1-retained (W0 y hy).eta n)) ≤ 1/41 := by
    intro y hy
    change (∑' n : ℕ, (1-(1/3 : ℝ))*(1/3 : ℝ)^n*
      (1-retained commonEta n)) ≤ 1/41
    rw [commonEta_discounted_budget]
  have hbJ : ∀ y (hy : y ∈ fineComparisonSet.states),
      (∑' n, (1-(1/3 : ℝ))*(1/3 : ℝ)^n*
        (1-retained (WJ y hy).eta n)) ≤ 1/41 := by
    intro y hy
    change (∑' n : ℕ, (1-(1/3 : ℝ))*(1/3 : ℝ)^n*
      (1-retained commonEta n)) ≤ 1/41
    rw [commonEta_discounted_budget]
  have main := actual_canonical_discounted_original_margin
    compression fineSpec coarseSpec fineFamily coarseFamily
    fineComparisonSet coarseComparisonSet entire_original_comparison_domain
    fineJ coarseJ W0 WJ (1/3 : ℝ) observedWorldScore hg hg0 hg1
    (by norm_num : 0 ≤ (1/3 : ℝ))
    (by norm_num : (1/3 : ℝ) < 1)
    (1/41 : ℝ) (1/41 : ℝ)
    (by norm_num : 0 ≤ (1/41 : ℝ))
    (by norm_num : 0 ≤ (1/41 : ℝ))
    hb0 hbJ
  norm_num at main ⊢
  exact main

end PermanssonResearch.Quotient.Q05ActualOriginalMarginAdapter
