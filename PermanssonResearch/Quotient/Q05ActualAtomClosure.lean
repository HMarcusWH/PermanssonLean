import PermanssonResearch.Quotient.Q05ActualOriginalMarginAdapter
import PermanssonResearch.X1.TypedModels
import Mathlib.Tactic

/-!
# Q-05 exact original alpha -> P -> U kernel domination candidate

The following lemmas identify genuine typed induced-kernel singleton atoms,
not a postulated Markov table. Once both actual atom identities are checked,
finite atom dominance supplies the missing original PointWitness premises.
No `sorry`, axiom, randomized-policy extension, or Exact GR claim.
This module is a SOURCE CANDIDATE until a pinned Lean/compiler receipt passes.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace PermanssonResearch.Quotient.Q05ActualAtomClosure

open PermanssonLean
open PermanssonResearch.X1 (coin coin_true coin_false coin_lintegral)
open PermanssonResearch.Quotient.Q05ActualOriginalMarginWitnessFixture
open PermanssonResearch.Quotient.Q05ActualOriginalMarginAdapter

set_option autoImplicit false

/-- The actual typed fine source has only the new strategic coordinate `t`,
and its physical world is the sampled action. -/
theorem fine_induced_singleton (t : Bool) (y z : FineState) :
    (fineModel t).inducedKernel y {z} =
      if z.1 = t then (coin (fineActionRate t y.1)) {z.2} else 0 := by
  classical
  rw [StrategicWorldModel.inducedKernel_apply
    (fineModel t) y (measurableSet_singleton z)]
  change (∫⁻ a, ∫⁻ x', (Measure.dirac t)
      {s : Bool | (s, x') ∈ ({z} : Set FineState)}
      ∂(Measure.dirac a) ∂coin (fineActionRate t y.1)) = _
  rcases z with ⟨sz, xz⟩
  simp only [lintegral_dirac]
  rw [coin_lintegral]
  cases t <;> cases sz <;> cases xz <;>
    simp [Measure.dirac_apply', coin_true, coin_false,
      Set.indicator, Set.mem_singleton_iff]

/-- Same actual alpha -> P -> U identity for the coarse Unit-strategic
model, where the physical P is still literally x' = a. -/
theorem coarse_induced_singleton (t : Bool) (y z : CoarseState) :
    (coarseModel t).inducedKernel y {z} =
      (coin (coarseActionRate t)) {z.2} := by
  classical
  rw [StrategicWorldModel.inducedKernel_apply
    (coarseModel t) y (measurableSet_singleton z)]
  change (∫⁻ a, ∫⁻ x', (Measure.dirac ())
      {s : Unit | (s, x') ∈ ({z} : Set CoarseState)}
      ∂(Measure.dirac a) ∂coin (coarseActionRate t)) = _
  rcases z with ⟨sz, xz⟩
  cases sz
  simp only [lintegral_dirac]
  rw [coin_lintegral]
  cases xz <;> simp [Measure.dirac_apply', coin_true, coin_false,
    Set.indicator, Set.mem_singleton_iff]

/-- Finite common subkernel: only the two physically reachable next
atoms carry mass, and the weights are the entrywise Bernoulli minima. -/
theorem common_source_singleton (t : Bool) (y z : FineState) :
    (commonSourceKernel t) y {z} =
      if z.1 = t then
        ENNReal.ofReal
          ((if z.2 then commonTrueMass t y.1
             else commonFalseMass t y.1 : ℚ) : ℝ)
      else 0 := by
  rcases z with ⟨sz, xz⟩
  cases t <;> cases sz <;> cases xz <;>
    simp [commonSourceKernel, commonSourceRow, Measure.add_apply,
      Measure.smul_apply, Measure.dirac_apply', commonTrueMass,
      commonFalseMass, fineActionRate, coarseActionRate]

/-- Genuine compressed common row, with all fine-memory dependence
still retained in the probability weights. -/
theorem projected_common_singleton (t : Bool) (y : FineState)
    (z : CoarseState) :
    ((commonSourceKernel t) y).map compression.stateMap {z} =
      ENNReal.ofReal
        ((if z.2 then commonTrueMass t y.1
           else commonFalseMass t y.1 : ℚ) : ℝ) := by
  rcases z with ⟨sz, xz⟩
  cases sz
  rw [Measure.map_apply compression.stateMap_measurable
    (measurableSet_singleton ((), xz))]
  cases t <;> cases xz <;> cases y with
    | mk s x =>
      cases s <;> cases x <;>
        simp [commonSourceKernel, commonSourceRow, compression,
          Measure.add_apply, Measure.smul_apply,
          Measure.dirac_apply', commonTrueMass, commonFalseMass,
          fineActionRate, coarseActionRate]

/-- The two original input-dependent singleton atoms dominate the actual
common subkernel on every fine strategic/physical state. -/
theorem fine_actual_atom_domination
    (t : Bool) (y z : FineState) :
    (commonSourceKernel t) y {z} ≤
      (fineModel t).inducedKernel y {z} := by
  rw [common_source_singleton, fine_induced_singleton]
  by_cases h : z.1 = t
  · simp only [h, ite_true]
    cases hz : z.2
    · rw [coin_false]
      apply ENNReal.ofReal_le_ofReal
      exact_mod_cast commonFalseMass_le_fine t y.1
    · rw [coin_true]
      apply ENNReal.ofReal_le_ofReal
      exact_mod_cast commonTrueMass_le_fine t y.1
  · simp [h]

/-- The compressed row is dominated by the REAL coarse induced kernel at
every original fine source state, not just at baseline-reachable states. -/
theorem coarse_actual_atom_domination
    (t : Bool) (y : FineState) (z : CoarseState) :
    ((commonSourceKernel t) y).map compression.stateMap {z} ≤
      (coarseModel t).inducedKernel (compression.stateMap y) {z} := by
  rw [projected_common_singleton, coarse_induced_singleton]
  cases hz : z.2
  · rw [coin_false]
    apply ENNReal.ofReal_le_ofReal
    exact_mod_cast commonFalseMass_le_coarse t y.1
  · rw [coin_true]
    apply ENNReal.ofReal_le_ofReal
    exact_mod_cast commonTrueMass_le_coarse t y.1

/-- Full actual all-state source-domination certificate, with no
pointwise/initial-law assumption hidden in the constructor. -/
noncomputable def original_verified_atom_domination :
    VerifiedSourceAtomDomination where
  fine := fine_actual_atom_domination
  projected := coarse_actual_atom_domination

noncomputable def original_point_witness (t : Bool) :
    PermanssonResearch.Quotient.DiscountedCanonicalMarginClosure.PointWitness
      compression (fineModel t) (coarseModel t) :=
  sourcePointWitnessOfAtoms original_verified_atom_domination t

/-- Full ORIGINAL constitutive-margin conclusion once source atom identities
and finite all-row dominance above have compiled. -/
theorem actual_original_B1_margin_bound :
    |PermanssonLean.RegimeSpecification.constitutiveMargin
        (fineModel false) fineSpec fineFamily
          (PermanssonResearch.Quotient.DiscountedOriginalMargin.projectedDiscountedProperty
            compression (1/3 : ℝ) observedWorldScore)
          fineComparisonSet fineJ -
      PermanssonLean.RegimeSpecification.constitutiveMargin
        (coarseModel false) coarseSpec coarseFamily
          (PermanssonResearch.Quotient.DiscountedOriginalMargin.discountedWholePathProperty
            (1/3 : ℝ) observedWorldScore)
          coarseComparisonSet coarseJ| ≤ (2/41 : ℝ) :=
  original_margin_of_verified_source_domination
    (sourceDominationOfAtoms original_verified_atom_domination)

end PermanssonResearch.Quotient.Q05ActualAtomClosure
