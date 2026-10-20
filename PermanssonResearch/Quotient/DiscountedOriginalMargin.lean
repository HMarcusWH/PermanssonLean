import PermanssonResearch.Quotient.DiscountedCanonicalBridge
import PermanssonResearch.Quotient.DiscountedProjectedOutputs
import PermanssonLean.Regime.Perturbation
import PermanssonLean.Quotient.PathLaw
import Mathlib.Tactic

/-!
NEXT-04.2: original full-path discounted RegimePropertyMap and exact B1
two-sided constitutive-margin transport. The baseline and intervention
output-error hypotheses must be separately established from actual typed
canonical laws and chronological common-mass witnesses; a mere positive
approximate margin cannot supply an Exact GR/PR certificate.
-/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory
namespace PermanssonResearch.Quotient.DiscountedOriginalMargin
open PermanssonLean
open PermanssonLean.RegimeSpecification
open PermanssonResearch.Probability

set_option autoImplicit false
variable {S X A Sb Xb Ab H Hb : Type*}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace Sb] [MeasurableSpace Xb] [MeasurableSpace Ab]
variable [MeasurableSpace H] [MeasurableSpace Hb]

/-- A REAL entire-path regime property. The output is the expectation of the
declared discounted score on the probability law, not a terminal-state toy. -/
noncomputable def discountedWholePathProperty
    {Y : Type*} [MeasurableSpace Y] (β : ℝ)
    (g : ℕ → Y → ℝ) : RegimePropertyMap Y ℝ :=
  fun ν => ∫ w, summablePathScore (fun n => (1-β)*β^n)
    (fun n w => g n (w n)) w ∂ν.toMeasure

/-- The fine property observes the fixed coarse descriptor q at every date;
it is evaluated on the full original fine path probability, not on an
arbitrarily postulated coarse Markov chain. -/
noncomputable def projectedDiscountedProperty
    (Qc : TypeRespectingStateCompression S X Sb Xb)
    (β : ℝ) (g : ℕ → JointState Sb Xb → ℝ) :
    RegimePropertyMap (JointState S X) ℝ :=
  fun ν => discountedWholePathProperty β g (Qc.pushPath ν)

/-- Both comparison outputs use the independently specified coarse
baseline/typed intervention and are pulled back to the full fine B1. -/
noncomputable def coarseOutputProfile
    (Qc : TypeRespectingStateCompression S X Sb Xb)
    (Mbar : StrategicWorldModel Sb Xb Ab)
    {ComponentBar : Type*} {Fbar : InterventionFamily Mbar ComponentBar}
    (Jbar : AdmissibleStrategicIntervention Fbar)
    (ψbar : RegimePropertyMap (JointState Sb Xb) ℝ) :
    PerturbedPropertyProfile (JointState S X) ℝ where
  baseline := fun y => baselinePropertyValue ψbar Mbar (Qc.stateMap y)
  intervention := fun y => intervenedPropertyValue ψbar Jbar.intervention (Qc.stateMap y)

/-- Exactly the original full-comparison-domain Proposition 5.2 margin,
not a minimum over a smaller hand-picked set. The two output bounds must
be proved for separate actual baseline and intervention processes. -/
theorem discounted_original_margin_abs_le
    (Qc : TypeRespectingStateCompression S X Sb Xb)
    {M : StrategicWorldModel S X A} {Mbar : StrategicWorldModel Sb Xb Ab}
    (spec : RegimeSpecification (JointState S X) H)
    (specBar : RegimeSpecification (JointState Sb Xb) Hb)
    {Component ComponentBar : Type*}
    (F : InterventionFamily M Component)
    (Fbar : InterventionFamily Mbar ComponentBar)
    (B₁ : ConstitutiveComparisonSet M spec)
    (Bbar₁ : ConstitutiveComparisonSet Mbar specBar)
    (hB : Bbar₁.states = Qc.stateMap '' B₁.states)
    (J : AdmissibleStrategicIntervention F)
    (Jbar : AdmissibleStrategicIntervention Fbar)
    (β : ℝ) (g : ℕ → JointState Sb Xb → ℝ)
    (ε₀ εJ : ℝ) (hε₀ : 0 ≤ ε₀) (hεJ : 0 ≤ εJ)
    (hbase : ∀ y ∈ B₁.states,
      dist (baselinePropertyValue (projectedDiscountedProperty Qc β g) M y)
        (baselinePropertyValue (discountedWholePathProperty β g) Mbar (Qc.stateMap y)) ≤ ε₀)
    (htreat : ∀ y ∈ B₁.states,
      dist (intervenedPropertyValue (projectedDiscountedProperty Qc β g) J.intervention y)
        (intervenedPropertyValue (discountedWholePathProperty β g)
          Jbar.intervention (Qc.stateMap y)) ≤ εJ) :
    |constitutiveMargin M spec F (projectedDiscountedProperty Qc β g) B₁ J -
      constitutiveMargin Mbar specBar Fbar (discountedWholePathProperty β g)
        Bbar₁ Jbar| ≤ ε₀ + εJ := by
  let profile := coarseOutputProfile Qc Mbar Jbar (discountedWholePathProperty β g)
  have herrors : HasConstitutiveOutputErrors M spec F
      (projectedDiscountedProperty Qc β g) B₁ J profile ε₀ εJ :=
    ⟨hε₀, hεJ, hbase, htreat⟩
  have hmain := constitutiveMargin_perturbation_abs_le M spec F
    (projectedDiscountedProperty Qc β g) B₁ J profile ε₀ εJ herrors
  have hprofile :
      perturbedConstitutiveMargin M spec B₁ profile =
        constitutiveMargin Mbar specBar Fbar (discountedWholePathProperty β g)
          Bbar₁ Jbar := by
    unfold perturbedConstitutiveMargin constitutiveMargin
    rw [hB, ← Set.image_comp]
    rfl
  rw [hprofile] at hmain
  simpa only [abs_sub_comm] using hmain

/-- Strict positivity survives only when a VERIFIED true-model gap
dominates the entire two-sided output-error envelope. -/
theorem discounted_original_margin_positive_of_gap
    (Qc : TypeRespectingStateCompression S X Sb Xb)
    {M : StrategicWorldModel S X A} {Mbar : StrategicWorldModel Sb Xb Ab}
    (spec : RegimeSpecification (JointState S X) H)
    (specBar : RegimeSpecification (JointState Sb Xb) Hb)
    {Component ComponentBar : Type*}
    (F : InterventionFamily M Component)
    (Fbar : InterventionFamily Mbar ComponentBar)
    (B₁ : ConstitutiveComparisonSet M spec)
    (Bbar₁ : ConstitutiveComparisonSet Mbar specBar)
    (hB : Bbar₁.states = Qc.stateMap '' B₁.states)
    (J : AdmissibleStrategicIntervention F)
    (Jbar : AdmissibleStrategicIntervention Fbar)
    (β : ℝ) (g : ℕ → JointState Sb Xb → ℝ)
    (ε₀ εJ : ℝ) (hε₀ : 0 ≤ ε₀) (hεJ : 0 ≤ εJ)
    (hbase : ∀ y ∈ B₁.states,
      dist (baselinePropertyValue (projectedDiscountedProperty Qc β g) M y)
        (baselinePropertyValue (discountedWholePathProperty β g) Mbar (Qc.stateMap y)) ≤ ε₀)
    (htreat : ∀ y ∈ B₁.states,
      dist (intervenedPropertyValue (projectedDiscountedProperty Qc β g) J.intervention y)
        (intervenedPropertyValue (discountedWholePathProperty β g)
          Jbar.intervention (Qc.stateMap y)) ≤ εJ)
    (hgap : ε₀ + εJ <
      constitutiveMargin M spec F (projectedDiscountedProperty Qc β g) B₁ J) :
    0 < constitutiveMargin Mbar specBar Fbar (discountedWholePathProperty β g)
      Bbar₁ Jbar := by
  have hh := discounted_original_margin_abs_le Qc spec specBar F Fbar
    B₁ Bbar₁ hB J Jbar β g ε₀ εJ hε₀ hεJ hbase htreat
  rw [abs_le] at hh
  linarith [hh.2]

/-- Numerical reporting uncertainty is NOT baked into the original
true constitutive margin. Each layer is an additional inequality. -/
theorem discounted_reported_margin_abs_le
    {κfine κcoarse κreported e₀ eJ b₀ bJ : ℝ}
    (hmodel : |κfine - κcoarse| ≤ e₀ + eJ)
    (hreport : |κreported - κcoarse| ≤ b₀ + bJ) :
    |κreported - κfine| ≤ (e₀ + eJ) + (b₀ + bJ) := by
  calc
    |κreported - κfine| =
        |(κreported - κcoarse) + (κcoarse - κfine)| := by congr 1; ring
    _ ≤ |κreported - κcoarse| + |κcoarse - κfine| := abs_add_le _ _
    _ ≤ (b₀ + bJ) + (e₀ + eJ) :=
      add_le_add hreport (by simpa only [abs_sub_comm] using hmodel)
    _ = _ := by ring

end PermanssonResearch.Quotient.DiscountedOriginalMargin
