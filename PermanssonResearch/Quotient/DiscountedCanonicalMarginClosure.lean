import PermanssonResearch.Quotient.DiscountedCanonicalSourceWitness
import PermanssonResearch.Quotient.DiscountedOriginalMargin
import Mathlib.Tactic

/-!
# Real source-to-original constitutive-margin closure

Uses genuine typed baseline/treatment canonical laws to construct the two
premises of original Proposition 5.2. A bound over every original B₁ start is
mandatory. Positive approximate margins never imply Exact GR preservation.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.Quotient.DiscountedCanonicalMarginClosure
open PermanssonLean
open PermanssonLean.RegimeSpecification
open PermanssonResearch.Probability
open PermanssonResearch.Probability.DependentHistory
open PermanssonResearch.Quotient.DiscountedCanonicalSourceWitness
open PermanssonResearch.Quotient.DiscountedOriginalMargin

set_option autoImplicit false
variable {S X A Sb Xb Ab H Hb : Type*}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace Sb] [MeasurableSpace Xb] [MeasurableSpace Ab]
variable [MeasurableSpace H] [MeasurableSpace Hb]
variable [MeasurableSingletonClass (JointState S X)]
variable [MeasurableSingletonClass (JointState Sb Xb)]

/-- A source-bound, point-initialized common-mass certificate.
The initial submeasure is exactly the matched Dirac law; its defect is zero.
The row domination covers intervention-reachable states as well. -/
structure PointWitness
    (Qc : TypeRespectingStateCompression S X Sb Xb)
    (M : StrategicWorldModel S X A)
    (Mbar : StrategicWorldModel Sb Xb Ab) where
  R : Kernel (JointState S X) (JointState S X)
  R_finite : IsFiniteKernel R
  R_sub : R ≤ M.inducedKernel
  R_projected : R.map Qc.stateMap ≤
    Mbar.inducedKernel.comap Qc.stateMap Qc.stateMap_measurable
  eta : ℕ → ℝ
  eta_nonneg : ∀ n, 0 ≤ eta n
  eta_le_one : ∀ n, eta n ≤ 1
  retention : ∀ n y, ENNReal.ofReal (1-eta n) ≤ R y Set.univ

/-- Actual canonical discounted output, from *each* genuine source and
coarse model at the same fixed comparison start. -/
theorem point_witness_output
    (Qc : TypeRespectingStateCompression S X Sb Xb)
    (M : StrategicWorldModel S X A)
    (Mbar : StrategicWorldModel Sb Xb Ab)
    (W : PointWitness Qc M Mbar)
    (y : JointState S X)
    (g : ℕ → JointState Sb Xb → ℝ)
    (hg : ∀ n, Measurable (g n))
    (hg0 : ∀ n z, 0 ≤ g n z) (hg1 : ∀ n z, g n z ≤ 1)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    |(∫ w, summablePathScore (fun n => (1-β)*β^n)
          (fun n w => g n (w n)) w
          ∂((M.pathLaw (Measure.dirac y)).map Qc.pathMap)) -
      ∫ w, summablePathScore (fun n => (1-β)*β^n)
          (fun n w => g n (w n)) w
          ∂(Mbar.pathLaw (Measure.dirac (Qc.stateMap y)))| ≤
       ∑' n, (1-β)*β^n*(1-retained W.eta n) := by
  letI : IsFiniteKernel W.R := W.R_finite
  have hmap : (Measure.dirac y).map Qc.stateMap =
      Measure.dirac (Qc.stateMap y) := by
    rw [Measure.map_dirac' Qc.stateMap_measurable]
  have h := canonical_discounted_output_error Qc M Mbar
    (Measure.dirac y) (Measure.dirac y)
    (Measure.dirac (Qc.stateMap y)) W.R
    le_rfl (le_of_eq hmap) W.R_sub W.R_projected
    W.eta W.eta_nonneg W.eta_le_one W.retention
    (by norm_num : 0 ≤ (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1)
    (by simp : ENNReal.ofReal (1-(0:ℝ)) ≤ (Measure.dirac y) Set.univ)
    g hg hg0 hg1 hβ0 hβ1
  simpa only [sub_zero, one_mul] using h

/-- All original comparison starts receive their own certified baseline and
intervention source witnesses; the same B₁ and coarse image Bbar₁ are used. -/
theorem actual_canonical_discounted_original_margin
    (Qc : TypeRespectingStateCompression S X Sb Xb)
    {M : StrategicWorldModel S X A}
    {Mbar : StrategicWorldModel Sb Xb Ab}
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
    (W0 : ∀ y ∈ B₁.states, PointWitness Qc M Mbar)
    (WJ : ∀ y ∈ B₁.states,
      PointWitness Qc J.intervention.apply Jbar.intervention.apply)
    (β : ℝ) (g : ℕ → JointState Sb Xb → ℝ)
    (hg : ∀ n, Measurable (g n))
    (hg0 : ∀ n z, 0 ≤ g n z) (hg1 : ∀ n z, g n z ≤ 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (e0 eJ : ℝ) (he0 : 0 ≤ e0) (heJ : 0 ≤ eJ)
    (huniform0 : ∀ y ∈ B₁.states,
      (∑' n, (1-β)*β^n*(1-retained (W0 y ‹y ∈ B₁.states›).eta n)) ≤ e0)
    (huniformJ : ∀ y ∈ B₁.states,
      (∑' n, (1-β)*β^n*(1-retained (WJ y ‹y ∈ B₁.states›).eta n)) ≤ eJ) :
    |constitutiveMargin M spec F (projectedDiscountedProperty Qc β g) B₁ J -
      constitutiveMargin Mbar specBar Fbar
        (discountedWholePathProperty β g) Bbar₁ Jbar| ≤ e0+eJ := by
  apply discounted_original_margin_abs_le Qc spec specBar F Fbar
    B₁ Bbar₁ hB J Jbar β g e0 eJ he0 heJ
  · intro y hy
    have hw := point_witness_output Qc M Mbar (W0 y hy) y g
      hg hg0 hg1 hβ0 hβ1
    have hb := huniform0 y hy
    unfold baselinePropertyValue projectedDiscountedProperty
      discountedWholePathProperty
    exact le_trans (by simpa only [Real.dist_eq] using hw) hb
  · intro y hy
    have hw := point_witness_output Qc J.intervention.apply
      Jbar.intervention.apply (WJ y hy) y g
      hg hg0 hg1 hβ0 hβ1
    have hb := huniformJ y hy
    unfold intervenedPropertyValue projectedDiscountedProperty
      discountedWholePathProperty
    exact le_trans (by simpa only [Real.dist_eq] using hw) hb

end PermanssonResearch.Quotient.DiscountedCanonicalMarginClosure
