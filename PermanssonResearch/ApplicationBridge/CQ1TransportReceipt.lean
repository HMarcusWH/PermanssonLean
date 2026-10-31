import PermanssonResearch.ApplicationBridge.FiniteScoreReceipt
import PermanssonResearch.ApplicationBridge.QuantitativeReceipt
import PermanssonResearch.ConstitutiveQuasi.CertificateTransport
import Mathlib.Tactic

/-!
# ApplicationBridge — CQ-1 certificate transport under exact TV budgets

A CQ-1 receipt certifies the realized model of a baseline matrix `K₀` with the
strategic intervention to `K₁` (`FiniteScoreReceipt`). A transport receipt
adds an approximate pair `A₀`, `A₁` sharing the realized world kernel (P), and
rational one-step budgets `δ₀ ≥ max_y TV(K₀ y, A₀ y)` and
`δJ ≥ max_y TV(K₁ y, A₁ y)`. `TransportChecks` decides both budgets row by
row (`rowTV`, half-L1), `0 ≤ δ ≤ 1`, and the remaining-margin condition
`env δ₀ L + env δJ L < κ`, where `env δ L = 1 - (1 - δ)^L` is the rational
form of `geometricTVEnvelope`.

`checked_transported_certificate` applies Research's
`transportFiniteConstitutiveCertificate` with `realized_uniformTV`. The
approximate model gets a genuine `FiniteConstitutiveCertificate`: same
specification, the transported comparison set (the same states, exactly the
declared `B₁`), persistence error `min 1 (η + env δ₀ L)` and margin
`κ - env δ₀ L - env δJ L`. Nothing about the approximate pair beyond the
budgets is computed. This is not an Exact GR/PR transfer, and the budgets are
not empirical error estimates.
-/

namespace PermanssonResearch.ApplicationBridge.CQ1TransportReceipt

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open PermanssonLean PermanssonLean.RegimeSpecification
open PermanssonResearch.ReverseSolver
open PermanssonResearch.ReverseSolver.FiniteStrategicRealization
open PermanssonResearch.ConstitutiveQuasi
open PermanssonResearch.ApplicationBridge.FiniteScoreReceipt
open PermanssonResearch.ApplicationBridge.QuantitativeReceipt

set_option autoImplicit false

variable {n : ℕ}

attribute [local instance] StrategicWorldModel.inducedKernel_isMarkov

/-- Rational form of `geometricTVEnvelope`. -/
def env (δ : ℚ) (L : ℕ) : ℚ := 1 - (1 - δ) ^ L

theorem geometricTVEnvelope_cast (δ : ℚ) (L : ℕ) :
    ProbabilitySupport.geometricTVEnvelope (δ : ℝ) L = ((env δ L : ℚ) : ℝ) := by
  simp [ProbabilitySupport.geometricTVEnvelope, env]

/-- The approximate realized pair: same realized world kernel, the approximate
    baseline, and the typed strategic intervention to the approximate treated matrix. -/
noncomputable def approxPair (K₀ K₁ A₀ A₁ : RationalMarkovMatrix n) :
    StrategicApproximationPair (realizedModel K₀) (researchActionFamily K₀)
      (rationalStrategicIntervention K₀ K₁) where
  approx := realizedModel A₀
  approxFamily := researchActionFamily A₀
  approxIntervention := rationalStrategicIntervention A₀ A₁
  approx_world_eq := rfl

/-- Row budgets, unit-interval budgets and the remaining-margin condition. -/
def TransportChecks (K₀ K₁ A₀ A₁ : RationalMarkovMatrix n) (L : ℕ) (κ δ₀ δJ : ℚ) : Prop :=
  0 ≤ δ₀ ∧ δ₀ ≤ 1 ∧ 0 ≤ δJ ∧ δJ ≤ 1 ∧ (∀ y, rowTV K₀ A₀ y ≤ δ₀) ∧ (∀ y, rowTV K₁ A₁ y ≤ δJ) ∧
  env δ₀ L + env δJ L < κ

instance (K₀ K₁ A₀ A₁ : RationalMarkovMatrix n) (L : ℕ) (κ δ₀ δJ : ℚ) :
    Decidable (TransportChecks K₀ K₁ A₀ A₁ L κ δ₀ δJ) := by
  unfold TransportChecks
  infer_instance

def checkTransport (K₀ K₁ A₀ A₁ : RationalMarkovMatrix n) (L : ℕ) (κ δ₀ δJ : ℚ) : Bool :=
  decide (TransportChecks K₀ K₁ A₀ A₁ L κ δ₀ δJ)

theorem checkTransport_sound (K₀ K₁ A₀ A₁ : RationalMarkovMatrix n) (L : ℕ) (κ δ₀ δJ : ℚ)
    (h : checkTransport K₀ K₁ A₀ A₁ L κ δ₀ δJ = true) : TransportChecks K₀ K₁ A₀ A₁ L κ δ₀ δJ := by
  unfold checkTransport at h
  exact of_decide_eq_true h

/-- **Transported CQ-1 certificate.** The approximate realized model carries a
    genuine finite constitutive certificate for the same specification and
    comparison states, with the propagated persistence error and margin. -/
theorem checked_transported_certificate (K₀ K₁ A₀ A₁ : RationalMarkovMatrix n)
    (R basin B₁ Q : Finset (Fin n)) (L : ℕ) (η κ δ₀ δJ : ℚ) (y₁ y₂ : Fin n)
    (hc : checkCQ1 K₀ K₁ R basin B₁ Q L η κ y₁ y₂ = true)
    (ht : checkTransport K₀ K₁ A₀ A₁ L κ δ₀ δJ = true) :
    ∃ C : ConstitutiveComparisonSet (realizedModel K₀) (spec R basin),
      C.states = liftSet B₁ ∧
      (transportComparisonSet (realizedModel K₀) (realizedModel A₀) (spec R basin) C).states =
        liftSet B₁ ∧
      FiniteConstitutiveCertificate (realizedModel A₀) (spec R basin) (researchActionFamily A₀)
        (transportComparisonSet (realizedModel K₀) (realizedModel A₀) (spec R basin) C)
        (rationalStrategicIntervention A₀ A₁) L (prefixScore Q L)
        (clampedPersistenceError (ENNReal.ofReal (η : ℝ)) ((env δ₀ L : ℚ) : ℝ))
        (((κ - env δ₀ L - env δJ L : ℚ) : ℝ)) := by
  obtain ⟨C, hC, cert, -⟩ := checked_finite_constitutive_certificate K₀ K₁ R basin B₁ Q L η κ y₁ y₂ hc
  obtain ⟨hδ₀, hδ₀1, hδJ, hδJ1, hrow₀, hrowJ, hrem⟩ := checkTransport_sound K₀ K₁ A₀ A₁ L κ δ₀ δJ ht
  have hTV₀ := realized_uniformTV K₀ A₀ δ₀ hrow₀
  have hTVJ : ProbabilitySupport.HasUniformEventTVBound
      (rationalStrategicIntervention K₀ K₁).intervention.apply.inducedKernel
      (rationalStrategicIntervention A₀ A₁).intervention.apply.inducedKernel (δJ : ℝ) := by
    simpa only [rationalStrategicIntervention_applied] using realized_uniformTV K₁ A₁ δJ hrowJ
  have hremR : ProbabilitySupport.geometricTVEnvelope (δ₀ : ℝ) L +
      ProbabilitySupport.geometricTVEnvelope (δJ : ℝ) L < (κ : ℝ) := by
    rw [geometricTVEnvelope_cast, geometricTVEnvelope_cast]
    exact_mod_cast hrem
  have hT := transportFiniteConstitutiveCertificate (pair := approxPair K₀ K₁ A₀ A₁) cert
    (by exact_mod_cast hδ₀) (by exact_mod_cast hδ₀1) (by exact_mod_cast hδJ) (by exact_mod_cast hδJ1)
    hTV₀ hTVJ hremR
  refine ⟨C, hC, hC, ?_⟩
  rw [geometricTVEnvelope_cast, geometricTVEnvelope_cast] at hT
  push_cast
  exact hT

end PermanssonResearch.ApplicationBridge.CQ1TransportReceipt
