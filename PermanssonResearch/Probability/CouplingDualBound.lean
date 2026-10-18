import PermanssonResearch.Probability.KantorovichDual
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! A-KR weak direction on genuine couplings, without an assumed transport
duality oracle. The reverse finite/Polish identification is a separate theorem.
No common supnorm-one restriction is imposed on the Lipschitz test class. -/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch.Probability

variable {Y : Type*} [PseudoMetricSpace Y] [MeasurableSpace Y]

structure IntegrableCoupling (μ ν : Measure Y) where
  law : Measure (Y × Y)
  isProbability : IsProbabilityMeasure law
  first : law.map Prod.fst = μ
  second : law.map Prod.snd = ν
  cost_integrable : Integrable (fun z : Y × Y => dist z.1 z.2) law

attribute [instance] IntegrableCoupling.isProbability

noncomputable def IntegrableCoupling.cost {μ ν : Measure Y} (γ : IntegrableCoupling μ ν) : ℝ :=
  ∫ z, dist z.1 z.2 ∂γ.law

theorem IntegrableCoupling.cost_nonneg {μ ν : Measure Y} (γ : IntegrableCoupling μ ν) :
    0 ≤ γ.cost := integral_nonneg (fun _ => dist_nonneg)

theorem IntegrableCoupling.dual_bound {μ ν : Measure Y} (γ : IntegrableCoupling μ ν) :
    W1DualLE μ ν γ.cost := by
  intro f hf
  obtain ⟨C, hC⟩ := hf.bounded
  have hfirst : Integrable (fun z : Y × Y => f z.1) γ.law :=
    Integrable.of_bound (hf.measurable.comp measurable_fst).aestronglyMeasurable C
      (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using hC z.1)
  have hsecond : Integrable (fun z : Y × Y => f z.2) γ.law :=
    Integrable.of_bound (hf.measurable.comp measurable_snd).aestronglyMeasurable C
      (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using hC z.2)
  have hiμ : (∫ y, f y ∂μ) = ∫ z, f z.1 ∂γ.law := by
    calc
      _ = ∫ y, f y ∂γ.law.map Prod.fst :=
        congrArg (fun θ : Measure Y => ∫ y, f y ∂θ) γ.first.symm
      _ = _ := integral_map measurable_fst.aemeasurable hf.measurable.aestronglyMeasurable
  have hiν : (∫ y, f y ∂ν) = ∫ z, f z.2 ∂γ.law := by
    calc
      _ = ∫ y, f y ∂γ.law.map Prod.snd :=
        congrArg (fun θ : Measure Y => ∫ y, f y ∂θ) γ.second.symm
      _ = _ := integral_map measurable_snd.aemeasurable hf.measurable.aestronglyMeasurable
  rw [hiμ, hiν, ← integral_sub hfirst hsecond]
  calc
    |∫ z, f z.1 - f z.2 ∂γ.law| ≤ ∫ z, |f z.1 - f z.2| ∂γ.law :=
      abs_integral_le_integral_abs
    _ ≤ γ.cost := by
      apply integral_mono (hfirst.sub hsecond).abs γ.cost_integrable
      intro z
      simpa [Real.dist_eq] using hf.lipschitz.dist_le_mul z.1 z.2

noncomputable def couplingCosts (μ ν : Measure Y) : Set ℝ :=
  Set.range (fun γ : IntegrableCoupling μ ν => γ.cost)

noncomputable def couplingW1 (μ ν : Measure Y) : ℝ := sInf (couplingCosts μ ν)

/-- Taking the infimum of genuine finite coupling costs preserves the weak
dual bound; nonemptiness rules out a vacuous infimum. -/
theorem w1DualLE_couplingW1 (μ ν : Measure Y) (hne : Nonempty (IntegrableCoupling μ ν)) :
    W1DualLE μ ν (couplingW1 μ ν) := by
  intro f hf
  apply le_csInf
  · obtain ⟨γ⟩ := hne
    exact ⟨γ.cost, γ, rfl⟩
  · rintro c ⟨γ, rfl⟩
    exact γ.dual_bound f hf

theorem w1DualLE_of_couplingW1_le (μ ν : Measure Y)
    (hne : Nonempty (IntegrableCoupling μ ν)) {c : ℝ} (h : couplingW1 μ ν ≤ c) :
    W1DualLE μ ν c := (w1DualLE_couplingW1 μ ν hne).mono h

/-- Finite probabilities have a concrete integrable coupling, including
degenerate laws. No optimal-coupling or duality premise is needed. -/
noncomputable def finiteProductCoupling [Finite Y] [MeasurableSingletonClass Y]
    (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IntegrableCoupling μ ν where
  law := μ.prod ν
  isProbability := inferInstance
  first := by simp
  second := by simp
  cost_integrable := Integrable.of_finite

theorem finite_w1DualLE_couplingW1 [Finite Y] [MeasurableSingletonClass Y]
    (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    W1DualLE μ ν (couplingW1 μ ν) :=
  w1DualLE_couplingW1 μ ν ⟨finiteProductCoupling μ ν⟩

end PermanssonResearch.Probability
