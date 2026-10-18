import PermanssonResearch.Probability.FiniteTransportSeparation
import PermanssonResearch.Probability.CouplingDualBound
import PermanssonResearch.StrategicWorld.ActionTraceInitialLaw

/-! Genuine finite Kantorovich--Rubinstein identification on the given metric.
Transport feasibility is proved by separation; every plan is then converted
to an actual measure with the exact original marginals. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace PermanssonResearch.Probability.FiniteTransport
open ActionTrace
set_option autoImplicit false

variable {Y : Type*} [Fintype Y] [Nonempty Y] [PseudoMetricSpace Y]

noncomputable def envelope (b : Y → ℝ) (i : Y) : ℝ := ⨅ j, dist i j-b j

theorem envelope_le (b : Y → ℝ) (i j : Y) : envelope b i ≤ dist i j-b j :=
  ciInf_le (Set.finite_range _).bddBelow j

theorem envelope_lipschitz (b : Y → ℝ) : LipschitzWith 1 (envelope b) := by
  apply LipschitzWith.of_le_add
  intro x y
  have hh : envelope b x-dist x y ≤ envelope b y := by
    apply le_ciInf
    intro j
    have hx := envelope_le b x j
    have ht := dist_triangle x y j
    linarith
  linarith

theorem envelope_dominates {a b : Y → ℝ} (h : ∀ i j, a i+b j ≤ dist i j) (i : Y) :
    a i ≤ envelope b i := by
  apply le_ciInf
  intro j
  linarith [h i j]

theorem envelope_diagonal (b : Y → ℝ) (j : Y) : envelope b j ≤ -b j := by
  simpa using envelope_le b j j

variable [MeasurableSpace Y] [MeasurableSingletonClass Y]

theorem finite_isKRTest {f : Y → ℝ} (hf : LipschitzWith 1 f) : IsKRTest f := by
  classical
  refine ⟨measurable_of_finite _,hf,⟨∑ j, |f j|,fun i => ?_⟩⟩
  exact Finset.single_le_sum (fun j _ => abs_nonneg (f j)) (Finset.mem_univ i)

theorem potentials_bound (μ ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {c : ℝ} (hc : W1DualLE μ ν c)
    (a b : Y → ℝ) (hab : ∀ i j, a i+b j ≤ dist i j) :
    (Row.ofMeasure μ).expect a + (Row.ofMeasure ν).expect b ≤ c := by
  let f := envelope b
  have hμ : (Row.ofMeasure μ).expect a ≤ (Row.ofMeasure μ).expect f :=
    Row.expect_mono _ (envelope_dominates hab)
  have hν : (Row.ofMeasure ν).expect b ≤ -(Row.ofMeasure ν).expect f := by
    calc
      _ ≤ (Row.ofMeasure ν).expect (fun j => -f j) := by
        apply Row.expect_mono
        intro j
        have h := envelope_diagonal b j
        dsimp [f]
        linarith
      _ = _ := by simp [Row.expect]
  have hh := hc f (finite_isKRTest (envelope_lipschitz b))
  rw [← Row.ofMeasure_measure μ,← Row.ofMeasure_measure ν,← Row.expect_eq_integral,
    ← Row.expect_eq_integral] at hh
  have hl := (le_abs_self _).trans hh
  linarith

theorem exists_plan_of_w1DualLE (μ ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {c : ℝ} (hc : W1DualLE μ ν c) :
    ∃ g : Row (Y × Y),
      (∀ i, ∑ j, g.mass (i,j) = μ.real {i}) ∧
      (∀ j, ∑ i, g.mass (i,j) = ν.real {j}) ∧
      g.expect (fun z => dist z.1 z.2) ≤ c :=
  exists_plan_of_dual (fun z => dist z.1 z.2) (Row.ofMeasure μ) (Row.ofMeasure ν) c
    (potentials_bound μ ν hc)

theorem integral_singleton_test [DecidableEq Y] (θ : Measure Y) (i : Y) :
    (∫ y, if y=i then (1 : ℝ) else 0 ∂θ) = θ.real {i} := by
  classical
  simpa [Set.indicator] using integral_indicator_one (μ := θ) (measurableSet_singleton i)

theorem first_marginal (g : Row (Y × Y)) (μ : Measure Y) [IsProbabilityMeasure μ]
    (hg : ∀ i, ∑ j, g.mass (i,j) = μ.real {i}) : g.measure.map Prod.fst = μ := by
  classical
  apply Measure.ext_of_measureReal_singleton
  intro i
  rw [← integral_singleton_test]
  rw [integral_map measurable_fst.aemeasurable (measurable_of_finite _).aestronglyMeasurable]
  rw [← Row.expect_eq_integral]
  simp only [Row.expect,Fintype.sum_prod_type,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_comm]
  simpa using hg i

theorem second_marginal (g : Row (Y × Y)) (ν : Measure Y) [IsProbabilityMeasure ν]
    (hg : ∀ j, ∑ i, g.mass (i,j) = ν.real {j}) : g.measure.map Prod.snd = ν := by
  classical
  apply Measure.ext_of_measureReal_singleton
  intro j
  rw [← integral_singleton_test]
  rw [integral_map measurable_snd.aemeasurable (measurable_of_finite _).aestronglyMeasurable]
  rw [← Row.expect_eq_integral]
  simpa [Row.expect,Fintype.sum_prod_type,mul_ite,Finset.sum_ite_irrel] using hg j

/-- The reverse direction constructs an actual coupling at the stated bound. -/
theorem exists_coupling_of_w1DualLE (μ ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {c : ℝ} (hc : W1DualLE μ ν c) :
    ∃ γ : IntegrableCoupling μ ν, γ.cost ≤ c := by
  obtain ⟨g,hgμ,hgν,hgc⟩ := exists_plan_of_w1DualLE μ ν hc
  let γ : IntegrableCoupling μ ν := {
    law := g.measure
    isProbability := inferInstance
    first := first_marginal g μ hgμ
    second := second_marginal g ν hgν
    cost_integrable := Integrable.of_finite }
  refine ⟨γ,?_⟩
  change (∫ z, dist z.1 z.2 ∂g.measure) ≤ c
  rwa [← Row.expect_eq_integral]

end PermanssonResearch.Probability.FiniteTransport

namespace PermanssonResearch.Probability
set_option autoImplicit false
variable {Y : Type*} [Finite Y] [PseudoMetricSpace Y] [MeasurableSpace Y]
variable [MeasurableSingletonClass Y]

/-- Finite reverse KR, using the original test class and genuine coupling
infimum. No compactness, optimality or duality hypothesis is supplied. -/
theorem finite_couplingW1_le_of_w1DualLE (μ ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {c : ℝ} (hc : W1DualLE μ ν c) : couplingW1 μ ν ≤ c := by
  classical
  letI := Fintype.ofFinite Y
  haveI : Nonempty Y := by
    obtain ⟨y,_⟩ := nonempty_of_measure_ne_zero (μ := μ) (s := Set.univ) (by simp)
    exact ⟨y⟩
  obtain ⟨γ,hγ⟩ := FiniteTransport.exists_coupling_of_w1DualLE μ ν hc
  have hb : BddBelow (couplingCosts μ ν) :=
    ⟨0,by rintro x ⟨η,rfl⟩; exact η.cost_nonneg⟩
  have hm : γ.cost ∈ couplingCosts μ ν := ⟨γ,rfl⟩
  exact (csInf_le hb hm).trans hγ

theorem finite_w1DualLE_iff_couplingW1_le (μ ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (c : ℝ) : W1DualLE μ ν c ↔ couplingW1 μ ν ≤ c :=
  ⟨finite_couplingW1_le_of_w1DualLE μ ν,
    w1DualLE_of_couplingW1_le μ ν ⟨finiteProductCoupling μ ν⟩⟩

theorem finite_exists_optimal_coupling (μ ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : ∃ γ : IntegrableCoupling μ ν, γ.cost = couplingW1 μ ν := by
  classical
  letI := Fintype.ofFinite Y
  haveI : Nonempty Y := by
    obtain ⟨y,_⟩ := nonempty_of_measure_ne_zero (μ := μ) (s := Set.univ) (by simp)
    exact ⟨y⟩
  obtain ⟨γ,hγ⟩ := FiniteTransport.exists_coupling_of_w1DualLE μ ν
    (finite_w1DualLE_couplingW1 μ ν)
  refine ⟨γ,le_antisymm hγ ?_⟩
  exact csInf_le ⟨0,by rintro x ⟨η,rfl⟩; exact η.cost_nonneg⟩ ⟨γ,rfl⟩

noncomputable def krDualValues (μ ν : Measure Y) : Set ℝ :=
  {c | ∃ f : Y → ℝ, IsKRTest f ∧ c = |∫ y, f y ∂μ-∫ y, f y ∂ν|}

/-- Literal equality of the coupling infimum and the supremum of the original
measurable bounded one-Lipschitz integral differences. -/
theorem finite_couplingW1_eq_dual_supremum (μ ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : couplingW1 μ ν = sSup (krDualValues μ ν) := by
  have hne : (krDualValues μ ν).Nonempty :=
    ⟨0,(fun _ => 0),IsKRTest.zero,by simp⟩
  have hb : BddAbove (krDualValues μ ν) := by
    refine ⟨couplingW1 μ ν,?_⟩
    rintro x ⟨f,hf,rfl⟩
    exact finite_w1DualLE_couplingW1 μ ν f hf
  apply le_antisymm
  · apply finite_couplingW1_le_of_w1DualLE
    intro f hf
    exact le_csSup hb ⟨f,hf,rfl⟩
  · apply csSup_le hne
    rintro x ⟨f,hf,rfl⟩
    exact finite_w1DualLE_couplingW1 μ ν f hf

end PermanssonResearch.Probability
