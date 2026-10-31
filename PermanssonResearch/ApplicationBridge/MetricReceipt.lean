import PermanssonResearch.Perturbation.DirectDualContraction
import PermanssonResearch.Perturbation.ContractiveOccupation
import PermanssonResearch.ReverseSolver.RationalKernel
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic

/-!
# ApplicationBridge — finite metric contraction and invariant-law perturbation

A receipt declares a finite rational metric `d` on `Fin n`, a baseline and a
perturbed rational Markov matrix, and transport certificates: couplings
(primal) and 1-Lipschitz potentials (dual). `Pt d` is `Fin n` carrying the
genuine metric `d` (checked to be a metric), the discrete σ-algebra and the
Markov kernels whose rows are the declared matrix rows.

`MetricChecks` decides the metric axioms, a coupling of every ordered row pair
of the baseline with cost at most `ρ d(x, y)`, `0 ≤ ρ < 1`, a coupling of every
baseline row with the perturbed row with cost at most `δ`, the invariance of
both declared laws, and a coupling and potential with equal value `w` for the
two invariant laws. Then:

* `checked_row_contraction` — Research's all-probability-law
  `IsW1Contraction` for the baseline kernel, via
  `isW1Contraction_of_test_images`;
* `checked_invariant_metric_bound` — Research's `ContractivePerturbation`
  is assembled from the checked data and `invariantLaw_wasserstein_le` gives
  `W1DualLE π πt (δ / (1 - ρ))`;
* `finite_transport_certificate_sound` — `w` is the exact dual
  Kantorovich–Rubinstein distance: `W1DualLE π πt w`, and no smaller bound
  holds. A coupling alone would only give the upper bound.

General Polish-space moment and invariance arguments are not restated.
-/

namespace PermanssonResearch.ApplicationBridge.MetricReceipt

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open PermanssonResearch.Probability
open PermanssonResearch.Perturbation
open PermanssonResearch.ReverseSolver

set_option autoImplicit false

variable {n : ℕ}

/-- A finite rational metric. -/
def IsFiniteMetric (d : Fin n → Fin n → ℚ) : Prop :=
  (∀ i, d i i = 0) ∧ (∀ i j, d i j = d j i) ∧ (∀ i j, i ≠ j → 0 < d i j) ∧
    ∀ i j k, d i k ≤ d i j + d j k

instance (d : Fin n → Fin n → ℚ) : Decidable (IsFiniteMetric d) := by
  unfold IsFiniteMetric
  infer_instance

/-- `Fin n` carrying the metric `d`. -/
structure Pt (d : Fin n → Fin n → ℚ) where
  idx : Fin n

variable {d : Fin n → Fin n → ℚ}

def ptEquiv (d : Fin n → Fin n → ℚ) : Pt d ≃ Fin n :=
  ⟨Pt.idx, Pt.mk, fun _ => rfl, fun _ => rfl⟩

instance : Fintype (Pt d) := Fintype.ofEquiv (Fin n) (ptEquiv d).symm
instance : DecidableEq (Pt d) := (ptEquiv d).decidableEq

noncomputable instance metricSpace [h : Fact (IsFiniteMetric d)] : MetricSpace (Pt d) where
  dist p q := (d p.idx q.idx : ℝ)
  dist_self p := by
    show (d p.idx p.idx : ℝ) = 0
    rw [h.out.1]
    simp
  dist_comm p q := by
    show (d p.idx q.idx : ℝ) = d q.idx p.idx
    rw [h.out.2.1]
  dist_triangle p q r := by exact_mod_cast h.out.2.2.2 p.idx q.idx r.idx
  eq_of_dist_eq_zero := by
    intro p q hpq
    by_contra hne
    have hidx : p.idx ≠ q.idx := fun e => hne (by cases p; cases q; simp_all)
    have := h.out.2.2.1 _ _ hidx
    have : (0 : ℝ) < d p.idx q.idx := by exact_mod_cast this
    change (d p.idx q.idx : ℝ) = 0 at hpq
    linarith

instance : MeasurableSpace (Pt d) := ⊤
instance : DiscreteMeasurableSpace (Pt d) := ⟨fun _ => trivial⟩
instance : MeasurableSingletonClass (Pt d) := ⟨fun _ => trivial⟩

theorem dist_pt [Fact (IsFiniteMetric d)] (p q : Pt d) : dist p q = (d p.idx q.idx : ℝ) := rfl

/-- A probability vector. -/
def IsProb (μ : Fin n → ℚ) : Prop := (∀ i, 0 ≤ μ i) ∧ (∑ i, μ i) = 1

/-- The law on `Pt d` with weights `μ`. -/
noncomputable def law (d : Fin n → Fin n → ℚ) (μ : Fin n → ℚ) (h : IsProb μ) : Measure (Pt d) :=
  (PMF.ofFintype (fun p : Pt d => ENNReal.ofReal (μ p.idx)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => by exact_mod_cast h.1 p.idx)]
    have : (∑ p : Pt d, (μ p.idx : ℝ)) = 1 := by
      rw [← (ptEquiv d).symm.sum_comp]
      exact_mod_cast h.2
    rw [this, ENNReal.ofReal_one])).toMeasure

instance (μ : Fin n → ℚ) (h : IsProb μ) : IsProbabilityMeasure (law d μ h) := by
  unfold law
  infer_instance

theorem integral_law (μ : Fin n → ℚ) (h : IsProb μ) (f : Pt d → ℝ) :
    ∫ p, f p ∂(law d μ h) = ∑ i, (μ i : ℝ) * f ⟨i⟩ := by
  unfold law
  rw [PMF.integral_eq_sum]
  rw [← (ptEquiv d).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  simp [ptEquiv, ENNReal.toReal_ofReal (by exact_mod_cast h.1 i : (0 : ℝ) ≤ μ i), smul_eq_mul]

theorem row_isProb (K : RationalMarkovMatrix n) (x : Fin n) : IsProb (fun z => K.entry x z) :=
  ⟨fun z => K.entry_nonneg x z, K.row_sum_one x⟩

/-- The Markov kernel on `Pt d` whose rows are the rows of `K`. -/
noncomputable def kernel (d : Fin n → Fin n → ℚ) (K : RationalMarkovMatrix n) : Kernel (Pt d) (Pt d) where
  toFun p := law d (fun z => K.entry p.idx z) (row_isProb K p.idx)
  measurable' := Measurable.of_discrete

instance (K : RationalMarkovMatrix n) : IsMarkovKernel (kernel d K) :=
  ⟨fun p => by unfold kernel; simp only [Kernel.coe_mk]; infer_instance⟩

/-- A coupling of `μ` and `ν`. -/
def IsCoupling (μ ν : Fin n → ℚ) (C : Fin n → Fin n → ℚ) : Prop :=
  (∀ i j, 0 ≤ C i j) ∧ (∀ i, (∑ j, C i j) = μ i) ∧ ∀ j, (∑ i, C i j) = ν j

def cost (d : Fin n → Fin n → ℚ) (C : Fin n → Fin n → ℚ) : ℚ := ∑ i, ∑ j, C i j * d i j

/-- Primal bound: a coupling's cost bounds every 1-Lipschitz test. -/
theorem coupling_test_bound [Fact (IsFiniteMetric d)] (μ ν : Fin n → ℚ) (C : Fin n → Fin n → ℚ)
    (hC : IsCoupling μ ν C) (f : Pt d → ℝ) (hf : LipschitzWith 1 f) :
    |(∑ i, (μ i : ℝ) * f ⟨i⟩) - ∑ j, (ν j : ℝ) * f ⟨j⟩| ≤ (cost d C : ℝ) := by
  obtain ⟨hnn, hrow, hcol⟩ := hC
  have hμ : ∀ i, (μ i : ℝ) = ∑ j, (C i j : ℝ) := fun i => by rw [← hrow i]; push_cast; rfl
  have hν : ∀ j, (ν j : ℝ) = ∑ i, (C i j : ℝ) := fun j => by rw [← hcol j]; push_cast; rfl
  have hsplit : (∑ i, (μ i : ℝ) * f ⟨i⟩) - ∑ j, (ν j : ℝ) * f ⟨j⟩ =
      ∑ i, ∑ j, (C i j : ℝ) * (f ⟨i⟩ - f ⟨j⟩) := by
    simp only [hμ, hν, Finset.sum_mul, mul_sub, Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_comm
  rw [hsplit]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  unfold cost
  push_cast
  apply Finset.sum_le_sum
  intro i _
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_of_nonneg (by exact_mod_cast hnn i j)]
  apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast hnn i j)
  have := hf.dist_le_mul ⟨i⟩ ⟨j⟩
  rw [Real.dist_eq, dist_pt] at this
  simpa using this

theorem coupling_w1DualLE [Fact (IsFiniteMetric d)] (μ ν : Fin n → ℚ) (hμ : IsProb μ) (hν : IsProb ν)
    (C : Fin n → Fin n → ℚ) (hC : IsCoupling μ ν C) {c : ℝ} (hc : (cost d C : ℝ) ≤ c) :
    W1DualLE (law d μ hμ) (law d ν hν) c := by
  intro f hf
  rw [integral_law, integral_law]
  exact (coupling_test_bound μ ν C hC f hf.lipschitz).trans hc

/-- The checked data. Couplings of ordered row pairs and of each baseline row
    with the perturbed row, invariant laws, and the invariant transport. -/
def MetricChecks (d : Fin n → Fin n → ℚ) (K Kt : RationalMarkovMatrix n) (ρ δ w : ℚ)
    (Cpair : Fin n → Fin n → Fin n → Fin n → ℚ) (Cdef : Fin n → Fin n → Fin n → ℚ)
    (π πt : Fin n → ℚ) (Cinv : Fin n → Fin n → ℚ) (f : Fin n → ℚ) : Prop :=
  IsFiniteMetric d ∧ 0 ≤ ρ ∧ ρ < 1 ∧
  (∀ x y, IsCoupling (fun z => K.entry x z) (fun z => K.entry y z) (Cpair x y) ∧
    cost d (Cpair x y) ≤ ρ * d x y) ∧
  (∀ y, IsCoupling (fun z => K.entry y z) (fun z => Kt.entry y z) (Cdef y) ∧ cost d (Cdef y) ≤ δ) ∧
  IsProb π ∧ IsProb πt ∧
  (∀ z, (∑ x, π x * K.entry x z) = π z) ∧ (∀ z, (∑ x, πt x * Kt.entry x z) = πt z) ∧
  IsCoupling π πt Cinv ∧ cost d Cinv = w ∧
  (∀ i j, f i - f j ≤ d i j) ∧ (∑ i, f i * (π i - πt i)) = w

instance (d : Fin n → Fin n → ℚ) (K Kt : RationalMarkovMatrix n) (ρ δ w : ℚ)
    (Cpair : Fin n → Fin n → Fin n → Fin n → ℚ) (Cdef : Fin n → Fin n → Fin n → ℚ)
    (π πt : Fin n → ℚ) (Cinv : Fin n → Fin n → ℚ) (f : Fin n → ℚ) :
    Decidable (MetricChecks d K Kt ρ δ w Cpair Cdef π πt Cinv f) := by
  unfold MetricChecks IsFiniteMetric IsCoupling IsProb
  infer_instance

def checkMetricReceipt (d : Fin n → Fin n → ℚ) (K Kt : RationalMarkovMatrix n) (ρ δ w : ℚ)
    (Cpair : Fin n → Fin n → Fin n → Fin n → ℚ) (Cdef : Fin n → Fin n → Fin n → ℚ)
    (π πt : Fin n → ℚ) (Cinv : Fin n → Fin n → ℚ) (f : Fin n → ℚ) : Bool :=
  decide (MetricChecks d K Kt ρ δ w Cpair Cdef π πt Cinv f)

theorem checkMetricReceipt_sound (d : Fin n → Fin n → ℚ) (K Kt : RationalMarkovMatrix n) (ρ δ w : ℚ)
    (Cpair : Fin n → Fin n → Fin n → Fin n → ℚ) (Cdef : Fin n → Fin n → Fin n → ℚ)
    (π πt : Fin n → ℚ) (Cinv : Fin n → Fin n → ℚ) (f : Fin n → ℚ)
    (h : checkMetricReceipt d K Kt ρ δ w Cpair Cdef π πt Cinv f = true) :
    MetricChecks d K Kt ρ δ w Cpair Cdef π πt Cinv f := by
  unfold checkMetricReceipt at h
  exact of_decide_eq_true h

theorem kernel_apply (K : RationalMarkovMatrix n) (p : Pt d) :
    kernel d K p = law d (fun z => K.entry p.idx z) (row_isProb K p.idx) := rfl

/-- **Row contraction.** The baseline kernel is a W1 contraction with factor
    `ρ` against every pair of probability laws. -/
theorem checked_row_contraction [Fact (IsFiniteMetric d)] (K Kt : RationalMarkovMatrix n) (ρ δ w : ℚ)
    (Cpair : Fin n → Fin n → Fin n → Fin n → ℚ) (Cdef : Fin n → Fin n → Fin n → ℚ)
    (π πt : Fin n → ℚ) (Cinv : Fin n → Fin n → ℚ) (f : Fin n → ℚ)
    (h : checkMetricReceipt d K Kt ρ δ w Cpair Cdef π πt Cinv f = true) :
    IsW1Contraction (kernel d K) (ρ : ℝ) := by
  obtain ⟨-, hρ0, -, hpair, -⟩ := checkMetricReceipt_sound d K Kt ρ δ w Cpair Cdef π πt Cinv f h
  apply isW1Contraction_of_test_images _ (by exact_mod_cast hρ0)
  intro g hg x y
  rw [kernel_apply, kernel_apply, integral_law, integral_law]
  obtain ⟨hC, hcost⟩ := hpair x.idx y.idx
  refine (coupling_test_bound _ _ _ hC g hg.lipschitz).trans ?_
  rw [dist_pt]
  exact_mod_cast hcost

theorem checked_defect [Fact (IsFiniteMetric d)] (K Kt : RationalMarkovMatrix n) (ρ δ w : ℚ)
    (Cpair : Fin n → Fin n → Fin n → Fin n → ℚ) (Cdef : Fin n → Fin n → Fin n → ℚ)
    (π πt : Fin n → ℚ) (Cinv : Fin n → Fin n → ℚ) (f : Fin n → ℚ)
    (h : checkMetricReceipt d K Kt ρ δ w Cpair Cdef π πt Cinv f = true) (y : Pt d) :
    W1DualLE (kernel d K y) (kernel d Kt y) (δ : ℝ) := by
  obtain ⟨-, -, -, -, hdef, -⟩ := checkMetricReceipt_sound d K Kt ρ δ w Cpair Cdef π πt Cinv f h
  obtain ⟨hC, hcost⟩ := hdef y.idx
  rw [kernel_apply, kernel_apply]
  exact coupling_w1DualLE _ _ (row_isProb K y.idx) (row_isProb Kt y.idx) _ hC (by exact_mod_cast hcost)

/-- A declared invariant vector gives an invariant measure. -/
theorem law_invariant (K : RationalMarkovMatrix n) (μ : Fin n → ℚ) (hμ : IsProb μ)
    (hinv : ∀ z, (∑ x, μ x * K.entry x z) = μ z) :
    kernel d K ∘ₘ law d μ hμ = law d μ hμ := by
  apply Measure.ext_of_singleton
  intro q
  rw [Measure.bind_apply (measurableSet_singleton q) (Kernel.aemeasurable _)]
  rw [lintegral_fintype]
  have hlaw : ∀ (ν : Fin n → ℚ) (hν : IsProb ν) (p : Pt d),
      law d ν hν {p} = ENNReal.ofReal (ν p.idx) := by
    intro ν hν p
    unfold law
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton p)]
    rfl
  simp only [kernel_apply, hlaw]
  rw [← (ptEquiv d).symm.sum_comp]
  simp only [ptEquiv, Equiv.coe_fn_symm_mk]
  rw [← hinv q.idx]
  push_cast
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => mul_nonneg
    (by exact_mod_cast hμ.1 x) (by exact_mod_cast K.entry_nonneg x q.idx))]
  apply Finset.sum_congr rfl
  intro x _
  rw [ENNReal.ofReal_mul (by exact_mod_cast hμ.1 x), mul_comm]

/-- **Invariant-law perturbation (A3).** Research's `ContractivePerturbation`
    assembled from the checked data bounds the invariant laws' distance. -/
theorem checked_invariant_metric_bound [Fact (IsFiniteMetric d)] (K Kt : RationalMarkovMatrix n)
    (ρ δ w : ℚ) (Cpair : Fin n → Fin n → Fin n → Fin n → ℚ) (Cdef : Fin n → Fin n → Fin n → ℚ)
    (π πt : Fin n → ℚ) (Cinv : Fin n → Fin n → ℚ) (f : Fin n → ℚ)
    (h : checkMetricReceipt d K Kt ρ δ w Cpair Cdef π πt Cinv f = true) :
    ∃ (hπ : IsProb π) (hπt : IsProb πt),
      kernel d K ∘ₘ law d π hπ = law d π hπ ∧ kernel d Kt ∘ₘ law d πt hπt = law d πt hπt ∧
      W1DualLE (law d π hπ) (law d πt hπt) ((δ : ℝ) / (1 - (ρ : ℝ))) := by
  obtain ⟨-, hρ0, hρ1, -, -, hπ, hπt, hinv, hinvt, hCinv, -⟩ :=
    checkMetricReceipt_sound d K Kt ρ δ w Cpair Cdef π πt Cinv f h
  let D : ContractivePerturbation (kernel d K) (kernel d Kt) :=
    { π := law d π hπ
      πt := law d πt hπt
      π_isProb := inferInstance
      πt_isProb := inferInstance
      invariant := law_invariant K π hπ hinv
      invariant_t := law_invariant Kt πt hπt hinvt
      ρ := ρ
      δ := δ
      ρ_nonneg := by exact_mod_cast hρ0
      ρ_lt_one := by exact_mod_cast hρ1
      contraction := checked_row_contraction K Kt ρ δ w Cpair Cdef π πt Cinv f h
      defect := checked_defect K Kt ρ δ w Cpair Cdef π πt Cinv f h
      finite := ⟨_, coupling_w1DualLE π πt hπ hπt Cinv hCinv le_rfl⟩ }
  exact ⟨hπ, hπt, D.invariant, D.invariant_t, D.w1_le⟩

/-- **Exact transport.** The coupling bounds and the potential attains `w`:
    `w` is the least dual Kantorovich–Rubinstein bound between the laws. -/
theorem finite_transport_certificate_sound [Fact (IsFiniteMetric d)] (K Kt : RationalMarkovMatrix n)
    (ρ δ w : ℚ) (Cpair : Fin n → Fin n → Fin n → Fin n → ℚ) (Cdef : Fin n → Fin n → Fin n → ℚ)
    (π πt : Fin n → ℚ) (Cinv : Fin n → Fin n → ℚ) (f : Fin n → ℚ)
    (h : checkMetricReceipt d K Kt ρ δ w Cpair Cdef π πt Cinv f = true) :
    ∃ (hπ : IsProb π) (hπt : IsProb πt),
      W1DualLE (law d π hπ) (law d πt hπt) (w : ℝ) ∧
      ∀ c : ℝ, W1DualLE (law d π hπ) (law d πt hπt) c → (w : ℝ) ≤ c := by
  obtain ⟨-, -, -, -, -, hπ, hπt, -, -, hCinv, hcost, hlip, hval⟩ :=
    checkMetricReceipt_sound d K Kt ρ δ w Cpair Cdef π πt Cinv f h
  refine ⟨hπ, hπt, coupling_w1DualLE π πt hπ hπt Cinv hCinv (by rw [hcost]), fun c hc => ?_⟩
  let g : Pt d → ℝ := fun p => (f p.idx : ℝ)
  have hg : IsKRTest g := by
    refine ⟨Measurable.of_discrete, LipschitzWith.of_dist_le_mul fun p q => ?_, ?_⟩
    · rw [Real.dist_eq, dist_pt, NNReal.coe_one, one_mul]
      rw [abs_le]
      constructor
      · have := hlip q.idx p.idx
        have hs : d q.idx p.idx = d p.idx q.idx := (Fact.out : IsFiniteMetric d).2.1 _ _
        rw [hs] at this
        have : (f q.idx : ℝ) - f p.idx ≤ d p.idx q.idx := by exact_mod_cast this
        simp only [g]
        linarith
      · show (f p.idx : ℝ) - f q.idx ≤ d p.idx q.idx
        exact_mod_cast hlip p.idx q.idx
    · refine ⟨∑ i, |(f i : ℝ)|, fun p => ?_⟩
      have := Finset.single_le_sum (f := fun i => |(f i : ℝ)|) (fun i _ => abs_nonneg _)
        (Finset.mem_univ p.idx)
      simpa [g] using this
  have := hc g hg
  rw [integral_law, integral_law] at this
  have hval' : (∑ i, (π i : ℝ) * g ⟨i⟩) - ∑ j, (πt j : ℝ) * g ⟨j⟩ = (w : ℝ) := by
    rw [← hval]
    push_cast
    simp only [g, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hval'] at this
  exact (le_abs_self _).trans this

end PermanssonResearch.ApplicationBridge.MetricReceipt
