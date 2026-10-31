import PermanssonResearch.ApplicationBridge.ExitReceipt
import PermanssonLean.Probability.FinitePrefixTV
import Mathlib.Tactic

/-!
# ApplicationBridge — finite-horizon perturbation (TV budget) receipts

A perturbation receipt compares a baseline and an alternative rational
Markov matrix on the same joint states: per-row half-L1 distances, their
maximum `δ`, the half-L1 distance of the two initial laws, both complete
region-survival tables, the two initial-law event probabilities and the
budget `min 1 (TV(μ, ν) + T δ)`.

Soundness, on the actual α/P/U realizations:

* `realized_eventTV_le_rowTV` — every one-step event discrepancy is at most
  the row's half-L1 distance, so `δ` is a uniform event-TV bound
  (`HasUniformEventTVBound`);
* `survival_difference_le` — the original core Proposition 5.4
  (`finitePrefix_eventTotalVariation_le_linear`) bounds the survival-event
  discrepancy from a common start by `T δ`;
* `checked_perturbation_bound` — mixing over the two initial laws adds at
  most their half-L1 distance, so the actual event probabilities differ by
  at most the checked budget.

This is a finite-horizon comparison of two declared chains, not a long-run,
GR/PR or causal statement.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch.ApplicationBridge.QuantitativeReceipt

open PermanssonLean
open PermanssonLean.ProbabilitySupport
open PermanssonResearch.ReverseSolver
open PermanssonResearch.ReverseSolver.FiniteStrategicRealization
open PermanssonResearch.ReverseSolver.FiniteStrategicPathBridge
open PermanssonResearch.ApplicationBridge.MenuReceipt
open PermanssonResearch.ApplicationBridge.ExitReceipt

set_option autoImplicit false

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

variable {n : ℕ}

/-- Half-L1 distance of two rows. -/
def rowTV (K L : RationalMarkovMatrix n) (y : Fin n) : ℚ :=
  (∑ z : Fin n, |K.entry y z - L.entry y z|) / 2

/-- Half-L1 distance of two initial laws. -/
def lawTV (μ ν : Fin n → ℚ) : ℚ :=
  (∑ y : Fin n, |μ y - ν y|) / 2

/-! ## Finite real inequalities -/

theorem abs_sum_le_half_of_sum_zero (d : Fin n → ℝ) (hd : ∑ z, d z = 0)
    (D : Finset (Fin n)) :
    |∑ z ∈ D, d z| ≤ (∑ z, |d z|) / 2 := by
  have h1 : ∑ z ∈ D, d z + ∑ z ∈ Dᶜ, d z = 0 := by
    rw [Finset.sum_add_sum_compl]
    exact hd
  have h2 := Finset.abs_sum_le_sum_abs d D
  have h3 := Finset.abs_sum_le_sum_abs d Dᶜ
  have h4 : ∑ z ∈ D, |d z| + ∑ z ∈ Dᶜ, |d z| = ∑ z, |d z| := Finset.sum_add_sum_compl D _
  have h5 : |∑ z ∈ Dᶜ, d z| = |∑ z ∈ D, d z| := by
    rw [show ∑ z ∈ Dᶜ, d z = -(∑ z ∈ D, d z) by linarith, abs_neg]
  linarith

theorem abs_weighted_le_half (d q : Fin n → ℝ) (hd : ∑ y, d y = 0)
    (hq : ∀ y, 0 ≤ q y ∧ q y ≤ 1) :
    |∑ y, d y * q y| ≤ (∑ y, |d y|) / 2 := by
  have hshift : ∑ y, d y * q y = ∑ y, d y * (q y - 1 / 2) := by
    have : ∑ y, d y * (q y - 1 / 2) = ∑ y, d y * q y - (∑ y, d y) / 2 := by
      rw [Finset.sum_div, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y _
      ring
    rw [this, hd]
    ring
  rw [hshift]
  calc |∑ y, d y * (q y - 1 / 2)| ≤ ∑ y, |d y * (q y - 1 / 2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y, |d y| * (1 / 2) := by
        apply Finset.sum_le_sum
        intro y _
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [abs_le]
        constructor <;> linarith [(hq y).1, (hq y).2]
    _ = (∑ y, |d y|) / 2 := by
        rw [← Finset.sum_mul]
        ring

/-! ## One-step event total variation of realized rows -/

open Classical in
theorem realized_kernel_real (K : RationalMarkovMatrix n) (y : Fin n)
    (S : Set (JointState Unit (Fin n))) :
    ((realizedModel K).inducedKernel (decode y)).real S =
      ∑ z ∈ Finset.univ.filter (fun z => decode z ∈ S), (K.entry y z : ℝ) := by
  classical
  have hS : S = encode ⁻¹' ↑(Finset.univ.filter (fun z : Fin n => decode z ∈ S)) := by
    ext w
    simp
  have hcyl := inducedKernel_worldCylinder K y
    (MeasurableSet.of_discrete (s := ↑(Finset.univ.filter (fun z : Fin n => decode z ∈ S))))
  unfold Measure.real
  rw [hS, hcyl, ← sum_measure_singleton]
  simp only [rationalFiniteKernel_singleton]
  rw [ENNReal.toReal_sum (fun z _ => ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr
  · ext z
    simp
  · intro z _
    exact ENNReal.toReal_ofReal (by exact_mod_cast K.entry_nonneg y z)

theorem realized_eventTV_le_rowTV (K L : RationalMarkovMatrix n) (y : Fin n) :
    eventTotalVariation ((realizedModel K).inducedKernel (decode y))
      ((realizedModel L).inducedKernel (decode y)) ≤ (rowTV K L y : ℝ) := by
  classical
  unfold eventTotalVariation
  apply csSup_le (eventTVCandidates_nonempty _ _)
  rintro r ⟨S, -, rfl⟩
  rw [realized_kernel_real, realized_kernel_real, ← Finset.sum_sub_distrib]
  have hzero : ∑ z, ((K.entry y z : ℝ) - (L.entry y z : ℝ)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have hK : (∑ z, (K.entry y z : ℝ)) = 1 := by exact_mod_cast K.row_sum_one y
    have hL : (∑ z, (L.entry y z : ℝ)) = 1 := by exact_mod_cast L.row_sum_one y
    rw [hK, hL]
    ring
  have h := abs_sum_le_half_of_sum_zero _ hzero (Finset.univ.filter (fun z => decode z ∈ S))
  unfold rowTV
  push_cast
  exact h

theorem realized_uniformTV (K L : RationalMarkovMatrix n) (δ : ℚ)
    (hrow : ∀ y, rowTV K L y ≤ δ) :
    HasUniformEventTVBound (realizedModel K).inducedKernel
      (realizedModel L).inducedKernel (δ : ℝ) := by
  intro w
  have hw : w = decode (encode w) := (decode_encode w).symm
  rw [hw]
  exact (realized_eventTV_le_rowTV K L (encode w)).trans (by exact_mod_cast hrow (encode w))

/-- From a common start, the region-survival probabilities of the two
    realized chains differ by at most `T δ` (core Proposition 5.4). -/
theorem survival_difference_le (K L : RationalMarkovMatrix n) (B : Finset (Fin n))
    (δ : ℚ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (hrow : ∀ y, rowTV K L y ≤ δ) (y : Fin n) (T : ℕ) :
    |((realizedModel K).pathLaw (Measure.dirac (decode y))).real (staysThrough B T) -
      ((realizedModel L).pathLaw (Measure.dirac (decode y))).real (staysThrough B T)| ≤
      (T : ℝ) * δ := by
  let S := (successPrefixEvent (typedTarget (exitTarget B)) T)ᶜ
  have hS : MeasurableSet S := (measurableSet_successPrefixEvent _ T).compl
  have hpre : staysThrough B T = (Preorder.frestrictLe T) ⁻¹' S := by
    rw [staysThrough_eq_compl]
    rfl
  have hprefix : ∀ M : RationalMarkovMatrix n,
      ((realizedModel M).pathLaw (Measure.dirac (decode y))).real (staysThrough B T) =
        (finitePrefixLaw (realizedModel M).inducedKernel (decode y) T).real S := by
    intro M
    rw [hpre, ← realized_pathLaw_prefix M (decode y) T]
    unfold Measure.real
    rw [Measure.map_apply (Preorder.measurable_frestrictLe T) hS]
  rw [hprefix K, hprefix L]
  have hδ0 : (0 : ℝ) ≤ δ := by exact_mod_cast h0
  have hδ1 : (δ : ℝ) ≤ 1 := by exact_mod_cast h1
  exact (abs_measureReal_sub_le_eventTotalVariation _ _ hS).trans
    (finitePrefix_eventTotalVariation_le_linear _ _ hδ0 hδ1 (realized_uniformTV K L δ hrow)
      (decode y) T)

/-! ## Receipt checks -/

/-- Exact row distances and their maximum, both complete survival tables,
    normalized initial laws, the initial-law distance, the budget and both
    initial-law event probabilities. -/
def PerturbationChecks (K L : RationalMarkovMatrix n) (B : Finset (Fin n)) (horizon : ℕ)
    (μ ν : Fin n → ℚ) (rows : Fin n → ℚ) (δ tv0 bound : ℚ)
    (base alt : ℕ → Fin n → ℚ) (pb pa : ℚ) : Prop :=
  (∀ y, rows y = rowTV K L y) ∧ (∀ y, rows y ≤ δ) ∧ (∃ y, rows y = δ) ∧ δ ≤ 1 ∧
  (∀ y, 0 ≤ μ y) ∧ (∑ y, μ y) = 1 ∧ (∀ y, 0 ≤ ν y) ∧ (∑ y, ν y) = 1 ∧
  tv0 = lawTV μ ν ∧ bound = min 1 (tv0 + horizon * δ) ∧
  (∀ t : Fin (horizon + 1), ∀ y, base t.val y = 1 - rationalHittingValue K (exitTarget B) t.val y) ∧
  (∀ t : Fin (horizon + 1), ∀ y, alt t.val y = 1 - rationalHittingValue L (exitTarget B) t.val y) ∧
  pb = ∑ y, μ y * base horizon y ∧ pa = ∑ y, ν y * alt horizon y

instance (K L : RationalMarkovMatrix n) (B : Finset (Fin n)) (horizon : ℕ)
    (μ ν : Fin n → ℚ) (rows : Fin n → ℚ) (δ tv0 bound : ℚ)
    (base alt : ℕ → Fin n → ℚ) (pb pa : ℚ) :
    Decidable (PerturbationChecks K L B horizon μ ν rows δ tv0 bound base alt pb pa) := by
  unfold PerturbationChecks
  infer_instance

def checkFiniteTVBudget (K L : RationalMarkovMatrix n) (B : Finset (Fin n)) (horizon : ℕ)
    (μ ν : Fin n → ℚ) (rows : Fin n → ℚ) (δ tv0 bound : ℚ)
    (base alt : ℕ → Fin n → ℚ) (pb pa : ℚ) : Bool :=
  decide (PerturbationChecks K L B horizon μ ν rows δ tv0 bound base alt pb pa)

theorem checkFiniteTVBudget_sound (K L : RationalMarkovMatrix n) (B : Finset (Fin n))
    (horizon : ℕ) (μ ν : Fin n → ℚ) (rows : Fin n → ℚ) (δ tv0 bound : ℚ)
    (base alt : ℕ → Fin n → ℚ) (pb pa : ℚ)
    (h : checkFiniteTVBudget K L B horizon μ ν rows δ tv0 bound base alt pb pa = true) :
    PerturbationChecks K L B horizon μ ν rows δ tv0 bound base alt pb pa := by
  unfold checkFiniteTVBudget at h
  exact of_decide_eq_true h

section Receipt

variable (K L : RationalMarkovMatrix n) (B : Finset (Fin n)) (horizon : ℕ)
  (μ ν : Fin n → ℚ) (rows : Fin n → ℚ) (δ tv0 bound : ℚ)
  (base alt : ℕ → Fin n → ℚ) (pb pa : ℚ)
  (h : checkFiniteTVBudget K L B horizon μ ν rows δ tv0 bound base alt pb pa = true)
include h

/-- Every checked row distance bounds the actual one-step event TV of that row. -/
theorem checked_row_eventTV (y : Fin n) :
    eventTotalVariation ((realizedModel K).inducedKernel (decode y))
      ((realizedModel L).inducedKernel (decode y)) ≤ (rows y : ℝ) := by
  have hrow := (checkFiniteTVBudget_sound K L B horizon μ ν rows δ tv0 bound base alt pb pa h).1 y
  rw [hrow]
  exact realized_eventTV_le_rowTV K L y

/-- The checked event probabilities are initial-law mixtures of actual
    region-survival probabilities of the two realized chains. -/
theorem checked_event_probabilities :
    (pb : ℝ) = ∑ y, (μ y : ℝ) *
        ((realizedModel K).pathLaw (Measure.dirac (decode y))).real (staysThrough B horizon) ∧
    (pa : ℝ) = ∑ y, (ν y : ℝ) *
        ((realizedModel L).pathLaw (Measure.dirac (decode y))).real (staysThrough B horizon) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hbase, halt, hpb, hpa⟩ :=
    checkFiniteTVBudget_sound K L B horizon μ ν rows δ tv0 bound base alt pb pa h
  constructor
  · rw [hpb]
    push_cast
    apply Finset.sum_congr rfl
    intro y _
    rw [survival_actual, hbase ⟨horizon, Nat.lt_succ_self _⟩ y]
    push_cast
    ring
  · rw [hpa]
    push_cast
    apply Finset.sum_congr rfl
    intro y _
    rw [survival_actual, halt ⟨horizon, Nat.lt_succ_self _⟩ y]
    push_cast
    ring

/-- The actual initial-law survival probabilities of the two chains differ by
    at most the checked budget `min 1 (TV(μ, ν) + T δ)`. -/
theorem checked_perturbation_bound :
    |∑ y, (μ y : ℝ) *
        ((realizedModel K).pathLaw (Measure.dirac (decode y))).real (staysThrough B horizon) -
      ∑ y, (ν y : ℝ) *
        ((realizedModel L).pathLaw (Measure.dirac (decode y))).real (staysThrough B horizon)| ≤
      (bound : ℝ) := by
  obtain ⟨-, hle, ⟨y0, hy0⟩, hδ1, hμ0, hμ1, hν0, hν1, htv, hbound, -, -, -, -⟩ :=
    checkFiniteTVBudget_sound K L B horizon μ ν rows δ tv0 bound base alt pb pa h
  have hrows := (checkFiniteTVBudget_sound K L B horizon μ ν rows δ tv0 bound base alt pb pa h).1
  have hrow : ∀ y, rowTV K L y ≤ δ := fun y => hrows y ▸ hle y
  have hδ0 : 0 ≤ δ := by
    rw [← hy0, hrows y0]
    unfold rowTV
    positivity
  set p : Fin n → ℝ := fun y =>
    ((realizedModel K).pathLaw (Measure.dirac (decode y))).real (staysThrough B horizon)
  set q : Fin n → ℝ := fun y =>
    ((realizedModel L).pathLaw (Measure.dirac (decode y))).real (staysThrough B horizon)
  have hq : ∀ y, 0 ≤ q y ∧ q y ≤ 1 := fun y => ⟨measureReal_nonneg, measureReal_le_one⟩
  have hp : ∀ y, 0 ≤ p y ∧ p y ≤ 1 := fun y => ⟨measureReal_nonneg, measureReal_le_one⟩
  have hpq : ∀ y, |p y - q y| ≤ (horizon : ℝ) * δ :=
    fun y => survival_difference_le K L B δ hδ0 hδ1 hrow y horizon
  have hμ1' : (∑ y, (μ y : ℝ)) = 1 := by exact_mod_cast hμ1
  have hν1' : (∑ y, (ν y : ℝ)) = 1 := by exact_mod_cast hν1
  have hsplit : ∑ y, (μ y : ℝ) * p y - ∑ y, (ν y : ℝ) * q y =
      ∑ y, (μ y : ℝ) * (p y - q y) + ∑ y, ((μ y : ℝ) - ν y) * q y := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hfirst : |∑ y, (μ y : ℝ) * (p y - q y)| ≤ (horizon : ℝ) * δ := by
    calc |∑ y, (μ y : ℝ) * (p y - q y)| ≤ ∑ y, |(μ y : ℝ) * (p y - q y)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y, (μ y : ℝ) * ((horizon : ℝ) * δ) := by
          apply Finset.sum_le_sum
          intro y _
          rw [abs_mul, abs_of_nonneg (by exact_mod_cast hμ0 y)]
          exact mul_le_mul_of_nonneg_left (hpq y) (by exact_mod_cast hμ0 y)
      _ = (horizon : ℝ) * δ := by rw [← Finset.sum_mul, hμ1', one_mul]
  have hsecond : |∑ y, ((μ y : ℝ) - ν y) * q y| ≤ (tv0 : ℝ) := by
    have hd : ∑ y, ((μ y : ℝ) - ν y) = 0 := by rw [Finset.sum_sub_distrib, hμ1', hν1']; ring
    have hw := abs_weighted_le_half (fun y => (μ y : ℝ) - ν y) q hd hq
    rw [htv]
    unfold lawTV
    push_cast
    exact hw
  have hone : |∑ y, (μ y : ℝ) * p y - ∑ y, (ν y : ℝ) * q y| ≤ 1 := by
    have hpm : 0 ≤ ∑ y, (μ y : ℝ) * p y ∧ ∑ y, (μ y : ℝ) * p y ≤ 1 := by
      constructor
      · exact Finset.sum_nonneg (fun y _ => mul_nonneg (by exact_mod_cast hμ0 y) (hp y).1)
      · calc ∑ y, (μ y : ℝ) * p y ≤ ∑ y, (μ y : ℝ) * 1 :=
              Finset.sum_le_sum (fun y _ =>
                mul_le_mul_of_nonneg_left (hp y).2 (by exact_mod_cast hμ0 y))
          _ = 1 := by simp [hμ1']
    have hqm : 0 ≤ ∑ y, (ν y : ℝ) * q y ∧ ∑ y, (ν y : ℝ) * q y ≤ 1 := by
      constructor
      · exact Finset.sum_nonneg (fun y _ => mul_nonneg (by exact_mod_cast hν0 y) (hq y).1)
      · calc ∑ y, (ν y : ℝ) * q y ≤ ∑ y, (ν y : ℝ) * 1 :=
              Finset.sum_le_sum (fun y _ =>
                mul_le_mul_of_nonneg_left (hq y).2 (by exact_mod_cast hν0 y))
          _ = 1 := by simp [hν1']
    rw [abs_le]
    constructor <;> linarith [hpm.1, hpm.2, hqm.1, hqm.2]
  have hsum : |∑ y, (μ y : ℝ) * p y - ∑ y, (ν y : ℝ) * q y| ≤ (tv0 : ℝ) + horizon * δ := by
    rw [hsplit]
    calc _ ≤ |∑ y, (μ y : ℝ) * (p y - q y)| + |∑ y, ((μ y : ℝ) - ν y) * q y| := abs_add_le _ _
      _ ≤ (horizon : ℝ) * δ + tv0 := add_le_add hfirst hsecond
      _ = (tv0 : ℝ) + horizon * δ := by ring
  rw [hbound]
  push_cast
  exact le_min hone hsum

end Receipt

end PermanssonResearch.ApplicationBridge.QuantitativeReceipt
