import PermanssonResearch.ReverseSolver.ResidenceEvent
import PermanssonResearch.ReverseSolver.HistoryForwardBridge
import PermanssonResearch.ReverseSolver.HistoryTypedTransport
import PermanssonResearch.ReverseSolver.Bellman
import Mathlib.Tactic

/-!
# D2: exact finite-history objective evaluation and Bellman optimization

The generic evaluator consumes an explicit Boolean terminal test on the
observed finite history. Residence specializes it to the literal block event
proved in ResidenceEvent. The finite-menu, fully observed deterministic
history policy class and real Mathlib partialTraj laws are the unchanged D1
objects. No randomized/partially observed/robust policy theorem is asserted.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch.ReverseSolver.Residence

open HistoryDependent ControlledKernel Bellman
open PermanssonLean.ProbabilitySupport
set_option autoImplicit false
universe uC

/-- Append an independently enumerated successor word to the observed past. -/
def extendHistory {n : ℕ} : PackedHistory n → List (Fin n) → PackedHistory n
  | p, [] => p
  | ⟨i, h⟩, z :: zs => extendHistory ⟨i+1, appendHistory h z⟩ zs

theorem extendHistory_append {n : ℕ} (p : PackedHistory n)
    (xs ys : List (Fin n)) :
    extendHistory p (xs ++ ys) = extendHistory (extendHistory p xs) ys := by
  induction xs generalizing p with
  | nil => rfl
  | cons z zs ih => cases p; exact ih _

/-- Enumerating the actual successors reconstructs the actual full history. -/
theorem extendHistory_actual {n : ℕ} (t : ℕ) (w : History n t) :
    extendHistory ⟨0, singletonPrefix
      (w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le t)⟩)⟩
      (List.ofFn (stepsFromHistory t w)) = ⟨t, w⟩ := by
  induction t with
  | zero =>
      have hw : singletonPrefix (w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 0)⟩) = w := by
        funext j
        have hj : j = ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 0)⟩ := by
          apply Subtype.ext
          exact Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp j.property)
        simp [singletonPrefix, hj]
      simpa [extendHistory] using congrArg
        (fun h : History n 0 => (⟨0, h⟩ : PackedHistory n)) hw
  | succ t ih =>
      let pre := observedPrefix w t t.le_succ
      have hstart : w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le (t+1))⟩ =
          pre ⟨0, Finset.mem_Iic.mpr (Nat.zero_le t)⟩ := rfl
      rw [stepsFromHistory_snoc, extendHistory_append, hstart, ih pre]
      simp only [extendHistory]
      exact congrArg (fun h : History n (t+1) => (⟨t+1, h⟩ : PackedHistory n))
        (appendHistory_reconstruct w)

/-- Independent full-word evaluation, using D1's actual chronological weights. -/
def objectiveEnumeration {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (accept : PackedHistory n → Bool) (D i : ℕ) (h : History n i) (r : ℕ) : ℚ :=
  ((finiteSuccessorWords n r).map fun xs =>
    completionMass sys σ D i h xs *
      (if accept (extendHistory ⟨i, h⟩ xs) then (1 : ℚ) else 0)).sum

theorem sum_map_flatMap_residence {α β : Type*} (xs : List α)
    (f : α → List β) (g : β → ℚ) :
    ((xs.flatMap f).map g).sum = (xs.map fun x => ((f x).map g).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

theorem sum_map_finRange_residence (n : ℕ) (g : Fin n → ℚ) :
    ((List.finRange n).map g).sum = ∑ z : Fin n, g z := by
  rw [← List.sum_toFinset g (List.nodup_finRange n)]
  simp

theorem objectiveEnumeration_succ {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (accept : PackedHistory n → Bool) (D i r : ℕ) (h : History n i) :
    objectiveEnumeration sys σ accept D i h (r+1) =
      ∑ z : Fin n, selectedEntry sys σ D i h z *
        objectiveEnumeration sys σ accept D (i+1) (appendHistory h z) r := by
  unfold objectiveEnumeration
  simp only [finiteSuccessorWords, sum_map_flatMap_residence]
  rw [sum_map_finRange_residence]
  apply Finset.sum_congr rfl
  intro z _
  simp only [List.map_map]
  have hfactor : ∀ xs : List (Fin n),
      completionMass sys σ D i h (z :: xs) *
        (if accept (extendHistory ⟨i, h⟩ (z :: xs)) then (1 : ℚ) else 0) =
      selectedEntry sys σ D i h z *
        (completionMass sys σ D (i+1) (appendHistory h z) xs *
          (if accept (extendHistory ⟨i+1, appendHistory h z⟩ xs)
            then (1 : ℚ) else 0)) := by
    intro xs
    simp only [completionMass, extendHistory]
    ring
  simp only [Function.comp_def, hfactor, List.sum_map_mul_left]

/-- Backwards evaluation under one declared history policy. -/
def objectiveValue {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (accept : PackedHistory n → Bool) (D : ℕ) :
    (r i : ℕ) → History n i → ℚ
  | 0, i, h => if accept ⟨i, h⟩ then 1 else 0
  | r+1, i, h => ∑ z : Fin n, selectedEntry sys σ D i h z *
      objectiveValue sys σ accept D r (i+1) (appendHistory h z)

/-- The backwards recursion agrees with independent full-path enumeration. -/
theorem objectiveEnumeration_eq_value {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (accept : PackedHistory n → Bool) (D r i : ℕ) (h : History n i) :
    objectiveEnumeration sys σ accept D i h r = objectiveValue sys σ accept D r i h := by
  induction r generalizing i with
  | zero =>
      cases hb : accept ⟨i, h⟩ <;>
        simp [objectiveEnumeration, objectiveValue, finiteSuccessorWords,
          completionMass, extendHistory, hb]
  | succ r ih =>
      rw [objectiveEnumeration_succ]
      simp only [objectiveValue, ih]

/-- The true canonical finite-prefix event probability. -/
noncomputable def objectiveProbability {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (accept : PackedHistory n → Bool) (D : ℕ) (x : Fin n) : ℝ≥0∞ :=
  prefixLaw sys σ D x D {w | accept ⟨D, w⟩ = true}

noncomputable def objectivePathSum {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (accept : PackedHistory n → Bool) (D : ℕ) (x : Fin n) : ℚ := by
  classical
  exact ∑ w : History n D,
    if w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le D)⟩ = x ∧ accept ⟨D, w⟩ = true
    then rationalPathWeight sys σ D D w else 0

/-- D1's atom theorem evaluated on the actual new event, not a surrogate law. -/
theorem objectiveProbability_eq_pathSum
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (accept : PackedHistory n → Bool) (D : ℕ) (x : Fin n) :
    objectiveProbability sys σ accept D x =
      ENNReal.ofReal ((objectivePathSum sys σ accept D x : ℚ) : ℝ) := by
  classical
  let μ := prefixLaw sys σ D x D
  let E : Set (History n D) := {w | accept ⟨D, w⟩ = true}
  have hfilter : (↑(Finset.univ.filter (fun w : History n D => w ∈ E)) :
      Set (History n D)) = E := by ext w; simp
  change μ E = _
  have hsum : μ E = ∑ w : History n D, if w ∈ E then μ {w} else 0 := by
    calc
      μ E = μ (↑(Finset.univ.filter (fun w : History n D => w ∈ E)) :
          Set (History n D)) := by rw [hfilter]
      _ = ∑ w ∈ Finset.univ.filter (fun w : History n D => w ∈ E), μ {w} := by
        rw [sum_measure_singleton]
      _ = ∑ w : History n D, if w ∈ E then μ {w} else 0 := by
        simp [Finset.sum_filter]
  rw [hsum]
  have hterm : ∀ w : History n D,
      (if w ∈ E then μ {w} else 0) = ENNReal.ofReal
        ((if w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le D)⟩ = x ∧ accept ⟨D, w⟩ = true
          then rationalPathWeight sys σ D D w else 0 : ℚ) : ℝ) := by
    intro w
    have ha := prefix_atom_product sys σ D x D w
    change (if w ∈ E then prefixLaw sys σ D x D {w} else 0) = _
    rw [ha]
    by_cases hs : w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le D)⟩ = x
    · cases hb : accept ⟨D, w⟩ <;> simp [E, hs, hb]
    · simp [hs]
  simp_rw [hterm]
  have hnonneg : ∀ w ∈ (Finset.univ : Finset (History n D)),
      0 ≤ ((if w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le D)⟩ = x ∧ accept ⟨D, w⟩ = true
        then rationalPathWeight sys σ D D w else 0 : ℚ) : ℝ) := by
    intro w _
    split_ifs
    · exact_mod_cast rationalPathWeight_nonneg sys σ D D w
    · norm_num
  rw [← ENNReal.ofReal_sum_of_nonneg hnonneg]
  unfold objectivePathSum
  congr 1
  norm_cast

theorem objectivePathSum_eq_enumeration
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (accept : PackedHistory n → Bool) (D : ℕ) (x : Fin n) :
    objectivePathSum sys σ accept D x =
      objectiveEnumeration sys σ accept D 0 (singletonPrefix x) D := by
  classical
  unfold objectivePathSum
  calc
    (∑ w : History n D,
      if w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le D)⟩ = x ∧ accept ⟨D, w⟩ = true
      then rationalPathWeight sys σ D D w else 0) =
        ∑ p : Fin n × (Fin D → Fin n),
          if p.1 = x ∧ accept ⟨D, historyFromSteps D p.1 p.2⟩ = true
          then rationalPathWeight sys σ D D (historyFromSteps D p.1 p.2) else 0 := by
      symm
      apply Fintype.sum_equiv (fullHistoryEquiv (n := n) D)
      intro p
      rfl
    _ = ∑ v : Fin D → Fin n,
        if accept ⟨D, historyFromSteps D x v⟩ = true
        then rationalPathWeight sys σ D D (historyFromSteps D x v) else 0 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      simp only [ite_and]
      simp
    _ = ∑ v : Fin D → Fin n,
        completionMass sys σ D 0 (singletonPrefix x) (List.ofFn v) *
          (if accept (extendHistory ⟨0, singletonPrefix x⟩ (List.ofFn v))
          then (1 : ℚ) else 0) := by
      apply Finset.sum_congr rfl
      intro v _
      have hm := completionMass_eq_rationalPathWeight sys σ D D (historyFromSteps D x v)
      have he := extendHistory_actual D (historyFromSteps D x v)
      simp only [historyFromSteps_initial, stepsFromHistory_historyFromSteps] at hm he
      rw [he, hm]
      cases accept ⟨D, historyFromSteps D x v⟩ <;> simp
    _ = objectiveEnumeration sys σ accept D 0 (singletonPrefix x) D := by
      unfold objectiveEnumeration
      exact (finiteSuccessorWords_sum_eq_vectorSum n D
        (fun xs => completionMass sys σ D 0 (singletonPrefix x) xs *
          (if accept (extendHistory ⟨0, singletonPrefix x⟩ xs)
            then (1 : ℚ) else 0))).symm

/-- Genuine event probability = independent enumeration = backwards recursion. -/
theorem objectiveProbability_eq_value
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (accept : PackedHistory n → Bool) (D : ℕ) (x : Fin n) :
    objectiveProbability sys σ accept D x = ENNReal.ofReal
      ((objectiveValue sys σ accept D D 0 (singletonPrefix x) : ℚ) : ℝ) := by
  rw [objectiveProbability_eq_pathSum, objectivePathSum_eq_enumeration,
    objectiveEnumeration_eq_value]

/-- Fully observed finite-history Bellman recursion. Efficient clock-state
compression is a separate obligation, not assumed in this definition. -/
noncomputable def objectiveBellman {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (accept : PackedHistory n → Bool) :
    (r i : ℕ) → History n i → ℚ
  | 0, i, h => if accept ⟨i, h⟩ then 1 else 0
  | r+1, i, h =>
      let v := fun z => objectiveBellman sys accept r (i+1) (appendHistory h z)
      actionScore sys v (last h) (bestControl sys v (last h))

theorem objectiveValue_le_bellman
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (accept : PackedHistory n → Bool) (D r i : ℕ) (h : History n i) :
    objectiveValue sys σ accept D r i h ≤ objectiveBellman sys accept r i h := by
  induction r generalizing i with
  | zero => exact le_rfl
  | succ r ih =>
      change (∑ z : Fin n, selectedEntry sys σ D i h z *
        objectiveValue sys σ accept D r (i+1) (appendHistory h z)) ≤ _
      apply le_trans (Finset.sum_le_sum fun z _ =>
        mul_le_mul_of_nonneg_left (ih (i+1) (appendHistory h z))
          (selectedEntry_nonneg sys σ D i h z))
      exact bestControl_dominates sys _ (last h) (σ.choose D i h) (σ.permitted D i h)

/-- An admissible controller depending only on the observed past and deadline. -/
noncomputable def objectiveMaximizer {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (accept : PackedHistory n → Bool) :
    HistoryPolicy sys where
  choose D i h := bestControl sys
    (fun z => objectiveBellman sys accept (D-(i+1)) (i+1) (appendHistory h z)) (last h)
  permitted D i h := bestControl_mem sys _ (last h)

theorem objectiveMaximizer_attains
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (accept : PackedHistory n → Bool)
    (D r i : ℕ) (h : History n i) (horizon : i+r = D) :
    objectiveValue sys (objectiveMaximizer sys accept) accept D r i h =
      objectiveBellman sys accept r i h := by
  induction r generalizing i with
  | zero => rfl
  | succ r ih =>
      have hsub : D-(i+1) = r := by omega
      let v := fun z => objectiveBellman sys accept r (i+1) (appendHistory h z)
      have hchoose : (objectiveMaximizer sys accept).choose D i h =
          bestControl sys v (last h) := by
        simp only [objectiveMaximizer, hsub]
      change (∑ z : Fin n, selectedEntry sys (objectiveMaximizer sys accept) D i h z *
        objectiveValue sys (objectiveMaximizer sys accept) accept D r (i+1)
          (appendHistory h z)) = actionScore sys v (last h) (bestControl sys v (last h))
      have hrow : ∀ z, selectedEntry sys (objectiveMaximizer sys accept) D i h z =
          (sys.matrix (bestControl sys v (last h))).entry (last h) z := by
        intro z
        unfold selectedEntry
        rw [hchoose]
      simp only [hrow, actionScore]
      apply Finset.sum_congr rfl
      intro z _
      rw [ih (i+1) (appendHistory h z) (by omega)]

/-- Optimization concerns the true path event for every declared history policy. -/
theorem objectiveProbability_optimal_and_attained
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (accept : PackedHistory n → Bool)
    (D : ℕ) (x : Fin n) :
    (∀ σ : HistoryPolicy sys, objectiveProbability sys σ accept D x ≤
      ENNReal.ofReal ((objectiveBellman sys accept D 0 (singletonPrefix x) : ℚ) : ℝ)) ∧
    (∃ σ : HistoryPolicy sys, objectiveProbability sys σ accept D x =
      ENNReal.ofReal ((objectiveBellman sys accept D 0 (singletonPrefix x) : ℚ) : ℝ)) := by
  constructor
  · intro σ
    rw [objectiveProbability_eq_value]
    apply ENNReal.ofReal_le_ofReal
    exact_mod_cast objectiveValue_le_bellman sys σ accept D D 0 (singletonPrefix x)
  · refine ⟨objectiveMaximizer sys accept, ?_⟩
    rw [objectiveProbability_eq_value, objectiveMaximizer_attains sys accept D D 0 _ (by omega)]

/-- Concrete residence terminal test, connected to the block event above. -/
def residenceAccept {n : ℕ} (G : Fin n → Prop) [DecidablePred G]
    (m : ℕ) (p : PackedHistory n) : Bool := hasRun G (m+1) (historyWord p.2)

/-- Exact true-event probability, not merely a claim about the clock. -/
theorem residenceProbability_eq_value
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (G : Fin n → Prop) [DecidablePred G] (m T : ℕ) (x : Fin n) :
    prefixLaw sys σ (T+m) x (T+m) (entryByResidenceEvent G m T) =
      ENNReal.ofReal ((objectiveValue sys σ (residenceAccept G m) (T+m) (T+m)
        0 (singletonPrefix x) : ℚ) : ℝ) :=
  objectiveProbability_eq_value sys σ (residenceAccept G m) (T+m) x

/-- Exact optimality for the literal entry-by-T residence event. -/
theorem residenceProbability_optimal_and_attained
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (G : Fin n → Prop) [DecidablePred G]
    (m T : ℕ) (x : Fin n) :
    (∀ σ : HistoryPolicy sys,
      prefixLaw sys σ (T+m) x (T+m) (entryByResidenceEvent G m T) ≤
        ENNReal.ofReal ((objectiveBellman sys (residenceAccept G m) (T+m)
          0 (singletonPrefix x) : ℚ) : ℝ)) ∧
    (∃ σ : HistoryPolicy sys,
      prefixLaw sys σ (T+m) x (T+m) (entryByResidenceEvent G m T) =
        ENNReal.ofReal ((objectiveBellman sys (residenceAccept G m) (T+m)
          0 (singletonPrefix x) : ℚ) : ℝ)) :=
  objectiveProbability_optimal_and_attained sys (residenceAccept G m) (T+m) x

/-- Transport the actual event using the existing full typed D1 prefix theorem.
The Unit×Fin n realization uses exactly the established alpha/P/U primitives. -/
theorem typed_residenceProbability_eq_value
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (G : Fin n → Prop) [DecidablePred G] (m T : ℕ) (x : Fin n) :
    HistoryDependentTyped.typedPrefixLaw sys σ (T+m) x (T+m)
      (FiniteStrategicPathBridge.prefixEncode (T+m) ⁻¹' entryByResidenceEvent G m T) =
      ENNReal.ofReal ((objectiveValue sys σ (residenceAccept G m) (T+m) (T+m)
        0 (singletonPrefix x) : ℚ) : ℝ) := by
  rw [← Measure.map_apply (FiniteStrategicPathBridge.measurable_prefixEncode (T+m))
    (Set.Finite.measurableSet (Set.toFinite _)),
    HistoryDependentTyped.typed_prefixLaw_map]
  exact residenceProbability_eq_value sys σ G m T x

end PermanssonResearch.ReverseSolver.Residence
