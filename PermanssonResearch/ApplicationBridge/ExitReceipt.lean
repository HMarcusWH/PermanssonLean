import PermanssonResearch.ApplicationBridge.MenuReceipt
import PermanssonResearch.ReverseSolver.FiniteStrategicPathBridge
import PermanssonResearch.ReverseSolver.TypedStoppedClassAbsorption
import PermanssonResearch.ReverseSolver.TypedStoppedClassSelection
import PermanssonResearch.ReverseSolver.RationalCertificateUniqueness
import PermanssonResearch.ReverseSolver.RationalCramerCertification
import PermanssonLean.StrategicWorld.PathLaw
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Tactic

/-!
# ApplicationBridge — first-exit routing receipts

For a fixed rational Markov matrix `K` and a region `B`, an exit receipt
reports, for every start in `B`, the probability of staying in `B` through
each step, the probability that the first visit outside `B` is at each
outside state `d` at each step, the eventual first-exit probability to each
`d`, and the never-exit mass. Nothing is normalized: exit probabilities form a
subprobability and the never-exit mass is kept separately.

All four quantities are identified with events of the actual infinite path
law of the α/P/U realization of `K`:

* finite horizons — the rational hitting recursion with goal `{d}` and
  forbidden `Bᶜ \ {d}` is the canonical finite-prefix probability
  (`typedHittingValue_eq_rational_all_horizons`);
* eventual routing — the exit-stopped matrix `stopOutside K B` (outside rows
  replaced by self-loops) has the same finite-horizon routing values, so by
  monotone continuity the eventual first-exit probability under `K` equals the
  eventual hitting probability of `{d}` under the stopped chain, which is its
  checked C10 Dirichlet absorption weight;
* never-exit — paths that never leave `B` are exactly the complement of the
  disjoint first-exit events.

Restart laws after exit, switch retention and GR/PR statements are not
claimed here.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace PermanssonResearch.ApplicationBridge.ExitReceipt

open PermanssonLean
open PermanssonLean.ProbabilitySupport
open PermanssonResearch.ReverseSolver
open PermanssonResearch.ReverseSolver.C10
open PermanssonResearch.ReverseSolver.FiniteStrategicRealization
open PermanssonResearch.ReverseSolver.FiniteStrategicPathBridge
open PermanssonResearch.ApplicationBridge.MenuReceipt

set_option autoImplicit false

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

variable {n : ℕ}

/-! ## Rational exit-stopped chains -/

/-- `K` inside `B`; every state outside `B` becomes absorbing. -/
def stopOutside (K : RationalMarkovMatrix n) (B : Finset (Fin n)) : RationalMarkovMatrix n where
  entry y z := if y ∈ B then K.entry y z else if z = y then 1 else 0
  entry_nonneg y z := by
    by_cases hy : y ∈ B
    · simp only [hy, ite_true]
      exact K.entry_nonneg y z
    · simp only [hy, ite_false]
      split_ifs <;> norm_num
  row_sum_one y := by
    by_cases hy : y ∈ B
    · simp only [hy, ite_true]
      exact K.row_sum_one y
    · simp [hy]

/-- First exit at `d`: hit `d` before any other state outside `B`. -/
def routeTarget (B : Finset (Fin n)) (d : Fin n) : RationalHittingTarget n where
  goal := {d}
  forbidden := Bᶜ.erase d
  disjoint := by simp

theorem stopOutside_entry_outside (K : RationalMarkovMatrix n) (B : Finset (Fin n))
    {y : Fin n} (hy : y ∉ B) (z : Fin n) :
    (stopOutside K B).entry y z = if z = y then 1 else 0 := by
  simp [stopOutside, hy]

/-- Plain hitting of `d`. -/
def hitTarget (d : Fin n) : RationalHittingTarget n where
  goal := {d}
  forbidden := ∅
  disjoint := by simp

/-- Rows outside `B` are never read when every outside state is terminal. -/
theorem rationalHittingValue_stopOutside (K : RationalMarkovMatrix n) (B : Finset (Fin n))
    (rt : RationalHittingTarget n)
    (hcover : ∀ y, y ∉ B → y ∈ rt.goal ∨ y ∈ rt.forbidden) :
    ∀ t y, rationalHittingValue (stopOutside K B) rt t y = rationalHittingValue K rt t y := by
  intro t
  induction t with
  | zero => intro y; rfl
  | succ t ih =>
    intro y
    rw [rationalHittingValue_succ, rationalHittingValue_succ]
    by_cases hg : y ∈ rt.goal
    · simp [hg]
    by_cases hf : y ∈ rt.forbidden
    · simp [hg, hf]
    have hy : y ∈ B := by
      by_contra hy
      rcases hcover y hy with h | h
      · exact hg h
      · exact hf h
    simp only [hg, hf, ite_false]
    apply Finset.sum_congr rfl
    intro z _
    rw [ih z]
    simp [stopOutside, hy]

/-- An absorbed outside state other than `d` never reaches `d`. -/
theorem stopOutside_absorbed (K : RationalMarkovMatrix n) (B : Finset (Fin n))
    (d y : Fin n) (hy : y ∉ B) (hyd : y ≠ d) :
    ∀ t, rationalHittingValue (stopOutside K B) (hitTarget d) t y = 0 := by
  intro t
  induction t with
  | zero => simp [hitTarget, hyd]
  | succ t ih =>
    rw [rationalHittingValue_succ]
    have hg : y ∉ (hitTarget d).goal := by simp [hitTarget, hyd]
    have hf : y ∉ (hitTarget d).forbidden := by simp [hitTarget]
    simp only [hg, hf, ite_false, stopOutside_entry_outside K B hy, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact ih

/-- In the stopped chain, hitting `d` and first exit at `d` coincide. -/
theorem stopOutside_hit_eq_route (K : RationalMarkovMatrix n) (B : Finset (Fin n))
    (d : Fin n) (hd : d ∉ B) :
    ∀ t y, rationalHittingValue (stopOutside K B) (hitTarget d) t y =
      rationalHittingValue (stopOutside K B) (routeTarget B d) t y := by
  intro t
  induction t with
  | zero => intro y; simp [hitTarget, routeTarget]
  | succ t ih =>
    intro y
    by_cases hyd : y = d
    · subst hyd
      rw [rationalHittingValue_succ, rationalHittingValue_succ]
      simp [hitTarget, routeTarget]
    by_cases hy : y ∈ B
    · rw [rationalHittingValue_succ, rationalHittingValue_succ]
      have h1 : y ∉ (hitTarget d).goal := by simp [hitTarget, hyd]
      have h2 : y ∉ (hitTarget d).forbidden := by simp [hitTarget]
      have h3 : y ∉ (routeTarget B d).goal := by simp [routeTarget, hyd]
      have h4 : y ∉ (routeTarget B d).forbidden := by simp [routeTarget, hy]
      simp only [h1, h2, h3, h4, ite_false]
      apply Finset.sum_congr rfl
      intro z _
      rw [ih z]
    · rw [stopOutside_absorbed K B d y hy hyd (t + 1), rationalHittingValue_succ]
      have h3 : y ∉ (routeTarget B d).goal := by simp [routeTarget, hyd]
      have h4 : y ∈ (routeTarget B d).forbidden := by simp [routeTarget, hy, hyd]
      simp [h3, h4]

/-- Finite-horizon first-exit routing is the same for `K` and its stopped chain. -/
theorem stopped_hit_eq_route (K : RationalMarkovMatrix n) (B : Finset (Fin n))
    (d : Fin n) (hd : d ∉ B) (t : ℕ) (y : Fin n) :
    rationalHittingValue (stopOutside K B) (hitTarget d) t y =
      rationalHittingValue K (routeTarget B d) t y := by
  rw [stopOutside_hit_eq_route K B d hd t y]
  refine rationalHittingValue_stopOutside K B (routeTarget B d) ?_ t y
  intro z hz
  by_cases hzd : z = d
  · left
    simp [routeTarget, hzd]
  · right
    simp [routeTarget, hz, hzd]

/-! ## Path events -/

variable {Y : Type*} [MeasurableSpace Y]

theorem mem_prefix_success_iff (ft : FrozenHittingTarget Y) (T : ℕ) (w : ℕ → Y) :
    w ∈ (Preorder.frestrictLe T) ⁻¹' successPrefixEvent ft T ↔
      ∃ t ≤ T, w t ∈ ft.goal ∧ ∀ u < t, w u ∉ ft.forbidden := by
  simp only [Set.mem_preimage, successPrefixEvent, Set.mem_iUnion, Set.mem_inter_iff,
    Set.mem_ofPred_eq, Set.mem_iInter, Preorder.frestrictLe_apply]
  constructor
  · rintro ⟨⟨t, ht⟩, hg, hf⟩
    have htT : t ≤ T := Finset.mem_Iic.mp ht
    refine ⟨t, htT, hg, fun u hu => ?_⟩
    exact hf ⟨u, Finset.mem_Iic.mpr (by omega)⟩ hu
  · rintro ⟨t, ht, hg, hf⟩
    exact ⟨⟨t, Finset.mem_Iic.mpr ht⟩, hg, fun u hu => hf u hu⟩

/-- Stayed in `B` at observation times `0..T`. -/
def staysThrough (B : Finset (Fin n)) (T : ℕ) : Set (ℕ → JointState Unit (Fin n)) :=
  {w | ∀ u ≤ T, encode (w u) ∈ B}

/-- Never left `B`. -/
def staysForever (B : Finset (Fin n)) : Set (ℕ → JointState Unit (Fin n)) :=
  {w | ∀ u, encode (w u) ∈ B}

/-- The first state outside `B` is `d`, reached by time `T`. -/
def firstExitBy (B : Finset (Fin n)) (d : Fin n) (T : ℕ) : Set (ℕ → JointState Unit (Fin n)) :=
  {w | ∃ t ≤ T, encode (w t) = d ∧ ∀ u < t, encode (w u) ∈ B}

/-- The first state outside `B` is `d`, at some finite time. -/
def firstExitAt (B : Finset (Fin n)) (d : Fin n) : Set (ℕ → JointState Unit (Fin n)) :=
  {w | ∃ t, encode (w t) = d ∧ ∀ u < t, encode (w u) ∈ B}

/-- Ever at `d`. -/
def everAt (d : Fin n) : Set (ℕ → JointState Unit (Fin n)) :=
  {w | ∃ t, encode (w t) = d}

theorem typedTarget_goal_iff (rt : RationalHittingTarget n) (y : JointState Unit (Fin n)) :
    y ∈ (typedTarget rt).goal ↔ encode y ∈ rt.goal := by
  simp [typedTarget, rationalTargetAsFrozen]

theorem typedTarget_forbidden_iff (rt : RationalHittingTarget n) (y : JointState Unit (Fin n)) :
    y ∈ (typedTarget rt).forbidden ↔ encode y ∈ rt.forbidden := by
  simp [typedTarget, rationalTargetAsFrozen]

theorem firstExitBy_eq_prefix (B : Finset (Fin n)) (d : Fin n) (T : ℕ) :
    firstExitBy B d T =
      (Preorder.frestrictLe T) ⁻¹' successPrefixEvent (typedTarget (routeTarget B d)) T := by
  ext w
  rw [mem_prefix_success_iff]
  simp only [typedTarget_goal_iff, typedTarget_forbidden_iff, firstExitBy, Set.mem_ofPred_eq,
    routeTarget, Finset.mem_singleton, Finset.mem_erase, Finset.mem_compl, not_and, not_not]
  constructor
  · rintro ⟨t, ht, hdt, hB⟩
    exact ⟨t, ht, hdt, fun u hu _ => hB u hu⟩
  · rintro ⟨t, ht, hdt, hf⟩
    classical
    have hex : ∃ s, encode (w s) = d := ⟨t, hdt⟩
    refine ⟨Nat.find hex, le_trans (Nat.find_min' hex hdt) ht, Nat.find_spec hex, ?_⟩
    intro u hu
    have hne : encode (w u) ≠ d := Nat.find_min hex hu
    exact hf u (lt_of_lt_of_le hu (Nat.find_min' hex hdt)) hne

theorem everAt_eq_iUnion (d : Fin n) :
    everAt d = ⋃ T : ℕ,
      (Preorder.frestrictLe T) ⁻¹' successPrefixEvent (typedTarget (hitTarget d)) T := by
  ext w
  simp only [everAt, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, (mem_prefix_success_iff _ t w).mpr ⟨t, le_rfl, ?_, fun u _ => ?_⟩⟩
    · simp [typedTarget_goal_iff, hitTarget, ht]
    · simp [typedTarget_forbidden_iff, hitTarget]
  · rintro ⟨T, hT⟩
    obtain ⟨t, -, hg, -⟩ := (mem_prefix_success_iff _ T w).mp hT
    exact ⟨t, by simpa [typedTarget_goal_iff, hitTarget] using hg⟩

theorem hit_prefix_monotone (d : Fin n) :
    Monotone (fun T : ℕ =>
      (Preorder.frestrictLe (π := fun _ : ℕ => JointState Unit (Fin n)) T) ⁻¹'
        successPrefixEvent (typedTarget (hitTarget d)) T) := by
  intro S T hST w hw
  obtain ⟨t, ht, hg, hf⟩ := (mem_prefix_success_iff _ S w).mp hw
  exact (mem_prefix_success_iff _ T w).mpr ⟨t, le_trans ht hST, hg, hf⟩

theorem firstExitBy_monotone (B : Finset (Fin n)) (d : Fin n) :
    Monotone (firstExitBy B d) := by
  intro S T hST w hw
  obtain ⟨t, ht, hg, hf⟩ := hw
  exact ⟨t, le_trans ht hST, hg, hf⟩

theorem firstExitAt_eq_iUnion (B : Finset (Fin n)) (d : Fin n) :
    firstExitAt B d = ⋃ T : ℕ, firstExitBy B d T := by
  ext w
  simp only [firstExitAt, firstExitBy, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨t, hdt, hB⟩
    exact ⟨t, t, le_rfl, hdt, hB⟩
  · rintro ⟨T, t, -, hdt, hB⟩
    exact ⟨t, hdt, hB⟩

theorem measurable_firstExitAt (B : Finset (Fin n)) (d : Fin n) :
    MeasurableSet (firstExitAt B d) := by
  rw [firstExitAt_eq_iUnion]
  refine MeasurableSet.iUnion (fun T => ?_)
  rw [firstExitBy_eq_prefix B d T]
  exact (measurableSet_successPrefixEvent _ T).preimage (Preorder.measurable_frestrictLe T)

theorem staysThrough_eq_compl (B : Finset (Fin n)) (T : ℕ) :
    staysThrough B T =
      ((Preorder.frestrictLe T) ⁻¹' successPrefixEvent (typedTarget (exitTarget B)) T)ᶜ := by
  ext w
  rw [Set.mem_compl_iff, mem_prefix_success_iff]
  simp only [staysThrough, Set.mem_ofPred_eq, typedTarget_goal_iff, typedTarget_forbidden_iff,
    exitTarget, Finset.mem_compl, Finset.notMem_empty, not_false_eq_true, implies_true, and_true,
    not_exists, not_and, not_not]

/-- Paths either never leave `B` or leave it first at exactly one outside state. -/
theorem staysForever_eq_compl (B : Finset (Fin n)) :
    staysForever B = (⋃ d ∈ Bᶜ, firstExitAt B d)ᶜ := by
  classical
  ext w
  simp only [staysForever, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, firstExitAt,
    Finset.mem_compl, exists_prop, not_exists, not_and]
  constructor
  · intro hall d hd t hdt _
    exact hd (hdt ▸ hall t)
  · intro hnone u
    by_contra hu
    have hex : ∃ s, encode (w s) ∉ B := ⟨u, hu⟩
    exact hnone (encode (w (Nat.find hex))) (Nat.find_spec hex) (Nat.find hex) rfl
      (fun v hv => not_not.mp (Nat.find_min hex hv))

theorem firstExitAt_pairwise_disjoint (B : Finset (Fin n)) :
    Set.PairwiseDisjoint (↑(Bᶜ) : Set (Fin n)) (firstExitAt B) := by
  intro d hd e he hde
  rw [Function.onFun, Set.disjoint_left]
  rintro w ⟨t, hdt, hBt⟩ ⟨s, hes, hBs⟩
  have hd' : d ∉ B := Finset.mem_compl.mp hd
  have he' : e ∉ B := Finset.mem_compl.mp he
  rcases lt_trichotomy t s with hts | rfl | hst
  · exact hd' (hdt ▸ hBs t hts)
  · exact hde (hdt.symm.trans hes)
  · exact he' (hes ▸ hBt s hst)

/-! ## Actual path-law identifications -/

/-- The Dirac-started path law of a realized matrix has the finite-prefix marginal. -/
theorem realized_pathLaw_prefix (K : RationalMarkovMatrix n) (y : JointState Unit (Fin n))
    (T : ℕ) :
    ((realizedModel K).pathLaw (Measure.dirac y)).map (Preorder.frestrictLe T) =
      finitePrefixLaw (realizedModel K).inducedKernel y T := by
  have hdirac : (realizedModel K).pathLaw (Measure.dirac y) =
      Kernel.traj
        (fun m => PermanssonLean.StrategicWorldModel.stationaryHistoryKernel
          (realizedModel K).inducedKernel m)
        0 (singletonPrefix y) := by
    unfold PermanssonLean.StrategicWorldModel.pathLaw
    unfold Kernel.trajMeasure
    rw [Measure.map_dirac y]
    rw [Measure.dirac_bind (Kernel.measurable _)]
    rfl
  rw [hdirac]
  have h := Kernel.traj_map_frestrictLe_apply
    (X := fun _ : ℕ => JointState Unit (Fin n))
    (κ := fun m => PermanssonLean.StrategicWorldModel.stationaryHistoryKernel
      (realizedModel K).inducedKernel m)
    0 T (singletonPrefix y)
  simpa only [finitePrefixLaw, PermanssonLean.StrategicWorldModel.stationaryHistoryKernel,
    stationaryPrefixKernel] using h

/-- Every rational finite-horizon hitting value is the actual path-law
    probability of the corresponding prefix event. -/
theorem realized_prefix_hitting (K : RationalMarkovMatrix n) (rt : RationalHittingTarget n)
    (x : Fin n) (T : ℕ) :
    ((realizedModel K).pathLaw (Measure.dirac (decode x))).real
      ((Preorder.frestrictLe T) ⁻¹' successPrefixEvent (typedTarget rt) T) =
      (rationalHittingValue K rt T x : ℝ) := by
  have hE := measurableSet_successPrefixEvent (typedTarget rt) T
  have hm : ((realizedModel K).pathLaw (Measure.dirac (decode x)))
      ((Preorder.frestrictLe T) ⁻¹' successPrefixEvent (typedTarget rt) T) =
      finitePrefixLaw (realizedModel K).inducedKernel (decode x) T
        (successPrefixEvent (typedTarget rt) T) := by
    rw [← realized_pathLaw_prefix K (decode x) T]
    exact (Measure.map_apply (Preorder.measurable_frestrictLe T) hE).symm
  have key := typedHittingValue_eq_rational_all_horizons K rt x T
  unfold hittingValue at key
  unfold Measure.real
  rw [hm]
  exact key

theorem survival_actual (K : RationalMarkovMatrix n) (B : Finset (Fin n)) (x : Fin n) (T : ℕ) :
    ((realizedModel K).pathLaw (Measure.dirac (decode x))).real (staysThrough B T) =
      1 - (rationalHittingValue K (exitTarget B) T x : ℝ) := by
  rw [staysThrough_eq_compl, probReal_compl_eq_one_sub
    ((measurableSet_successPrefixEvent _ T).preimage (Preorder.measurable_frestrictLe T)),
    realized_prefix_hitting]

theorem firstExitBy_actual (K : RationalMarkovMatrix n) (B : Finset (Fin n)) (d : Fin n)
    (x : Fin n) (T : ℕ) :
    ((realizedModel K).pathLaw (Measure.dirac (decode x))).real (firstExitBy B d T) =
      (rationalHittingValue K (routeTarget B d) T x : ℝ) := by
  rw [firstExitBy_eq_prefix B d T, realized_prefix_hitting]

/-- Eventual first exit at `d` under `K` is eventual hitting of `d` under the
    exit-stopped chain: both are monotone limits of equal finite-horizon values. -/
theorem firstExitAt_eq_stopped_everAt (K : RationalMarkovMatrix n) (B : Finset (Fin n))
    (d : Fin n) (hd : d ∉ B) (x : Fin n) :
    ((realizedModel K).pathLaw (Measure.dirac (decode x))) (firstExitAt B d) =
      ((realizedModel (stopOutside K B)).pathLaw (Measure.dirac (decode x))) (everAt d) := by
  let P := (realizedModel K).pathLaw (Measure.dirac (decode x))
  let Q := (realizedModel (stopOutside K B)).pathLaw (Measure.dirac (decode x))
  have hP : Tendsto (fun T => P (firstExitBy B d T)) atTop (𝓝 (P (firstExitAt B d))) := by
    rw [firstExitAt_eq_iUnion]
    exact tendsto_measure_iUnion_atTop (firstExitBy_monotone B d)
  have hQ : Tendsto (fun T => Q ((Preorder.frestrictLe T) ⁻¹'
      successPrefixEvent (typedTarget (hitTarget d)) T)) atTop (𝓝 (Q (everAt d))) := by
    rw [everAt_eq_iUnion]
    exact tendsto_measure_iUnion_atTop (hit_prefix_monotone d)
  have hEq : ∀ T, P (firstExitBy B d T) = Q ((Preorder.frestrictLe T) ⁻¹'
      successPrefixEvent (typedTarget (hitTarget d)) T) := by
    intro T
    have h1 := firstExitBy_actual K B d x T
    have h2 := realized_prefix_hitting (stopOutside K B) (hitTarget d) x T
    rw [stopped_hit_eq_route K B d hd T x] at h2
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
      (h1.trans h2.symm)
  simp only [hEq] at hP
  exact tendsto_nhds_unique hP hQ

/-! ## Receipt checks -/

/-- Survival table, cumulative first-exit table, Dirichlet certificate of the
    stopped chain, eventual routing and never-exit mass, for starts in `B`. -/
def ExitChecks (K : RationalMarkovMatrix n) (B : Finset (Fin n)) (horizon : ℕ)
    (survival : ℕ → Fin n → ℚ) (steps : ℕ → Fin n → Fin n → ℚ)
    (cert : DirichletCertificate n) (eventual : Fin n → Fin n → ℚ) (never : Fin n → ℚ) :
    Prop :=
  (∀ t : Fin (horizon + 1), ∀ x ∈ B,
    survival t.val x = 1 - rationalHittingValue K (exitTarget B) t.val x) ∧
  (∀ t : Fin (horizon + 1), ∀ x ∈ B, ∀ d ∈ Bᶜ,
    (∑ s ∈ Finset.range t.val, steps s x d) = rationalHittingValue K (routeTarget B d) t.val x) ∧
  checkDirichlet (stopOutside K B) cert = true ∧
  (∀ x ∈ B, ∀ d ∈ Bᶜ, {d} ∈ cert.classes ∧ eventual x d = cert.weight {d} x) ∧
  (∀ x ∈ B, never x = 1 - ∑ d ∈ Bᶜ, eventual x d)

instance (K : RationalMarkovMatrix n) (B : Finset (Fin n)) (horizon : ℕ)
    (survival : ℕ → Fin n → ℚ) (steps : ℕ → Fin n → Fin n → ℚ)
    (cert : DirichletCertificate n) (eventual : Fin n → Fin n → ℚ) (never : Fin n → ℚ) :
    Decidable (ExitChecks K B horizon survival steps cert eventual never) := by
  unfold ExitChecks
  infer_instance

/-- A false result means some table entry, routing value or certificate is wrong. -/
def checkExitRoutingReceipt (K : RationalMarkovMatrix n) (B : Finset (Fin n)) (horizon : ℕ)
    (survival : ℕ → Fin n → ℚ) (steps : ℕ → Fin n → Fin n → ℚ)
    (cert : DirichletCertificate n) (eventual : Fin n → Fin n → ℚ) (never : Fin n → ℚ) : Bool :=
  decide (ExitChecks K B horizon survival steps cert eventual never)

theorem checkExitRoutingReceipt_sound (K : RationalMarkovMatrix n) (B : Finset (Fin n))
    (horizon : ℕ) (survival : ℕ → Fin n → ℚ) (steps : ℕ → Fin n → Fin n → ℚ)
    (cert : DirichletCertificate n) (eventual : Fin n → Fin n → ℚ) (never : Fin n → ℚ)
    (h : checkExitRoutingReceipt K B horizon survival steps cert eventual never = true) :
    ExitChecks K B horizon survival steps cert eventual never := by
  unfold checkExitRoutingReceipt at h
  exact of_decide_eq_true h

section Receipt

variable (K : RationalMarkovMatrix n) (B : Finset (Fin n)) (horizon : ℕ)
  (survival : ℕ → Fin n → ℚ) (steps : ℕ → Fin n → Fin n → ℚ)
  (cert : DirichletCertificate n) (eventual : Fin n → Fin n → ℚ) (never : Fin n → ℚ)
  (h : checkExitRoutingReceipt K B horizon survival steps cert eventual never = true)
include h

/-- Every checked survival entry is the actual probability of staying in `B`
    at observation times `0..t`. -/
theorem checked_survival_actual (t : ℕ) (ht : t ≤ horizon) (x : Fin n) (hx : x ∈ B) :
    (survival t x : ℝ) =
      ((realizedModel K).pathLaw (Measure.dirac (decode x))).real (staysThrough B t) := by
  have hrow := (checkExitRoutingReceipt_sound K B horizon survival steps cert eventual never h).1
    ⟨t, Nat.lt_succ_of_le ht⟩ x hx
  rw [survival_actual, hrow]
  push_cast
  ring

/-- The checked per-step first-exit entries sum to the actual probability
    that the first state outside `B` is `d`, reached within `t` steps. -/
theorem checked_exit_by_actual (t : ℕ) (ht : t ≤ horizon) (x : Fin n) (hx : x ∈ B)
    (d : Fin n) (hd : d ∉ B) :
    ((∑ s ∈ Finset.range t, steps s x d : ℚ) : ℝ) =
      ((realizedModel K).pathLaw (Measure.dirac (decode x))).real (firstExitBy B d t) := by
  have hrow := (checkExitRoutingReceipt_sound K B horizon survival steps cert eventual never
    h).2.1 ⟨t, Nat.lt_succ_of_le ht⟩ x hx d (Finset.mem_compl.mpr hd)
  rw [firstExitBy_actual K B d x t, ← hrow]

/-- Every checked eventual routing value is the actual probability that the
    first state outside `B` is `d`. Not normalized. -/
theorem checked_eventual_exit_actual [NeZero n] (x : Fin n) (hx : x ∈ B) (d : Fin n)
    (hd : d ∉ B) :
    (eventual x d : ℝ) =
      ((realizedModel K).pathLaw (Measure.dirac (decode x))).real (firstExitAt B d) := by
  obtain ⟨-, -, hc, hev, -⟩ :=
    checkExitRoutingReceipt_sound K B horizon survival steps cert eventual never h
  obtain ⟨hmem, hval⟩ := hev x hx d (Finset.mem_compl.mpr hd)
  have hb : {d} ∈ bottomClasses (stopOutside K B) := (checkDirichlet_sound _ cert hc).1 ▸ hmem
  have hweight := checked_class_column_unique (stopOutside K B) cert
    (referenceDirichletCertificate (stopOutside K B)) hc
    (referenceDirichlet_check_true (stopOutside K B)) {d} hb x
  have hcramer := cramerWeight_eq_typedStoppedClass_probability (stopOutside K B) {d} hb x
  have hever := typedStopped_mass_eq_everHit (stopOutside K B) {d} hb x
  have hset : {w : ℕ → JointState Unit (Fin n) | ∃ t : ℕ, encode (w t) ∈ ({d} : Finset (Fin n))} =
      everAt d := by
    ext w
    simp [everAt]
  rw [hset] at hever
  unfold Measure.real
  rw [firstExitAt_eq_stopped_everAt K B d hd x, ← hever, hval, hweight]
  exact hcramer.symm

/-- The checked never-exit mass is the actual probability of never leaving `B`. -/
theorem checked_never_exit_actual [NeZero n] (x : Fin n) (hx : x ∈ B) :
    (never x : ℝ) =
      ((realizedModel K).pathLaw (Measure.dirac (decode x))).real (staysForever B) := by
  have hnever := (checkExitRoutingReceipt_sound K B horizon survival steps cert eventual never
    h).2.2.2.2 x hx
  have hmeas : ∀ d ∈ Bᶜ, MeasurableSet (firstExitAt B d) :=
    fun d _ => measurable_firstExitAt B d
  rw [staysForever_eq_compl, probReal_compl_eq_one_sub (Finset.measurableSet_biUnion _ hmeas),
    measureReal_biUnion_finset (firstExitAt_pairwise_disjoint B) hmeas, hnever]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  exact checked_eventual_exit_actual K B horizon survival steps cert eventual never h x hx d
    (Finset.mem_compl.mp hd)

end Receipt

end PermanssonResearch.ApplicationBridge.ExitReceipt
