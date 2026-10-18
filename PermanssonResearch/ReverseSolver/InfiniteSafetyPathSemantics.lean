import PermanssonResearch.ReverseSolver.InfiniteSafetyFiniteEvaluation
import Mathlib.MeasureTheory.Measure.Continuity

/-! Literal physical safety events under the genuine infinite behavioral law.
The full-history Markovization is used only to construct the law; these events
inspect the physical state at every chronological time. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch.ReverseSolver.InfiniteSafety

open ControlledKernel FiniteMonitor
open PermanssonResearch.MultipleLimit.FiniteCanonicalPath
open PermanssonResearch.MultipleLimit.CanonicalKernelMarginals

noncomputable section
variable {C : Type*} [DecidableEq C] [Fintype C] {n : ℕ}

theorem historyKernel_ae (sys : FiniteControlSystem C n) (σ : BehavioralPolicy sys)
    (h : HistoryState C n) (p : HistoryState C n → Prop)
    (hp : ∀ a : C × Fin n, p (append h a.1 a.2)) :
    ∀ᵐ h' ∂historyKernel sys σ h, p h' := by
  change ∀ᵐ h' ∂transitionMeasure sys σ h, p h'
  rw [transitionMeasure,ae_finsetSum_measure_iff]
  intro a _
  apply Measure.ae_smul_measure
  exact (ae_dirac_iff (.of_discrete)).mpr (hp a)

/-- A pointwise support relation of the history kernel holds simultaneously
at all successive times of its actual canonical infinite trajectory. -/
theorem pathLaw_ae_successive (sys : FiniteControlSystem C n) (σ : BehavioralPolicy sys)
    (y : Fin n) (R : HistoryState C n → HistoryState C n → Prop)
    (hR : ∀ h, ∀ᵐ h' ∂historyKernel sys σ h, R h h') :
    ∀ᵐ w ∂pathLaw sys σ y, ∀ t : ℕ, R (w t) (w (t+1)) := by
  rw [ae_all_iff]
  intro t
  let last : ((i : Finset.Iic t) → HistoryState C n) → HistoryState C n :=
    fun h => h ⟨t,Finset.mem_Iic.mpr le_rfl⟩
  let p : (((i : Finset.Iic t) → HistoryState C n) × HistoryState C n) → Prop :=
    fun a => R (last a.1) a.2
  have hp : MeasurableSet {a | p a} := (Set.to_countable _).measurableSet
  have ha : ∀ᵐ a ∂((pathLaw sys σ y).map (Preorder.frestrictLe t)) ⊗ₘ
      PermanssonLean.ProbabilitySupport.stationaryPrefixKernel (historyKernel sys σ) t,
      p a := by
    apply Measure.ae_compProd_of_ae_ae hp
    exact Filter.Eventually.of_forall (fun h => hR (last h))
  change ∀ᵐ a ∂((canonicalPathLaw (historyKernel sys σ) (Measure.dirac (initialHistory y))).map
    (Preorder.frestrictLe t)) ⊗ₘ
      PermanssonLean.ProbabilitySupport.stationaryPrefixKernel (historyKernel sys σ) t, p a at ha
  rw [canonical_transition_pair] at ha
  have hm : Measurable (fun w : ℕ → HistoryState C n =>
      (Preorder.frestrictLe t w,w (t+1))) := by fun_prop
  exact ae_of_ae_map hm.aemeasurable ha

theorem pathLaw_ae_initial (sys : FiniteControlSystem C n) (σ : BehavioralPolicy sys)
    (y : Fin n) : ∀ᵐ w ∂pathLaw sys σ y, w 0=initialHistory y := by
  have hi : ∀ᵐ h ∂Measure.dirac (initialHistory (C := C) y), h=initialHistory y := by simp
  rw [← canonical_eval_zero_dirac (historyKernel sys σ) (initialHistory y)] at hi
  exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable hi

theorem pathLaw_ae_append (sys : FiniteControlSystem C n) (σ : BehavioralPolicy sys)
    (y : Fin n) : ∀ᵐ w ∂pathLaw sys σ y, ∀ t : ℕ,
      ∃ a : C × Fin n, w (t+1)=append (w t) a.1 a.2 :=
  pathLaw_ae_successive sys σ y (fun h h' => ∃ a : C × Fin n, h'=append h a.1 a.2)
    (fun h => historyKernel_ae sys σ h _ (fun a => ⟨a,rfl⟩))

/-- The stored past is the realized chronological past: the controller's
time argument is exactly t and its initial physical state is exactly y. -/
theorem pathLaw_ae_chronological (sys : FiniteControlSystem C n) (σ : BehavioralPolicy sys)
    (y : Fin n) : ∀ᵐ w ∂pathLaw sys σ y, ∀ t : ℕ,
      (w t).initial=y ∧ (w t).word.length=t := by
  filter_upwards [pathLaw_ae_initial sys σ y,pathLaw_ae_append sys σ y] with w h0 hs
  intro t
  induction t with
  | zero => simp [h0,initialHistory]
  | succ t ih =>
      obtain ⟨a,ha⟩ := hs t
      rw [ha]
      simp [append,ih]

def safeThrough (G : Finset (Fin n)) (N : ℕ) : Set (ℕ → HistoryState C n) :=
  {w | ∀ t ≤ N, current (w t) ∈ G}

def safeForever (G : Finset (Fin n)) : Set (ℕ → HistoryState C n) :=
  {w | ∀ t, current (w t) ∈ G}

theorem safeThrough_measurable (G : Finset (Fin n)) (N : ℕ) :
    MeasurableSet (safeThrough (C := C) G N) := by
  unfold safeThrough
  simp only [Set.ofPred_forall]
  have hG : MeasurableSet {h : HistoryState C n | current h∈G} := .of_discrete
  exact MeasurableSet.iInter (fun (t : ℕ) => MeasurableSet.iInter
    (fun (_ : t≤N) => (show Measurable (fun w : ℕ → HistoryState C n => w t)
      from measurable_pi_apply t) hG))

theorem safeForever_measurable (G : Finset (Fin n)) :
    MeasurableSet (safeForever (C := C) G) := by
  unfold safeForever
  rw [Set.ofPred_forall]
  have hG : MeasurableSet {h : HistoryState C n | current h∈G} := .of_discrete
  exact MeasurableSet.iInter (fun (t : ℕ) =>
    (show Measurable (fun w : ℕ → HistoryState C n => w t) from measurable_pi_apply t) hG)

theorem safeThrough_antitone (G : Finset (Fin n)) :
    Antitone (safeThrough (C := C) G) := by
  intro a b hab w hw t ht
  exact hw t (ht.trans hab)

theorem safeForever_eq_iInter (G : Finset (Fin n)) :
    safeForever (C := C) G=⋂ N, safeThrough G N := by
  ext w
  simp only [safeForever,safeThrough,Set.mem_setOf_eq,Set.mem_iInter]
  constructor
  · exact fun hw N t _ => hw t
  · exact fun hw t => hw t t le_rfl

theorem pathLaw_ae_historySafe_iff (sys : FiniteControlSystem C n)
    (σ : BehavioralPolicy sys) (G : Finset (Fin n)) (y : Fin n) :
    ∀ᵐ w ∂pathLaw sys σ y, ∀ N, historySafe G (w N) ↔ w ∈ safeThrough G N := by
  have hstep := pathLaw_ae_successive sys σ y
    (fun h h' => historySafe G h' ↔ historySafe G h ∧ current h' ∈ G)
    (fun h => historyKernel_ae sys σ h _ (fun a => by simp))
  filter_upwards [pathLaw_ae_initial sys σ y,hstep] with w hw hs
  intro N
  induction N with
  | zero => simp [safeThrough,hw]
  | succ N ih =>
      rw [hs N,ih]
      change (∀ t≤N, current (w t)∈G) ∧ current (w (N+1))∈G ↔
        ∀ t≤N+1, current (w t)∈G
      constructor
      · rintro ⟨h,hN⟩ t ht
        rcases (Nat.le_succ_iff_eq_or_le.mp ht) with ht | ht
        · simpa [ht] using hN
        · exact h t ht
      · intro h
        exact ⟨fun t ht => h t (ht.trans (Nat.le_succ N)), h (N+1) le_rfl⟩

/-- The probability of literal physical safety through N is the evaluator
derived from the full behavioral law, via the actual infinite-law marginal. -/
theorem pathLaw_safeThrough (sys : FiniteControlSystem C n) (σ : BehavioralPolicy sys)
    (G : Finset (Fin n)) (y : Fin n) (N : ℕ) :
    pathLaw sys σ y (safeThrough G N)=
      ENNReal.ofReal (survival sys σ G N (initialHistory y)) := by
  have he : safeThrough G N =ᵐ[pathLaw sys σ y]
      {w | historySafe G (w N)} := by
    filter_upwards [pathLaw_ae_historySafe_iff sys σ G y] with w hw
    exact propext (hw N).symm
  rw [measure_congr he]
  have hm : MeasurableSet {h : HistoryState C n | historySafe G h} := .of_discrete
  change pathLaw sys σ y ((fun w => w N) ⁻¹' {h | historySafe G h})=_
  rw [← Measure.map_apply (measurable_pi_apply N) hm]
  change (canonicalPathLaw (historyKernel sys σ) (Measure.dirac (initialHistory y))).map
      (fun w => w N) {h | historySafe G h}=_
  rw [canonical_eval_eq_kernel_pow,kernel_pow_safe_eq_survival]

theorem pathLaw_safeForever_eq_iInf (sys : FiniteControlSystem C n)
    (σ : BehavioralPolicy sys) (G : Finset (Fin n)) (y : Fin n) :
    pathLaw sys σ y (safeForever G)=⨅N, pathLaw sys σ y (safeThrough G N) := by
  rw [safeForever_eq_iInter]
  exact (safeThrough_antitone G).measure_iInter
    (fun N => (safeThrough_measurable G N).nullMeasurableSet)
    ⟨0,measure_ne_top (pathLaw sys σ y) _⟩

end
end PermanssonResearch.ReverseSolver.InfiniteSafety
