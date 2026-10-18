import PermanssonResearch.MultipleLimit.CanonicalKernelMarginals
import PermanssonResearch.Probability.CompProdPushforward
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Tactic

/-! The actual homogeneous canonical trajectory is shift invariant when its
declared initial probability is invariant. The proof identifies every finite
prefix by its initial marginal and complete-prefix transition identity. -/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultipleLimit.StationaryCanonical

set_option autoImplicit false
variable {Y : Type*} [MeasurableSpace Y]
open FiniteCanonicalPath
open PermanssonLean.ProbabilitySupport

def shift (w : ℕ → Y) : ℕ → Y := fun n => w (n+1)

theorem measurable_shift : Measurable (shift (Y := Y)) :=
  Measurable.of_eval fun n => measurable_pi_apply (n+1)

theorem shift_iterate_zero (n : ℕ) (w : ℕ → Y) : (shift^[n] w) 0 = w n := by
  have hall : ∀ n k, (shift^[n] w) k = w (k+n) := by
    intro n
    induction n with
    | zero => intro k; simp
    | succ n ih =>
      intro k
      rw [Function.iterate_succ_apply']
      change (shift^[n] w) (k+1) = w (k+(n+1))
      rw [ih]
      congr 1 <;> omega
  simpa using hall n 0

theorem canonical_prefix_zero (K : Kernel Y Y) [IsMarkovKernel K]
    (μ : Measure Y) [IsProbabilityMeasure μ] :
    (canonicalPathLaw K μ).map (Preorder.frestrictLe 0) =
      μ.map (MeasurableEquiv.piUnique (fun _ : Iic 0 => Y)).symm := by
  unfold canonicalPathLaw Kernel.trajMeasure
  rw [Measure.map_comp _ _ (by fun_prop), Kernel.traj_map_frestrictLe]
  simp

theorem canonical_eval_zero (K : Kernel Y Y) [IsMarkovKernel K]
    (μ : Measure Y) [IsProbabilityMeasure μ] :
    (canonicalPathLaw K μ).map (fun w : ℕ → Y => w 0) = μ := by
  let last : ((i : Iic 0) → Y) → Y := fun h => h ⟨0, mem_Iic.mpr le_rfl⟩
  have hm : Measurable last := measurable_pi_apply _
  calc
    _ = ((canonicalPathLaw K μ).map (Preorder.frestrictLe 0)).map last := by
      rw [Measure.map_map hm (Preorder.measurable_frestrictLe 0)]; rfl
    _ = (μ.map (MeasurableEquiv.piUnique (fun _ : Iic 0 => Y)).symm).map last := by
      rw [canonical_prefix_zero]
    _ = μ := by
      rw [Measure.map_map hm (MeasurableEquiv.measurable _)]
      convert (Measure.map_id : μ.map id = μ) using 1
      congr 1

def append (n : ℕ) (z : ((i : Iic n) → Y) × Y) : (i : Iic (n+1)) → Y :=
  fun i => if h : i.1 ≤ n then z.1 ⟨i.1, mem_Iic.mpr h⟩ else z.2

theorem measurable_append (n : ℕ) : Measurable (append (Y := Y) n) := by
  refine Measurable.of_eval fun i => ?_
  by_cases h : i.1 ≤ n
  · simp only [append, dif_pos h]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [append, dif_neg h]
    exact measurable_snd

theorem append_pair (n : ℕ) (w : ℕ → Y) :
    append n (Preorder.frestrictLe n w, w (n+1)) = Preorder.frestrictLe (n+1) w := by
  funext i
  by_cases h : i.1 ≤ n
  · simp [append, h]
  · have hi : i.1 = n+1 := by have := mem_Iic.mp i.2; omega
    simp [append, hi]

def HasTransitionPair (ν : Measure (ℕ → Y)) (K : Kernel Y Y) : Prop :=
  ∀ n, ν.map (Preorder.frestrictLe n) ⊗ₘ stationaryPrefixKernel K n =
    ν.map (fun w => (Preorder.frestrictLe n w, w (n+1)))

theorem prefix_maps_eq {μ ν : Measure (ℕ → Y)} (K : Kernel Y Y)
    (h0 : μ.map (Preorder.frestrictLe 0) = ν.map (Preorder.frestrictLe 0))
    (hμ : HasTransitionPair μ K) (hν : HasTransitionPair ν K) :
    ∀ n, μ.map (Preorder.frestrictLe n) = ν.map (Preorder.frestrictLe n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    have hp : μ.map (fun w => (Preorder.frestrictLe n w,w (n+1))) =
        ν.map (fun w => (Preorder.frestrictLe n w,w (n+1))) := by
      rw [← hμ n, ← hν n, ih]
    have hrec (ρ : Measure (ℕ → Y)) : ρ.map (Preorder.frestrictLe (n+1)) =
        (ρ.map (fun w => (Preorder.frestrictLe n w,w (n+1)))).map (append n) := by
      rw [Measure.map_map (measurable_append n) (by fun_prop)]
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun w => (append_pair n w).symm
    rw [hrec μ, hrec ν, hp]

theorem measure_eq_of_prefix_maps (μ ν : Measure (ℕ → Y))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ n, μ.map (Preorder.frestrictLe n) = ν.map (Preorder.frestrictLe n)) : μ = ν := by
  let fam : (I : Finset ℕ) → Measure ((i : I) → (fun _ : ℕ => Y) i) :=
    fun I => μ.map (fun w => I.restrict w)
  have hfam : IsProjectiveMeasureFamily (α := fun _ : ℕ => Y) fam := by
    dsimp [fam]
    exact ProbabilityTheory.isProjectiveMeasureFamily_map_restrict
      (fun t => (measurable_pi_apply t).aemeasurable)
  have hμ : IsProjectiveLimit (α := fun _ : ℕ => Y) μ fam := by intro I; rfl
  have hν : IsProjectiveLimit (α := fun _ : ℕ => Y) ν fam := by
    rw [MeasureTheory.isProjectiveLimit_nat_iff hfam]
    intro n
    exact (h n).symm
  haveI (I : Finset ℕ) : IsFiniteMeasure (fam I) := by dsimp [fam]; infer_instance
  exact hμ.unique hν

def dropPrefix (n : ℕ) (h : (i : Iic (n+1)) → Y) : (i : Iic n) → Y :=
  fun i => h ⟨i.1+1, mem_Iic.mpr (Nat.add_le_add_right (mem_Iic.mp i.2) 1)⟩

theorem measurable_dropPrefix (n : ℕ) : Measurable (dropPrefix (Y := Y) n) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

theorem shifted_transition (K : Kernel Y Y) [IsMarkovKernel K]
    (μ : Measure Y) [IsProbabilityMeasure μ] :
    HasTransitionPair ((canonicalPathLaw K μ).map shift) K := by
  intro n
  let P := canonicalPathLaw K μ
  let drop := dropPrefix (Y := Y) n
  have hd : Measurable drop := measurable_dropPrefix n
  have hprefix : (P.map shift).map (Preorder.frestrictLe n) =
      (P.map (Preorder.frestrictLe (n+1))).map drop := by
    rw [Measure.map_map (Preorder.measurable_frestrictLe n) measurable_shift,
      Measure.map_map hd (Preorder.measurable_frestrictLe (n+1))]
    rfl
  have hpair : (P.map shift).map (fun w => (Preorder.frestrictLe n w,w (n+1))) =
      (P.map (fun w => (Preorder.frestrictLe (n+1) w,w ((n+1)+1)))).map
        (Prod.map drop id) := by
    rw [Measure.map_map (by fun_prop) measurable_shift,
      Measure.map_map (hd.prodMap measurable_id) (by fun_prop)]
    rfl
  have hK : stationaryPrefixKernel K (n+1) =
      (stationaryPrefixKernel K n).comap drop hd := by
    ext h : 1
    rfl
  rw [hprefix,hpair,← CanonicalKernelMarginals.canonical_transition_pair K μ (n+1),hK]
  exact PermanssonResearch.Probability.compProd_map_left_eq_map_compProd_comap
    _ hd (stationaryPrefixKernel K n)

theorem shift_measurePreserving (K : Kernel Y Y) [IsMarkovKernel K]
    (π : ProbabilityMeasure Y) (hπ : K ∘ₘ π.toMeasure = π.toMeasure) :
    MeasurePreserving (shift (Y := Y))
      (canonicalPathLaw K π.toMeasure) (canonicalPathLaw K π.toMeasure) := by
  refine ⟨measurable_shift, ?_⟩
  let P := canonicalPathLaw K π.toMeasure
  have h0 : (P.map shift).map (fun w : ℕ → Y => w 0) = P.map (fun w => w 0) := by
    rw [Measure.map_map (measurable_pi_apply 0) measurable_shift]
    change P.map (fun w => w (0+1)) = _
    rw [CanonicalKernelMarginals.canonical_eval_succ,
      canonical_eval_zero, hπ]
  have hp0 : (P.map shift).map (Preorder.frestrictLe 0) =
      P.map (Preorder.frestrictLe 0) := by
    have hf : (Preorder.frestrictLe 0 : (ℕ → Y) → ((i : Iic 0) → Y)) =
        (MeasurableEquiv.piUnique (fun _ : Iic 0 => Y)).symm ∘ (fun w => w 0) := by
      funext w i
      have hi : i.1 = 0 := Nat.le_zero.mp (mem_Iic.mp i.2)
      simp [hi]
    have he := (MeasurableEquiv.piUnique (fun _ : Iic 0 => Y)).symm.measurable
    rw [hf,← Measure.map_map he (measurable_pi_apply 0),
      ← Measure.map_map he (measurable_pi_apply 0),h0]
  apply measure_eq_of_prefix_maps
  exact prefix_maps_eq K hp0 (shifted_transition K π.toMeasure)
    (CanonicalKernelMarginals.canonical_transition_pair K π.toMeasure)

end PermanssonResearch.MultipleLimit.StationaryCanonical
