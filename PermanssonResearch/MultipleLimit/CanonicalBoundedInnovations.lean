import PermanssonResearch.Probability.BoundedInnovations
import PermanssonResearch.MultipleLimit.FiniteCanonicalPath
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Process.Filtration

/-! Bounded measurable tests of the actual infinite canonical Markov law.
The complete-past conditional mean comes from the genuine Ionescu--Tulcea
conditional distribution. The state space need not be finite. -/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal

namespace PermanssonResearch.MultipleLimit.CanonicalBoundedInnovations

set_option autoImplicit false
noncomputable section

open FiniteCanonicalPath
open PermanssonResearch.Probability.BoundedInnovations

variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

def past : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Y)) :=
  Filtration.piLE (X := fun _ : ℕ => Y)

theorem coordinate_measurable (s t : ℕ) (hst : s ≤ t) :
    Measurable[past (Y := Y) t] (fun w : ℕ → Y => w s) := by
  change Measurable[Filtration.piLE (X := fun _ : ℕ => Y) t] _
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have he : (fun w : ℕ → Y => w s) =
      (fun h : ((i : Finset.Iic t) → Y) => h ⟨s,Finset.mem_Iic.mpr hst⟩) ∘
        Preorder.frestrictLe t := by funext w; rfl
  rw [he]
  exact (measurable_pi_apply (⟨s,Finset.mem_Iic.mpr hst⟩ : Finset.Iic t)).comp (comap_measurable _)

def predict (f : Y → ℝ) (y : Y) : ℝ := ∫ z, f z ∂K y

theorem predict_measurable (f : Y → ℝ) (hf : Measurable f) : Measurable (predict K f) :=
  hf.stronglyMeasurable.integral_kernel.measurable

theorem predict_bound (f : Y → ℝ) (B : ℝ) (hb : ∀ y, |f y| ≤ B) (y : Y) :
    |predict K f y| ≤ B := by
  have h := norm_integral_le_of_norm_le_const (μ := K y) (f := f) (C := B)
    (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hb z))
  simpa [predict,Real.norm_eq_abs] using h

/-- The next-test conditional mean under the entire natural past, with
the actual original transition kernel and arbitrary initial probability. -/
theorem next_conditional (μ : ProbabilityMeasure Y) (f : Y → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ y, |f y| ≤ B) (t : ℕ) :
    (canonicalPathLaw K μ.toMeasure)[(fun w : ℕ → Y => f (w (t+1))) | past (Y := Y) t]
      =ᵐ[canonicalPathLaw K μ.toMeasure] (fun w => predict K f (w t)) := by
  let P := canonicalPathLaw K μ.toMeasure
  have hi : Integrable (fun w : ℕ → Y => f (w (t+1))) P := by
    apply Integrable.of_bound (hf.comp (measurable_pi_apply (t+1))).aestronglyMeasurable B
    exact ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs,Function.comp_apply] using hb (w (t+1)))
  have hc := condExp_ae_eq_integral_condDistrib
    (μ := P) (X := Preorder.frestrictLe t) (Y := fun w : ℕ → Y => w (t+1))
    (Preorder.measurable_frestrictLe (X := fun _ : ℕ => Y) t)
    (measurable_pi_apply (t+1)).aemeasurable hf.stronglyMeasurable hi
  have hk := Kernel.condDistrib_trajMeasure
    (X := fun _ : ℕ => Y)
    (μ₀ := μ.toMeasure)
    (κ := fun n => PermanssonLean.ProbabilitySupport.stationaryPrefixKernel K n) (a := t)
  have hkp : ∀ᵐ w ∂P,
      condDistrib (fun w : ℕ → Y => w (t+1)) (Preorder.frestrictLe t) P
        (Preorder.frestrictLe t w) =
      PermanssonLean.ProbabilitySupport.stationaryPrefixKernel K t (Preorder.frestrictLe t w) :=
    ae_of_ae_map (Preorder.measurable_frestrictLe (X := fun _ : ℕ => Y) t).aemeasurable hk
  change P[(fun w : ℕ → Y => f (w (t+1))) | past (Y := Y) t] =ᵐ[P] _
  have hpast : past (Y := Y) t = MeasurableSpace.comap (Preorder.frestrictLe t) inferInstance :=
    Filtration.piLE_eq_comap_frestrictLe t
  rw [hpast]
  filter_upwards [hc,hkp] with w hw hk'
  rw [hw,hk']
  rfl

def innovation (f : Y → ℝ) (t : ℕ) (w : ℕ → Y) : ℝ := f (w (t+1)) - predict K f (w t)

theorem innovation_measurable (f : Y → ℝ) (hf : Measurable f) (t : ℕ) :
    Measurable[past (Y := Y) (t+1)] (innovation K f t) :=
  (hf.comp (coordinate_measurable (t+1) (t+1) le_rfl)).sub
    ((predict_measurable K f hf).comp (coordinate_measurable t (t+1) (Nat.le_succ t)))

theorem innovation_bound (f : Y → ℝ) (B : ℝ) (hb : ∀ y, |f y| ≤ B) (t : ℕ) (w : ℕ → Y) :
    |innovation K f t w| ≤ 2*B := by
  exact (abs_sub _ _).trans ((add_le_add (hb _) (predict_bound K f B hb _)).trans_eq (by ring))

theorem innovation_centered (μ : ProbabilityMeasure Y) (f : Y → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ y, |f y| ≤ B) (t : ℕ) :
    (canonicalPathLaw K μ.toMeasure)[innovation K f t | past (Y := Y) t]
      =ᵐ[canonicalPathLaw K μ.toMeasure] (fun _ => (0 : ℝ)) := by
  let P := canonicalPathLaw K μ.toMeasure
  let ℱ := past (Y := Y)
  have hnexti : Integrable (fun w : ℕ → Y => f (w (t+1))) P := by
    apply Integrable.of_bound (hf.comp (measurable_pi_apply (t+1))).aestronglyMeasurable B
    exact ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs,Function.comp_apply] using hb _)
  have hpredi : Integrable (fun w : ℕ → Y => predict K f (w t)) P := by
    apply Integrable.of_bound
      ((predict_measurable K f hf).comp (measurable_pi_apply t)).aestronglyMeasurable B
    exact ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs,Function.comp_apply] using predict_bound K f B hb _)
  have hpred : StronglyMeasurable[ℱ t] (fun w : ℕ → Y => predict K f (w t)) :=
    ((predict_measurable K f hf).comp (coordinate_measurable t t le_rfl)).stronglyMeasurable
  have hce := condExp_of_stronglyMeasurable (ℱ.le t) hpred hpredi
  have hs := condExp_sub hnexti hpredi (ℱ t)
  have hs' : P[(fun w : ℕ → Y => f (w (t+1))-predict K f (w t)) | ℱ t] =ᵐ[P]
      (fun w => (P[(fun w : ℕ → Y => f (w (t+1))) | ℱ t]) w -
        (P[(fun w : ℕ → Y => predict K f (w t)) | ℱ t]) w) := by
    convert hs using 1 <;> rfl
  have hn := next_conditional K μ f hf B hb t
  change P[(fun w : ℕ → Y => f (w (t+1))-predict K f (w t)) | ℱ t] =ᵐ[P] _
  filter_upwards [hs',hn] with w hw hnext
  change (P[(fun w : ℕ → Y => f (w (t+1))-predict K f (w t)) | ℱ t]) w = 0
  rw [hw]
  change (P[(fun w : ℕ → Y => f (w (t+1))) | ℱ t]) w -
    (P[(fun w : ℕ → Y => predict K f (w t)) | ℱ t]) w = 0
  rw [hce,hnext,sub_self]

def normalization (B : ℝ) : ℝ := 2*(B+1)

def boundedProcess (μ : ProbabilityMeasure Y) (f : Y → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ y, |f y| ≤ B) :
    Process (canonicalPathLaw K μ.toMeasure) (past (Y := Y)) where
  value t := (normalization B)⁻¹ • innovation K f t
  measurable_next t := (innovation_measurable K f hf t).const_smul _
  bounded t w := by
    have hpos : 0 < normalization B := by dsimp [normalization]; positivity
    simp only [Pi.smul_apply,smul_eq_mul,abs_mul,abs_of_pos (inv_pos.mpr hpos)]
    have hb' := innovation_bound K f B hb t w
    have hc : 2*B ≤ normalization B := by dsimp [normalization]; linarith
    calc
      (normalization B)⁻¹ * |innovation K f t w| ≤ (normalization B)⁻¹ * normalization B :=
        mul_le_mul_of_nonneg_left (hb'.trans hc) (inv_nonneg.mpr hpos.le)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
  centered t := by
    have hs := condExp_smul (μ := canonicalPathLaw K μ.toMeasure) (normalization B)⁻¹
      (innovation K f t) (past (Y := Y) t)
    filter_upwards [hs,innovation_centered K μ f hf B hb t] with w hw hz
    change ((canonicalPathLaw K μ.toMeasure)[(normalization B)⁻¹ • innovation K f t |
      past (Y := Y) t]) w = 0
    rw [hw]
    change (normalization B)⁻¹ *
      ((canonicalPathLaw K μ.toMeasure)[innovation K f t | past (Y := Y) t]) w = 0
    rw [hz,mul_zero]

/-- Actual all-initial-law strong law for any bounded measurable Markov
test, without finite-state, recurrence, stationarity or aperiodicity inputs. -/
theorem canonical_innovation_strong_law (μ : ProbabilityMeasure Y) (f : Y → ℝ)
    (hf : Measurable f) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ y, |f y| ≤ B) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n => (∑ t ∈ Finset.range (n+1), innovation K f t w) /
        ((n+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  let p := boundedProcess K μ f hf B hB hb
  have hc : normalization B ≠ 0 := ne_of_gt (by dsimp [normalization]; positivity)
  filter_upwards [p.ae_strong_law] with w hw
  have hs : Tendsto (fun n => normalization B * (p.total (n+1) w / ((n+1 : ℕ) : ℝ)))
      atTop (𝓝 (normalization B*0)) := tendsto_const_nhds.mul hw
  have he (n : ℕ) : normalization B * (p.total (n+1) w / ((n+1 : ℕ) : ℝ)) =
      (∑ t ∈ Finset.range (n+1), innovation K f t w) / ((n+1 : ℕ) : ℝ) := by
    simp only [Process.total,p,boundedProcess,Pi.smul_apply,smul_eq_mul,← Finset.mul_sum]
    field_simp [hc]
  simpa only [he,mul_zero] using hs

end
end PermanssonResearch.MultipleLimit.CanonicalBoundedInnovations
