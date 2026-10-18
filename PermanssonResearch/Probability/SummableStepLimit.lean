import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-! A constructed measurable limit of random variables with summable expected
step distances. Summability almost surely, the limit, first moment and tail
cost bounds are all derived. -/

open MeasureTheory Filter TopologicalSpace
open scoped Topology ENNReal NNReal
namespace PermanssonResearch.Probability.SummableStepLimit
set_option autoImplicit false

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

theorem lintegral_tsum_ne_top (F : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (F n))
    (hpos : ∀ n x, 0 ≤ F n x) (hi : ∀ n, Integrable (F n) P)
    (hs : Summable (fun n => ∫ x, F n x ∂P)) :
    (∫⁻ x, ∑' n, ENNReal.ofReal (F n x) ∂P) ≠ ∞ := by
  rw [lintegral_tsum (fun n => (hm n).ennreal_ofReal.aemeasurable)]
  have he (n : ℕ) : (∫⁻ x, ENNReal.ofReal (F n x) ∂P) =
      ENNReal.ofReal (∫ x, F n x ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal (hi n) (ae_of_all _ (hpos n))).symm
  simp_rw [he]
  exact hs.tsum_ofReal_ne_top

theorem ae_summable (F : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (F n))
    (hpos : ∀ n x, 0 ≤ F n x) (hi : ∀ n, Integrable (F n) P)
    (hs : Summable (fun n => ∫ x, F n x ∂P)) :
    ∀ᵐ x ∂P, Summable (fun n => F n x) := by
  have hae := ae_lt_top (Measurable.tsum (fun n => (hm n).ennreal_ofReal))
    (lintegral_tsum_ne_top P F hm hpos hi hs)
  filter_upwards [hae] with x hx
  let G : ℕ → ℝ≥0 := fun n => ⟨F n x,hpos n x⟩
  have he : (∑' n, ENNReal.ofReal (F n x)) = ∑' n, (G n : ℝ≥0∞) := by
    apply tsum_congr
    intro n
    change ENNReal.ofReal ((G n : ℝ≥0) : ℝ) = (G n : ℝ≥0∞)
    simp
  have hn : (∑' n, (G n : ℝ≥0∞)) ≠ ∞ := by rw [← he]; exact hx.ne
  exact NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 hn)

theorem tsum_integrable (F : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (F n))
    (hpos : ∀ n x, 0 ≤ F n x) (hi : ∀ n, Integrable (F n) P)
    (hs : Summable (fun n => ∫ x, F n x ∂P)) :
    Integrable (fun x => ∑' n, F n x) P := by
  refine ⟨(Measurable.tsum hm).aestronglyMeasurable,?_⟩
  change (∫⁻ x, ‖∑' n, F n x‖ₑ ∂P) < ∞
  have he : (fun x => ‖∑' n, F n x‖ₑ) =ᵐ[P]
      (fun x => ∑' n, ENNReal.ofReal (F n x)) := by
    filter_upwards [ae_summable P F hm hpos hi hs] with x hx
    rw [Real.enorm_eq_ofReal (tsum_nonneg (fun n => hpos n x)),
      ENNReal.ofReal_tsum_of_nonneg (fun n => hpos n x) hx]
  rw [lintegral_congr_ae he]
  exact (lintegral_tsum_ne_top P F hm hpos hi hs).lt_top

theorem integral_tsum (F : ℕ → Ω → ℝ) (hpos : ∀ n x, 0 ≤ F n x)
    (hi : ∀ n, Integrable (F n) P) (hs : Summable (fun n => ∫ x, F n x ∂P)) :
    (∫ x, ∑' n, F n x ∂P) = ∑' n, ∫ x, F n x ∂P := by
  apply (integral_tsum_of_summable_integral_norm hi ?_).symm
  have he : (fun n => ∫ x, ‖F n x‖ ∂P) = fun n => ∫ x, F n x ∂P := by
    funext n
    congr 1
    funext x
    exact Real.norm_of_nonneg (hpos n x)
  rwa [he]

variable {Y : Type*} [MetricSpace Y] [CompleteSpace Y] [MeasurableSpace Y]
variable [BorelSpace Y] [SeparableSpace Y] [Nonempty Y]
variable (X : ℕ → Ω → Y)

def step (n : ℕ) (x : Ω) : ℝ := dist (X n x) (X (n+1) x)

theorem step_measurable (hm : ∀ n, Measurable (X n)) (n : ℕ) :
    Measurable (step X n) := (hm n).dist (hm (n+1))

noncomputable def limit (x : Ω) : Y := limUnder atTop (fun n => X n x)

theorem limit_measurable (hm : ∀ n, Measurable (X n)) : Measurable (limit X) :=
  (StronglyMeasurable.limUnder (l := atTop) (fun n => (hm n).stronglyMeasurable)).measurable

theorem ae_summable_step (hm : ∀ n, Measurable (X n))
    (hi : ∀ n, Integrable (step X n) P)
    (hs : Summable (fun n => ∫ x, step X n x ∂P)) :
    ∀ᵐ x ∂P, Summable (fun n => dist (X n x) (X (n+1) x)) :=
  ae_summable P (step X) (step_measurable X hm) (fun _ _ => dist_nonneg) hi hs

theorem ae_tendsto (hm : ∀ n, Measurable (X n))
    (hi : ∀ n, Integrable (step X n) P)
    (hs : Summable (fun n => ∫ x, step X n x ∂P)) :
    ∀ᵐ x ∂P, Tendsto (fun n => X n x) atTop (𝓝 (limit X x)) := by
  filter_upwards [ae_summable_step P X hm hi hs] with x hx
  obtain ⟨y,hy⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hx)
  simpa [limit,hy.limUnder_eq] using hy

theorem ae_dist_tail (hm : ∀ n, Measurable (X n))
    (hi : ∀ n, Integrable (step X n) P)
    (hs : Summable (fun n => ∫ x, step X n x ∂P)) (n : ℕ) :
    ∀ᵐ x ∂P, dist (X n x) (limit X x) ≤ ∑' k, step X (n+k) x := by
  filter_upwards [ae_summable_step P X hm hi hs,ae_tendsto P X hm hi hs] with x hx ht
  exact dist_le_tsum_dist_of_tendsto hx ht n

theorem tail_integrable (hm : ∀ n, Measurable (X n))
    (hi : ∀ n, Integrable (step X n) P)
    (hs : Summable (fun n => ∫ x, step X n x ∂P)) (n : ℕ) :
    Integrable (fun x => ∑' k, step X (n+k) x) P := by
  apply tsum_integrable P (fun k => step X (n+k))
    (fun k => step_measurable X hm _) (fun _ _ => dist_nonneg) (fun k => hi _)
  exact hs.comp_injective (fun a b h => by omega)

theorem dist_limit_integrable (hm : ∀ n, Measurable (X n))
    (hi : ∀ n, Integrable (step X n) P)
    (hs : Summable (fun n => ∫ x, step X n x ∂P)) (n : ℕ) :
    Integrable (fun x => dist (X n x) (limit X x)) P := by
  apply (tail_integrable P X hm hi hs n).mono'
    ((hm n).dist (limit_measurable X hm)).aestronglyMeasurable
  filter_upwards [ae_dist_tail P X hm hi hs n] with x hx
  simpa [Real.norm_eq_abs,abs_of_nonneg dist_nonneg] using hx

theorem integral_dist_limit_le (hm : ∀ n, Measurable (X n))
    (hi : ∀ n, Integrable (step X n) P)
    (hs : Summable (fun n => ∫ x, step X n x ∂P)) (n : ℕ) :
    (∫ x, dist (X n x) (limit X x) ∂P) ≤ ∑' k, ∫ x, step X (n+k) x ∂P := by
  calc
    _ ≤ ∫ x, ∑' k, step X (n+k) x ∂P := integral_mono_ae
      (dist_limit_integrable P X hm hi hs n) (tail_integrable P X hm hi hs n)
      (ae_dist_tail P X hm hi hs n)
    _ = _ := integral_tsum P (fun k => step X (n+k)) (fun _ _ => dist_nonneg)
      (fun k => hi _) (hs.comp_injective (fun a b h => by omega))

theorem limit_firstMoment (hm : ∀ n, Measurable (X n))
    (hi : ∀ n, Integrable (step X n) P)
    (hs : Summable (fun n => ∫ x, step X n x ∂P)) (y₀ : Y)
    (h₀ : Integrable (fun x => dist (X 0 x) y₀) P) :
    Integrable (fun x => dist (limit X x) y₀) P := by
  apply (h₀.add (dist_limit_integrable P X hm hi hs 0)).mono'
    ((limit_measurable X hm).dist measurable_const).aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg dist_nonneg]
  change dist (limit X x) y₀ ≤ dist (X 0 x) y₀ + dist (X 0 x) (limit X x)
  calc
    _ ≤ dist (limit X x) (X 0 x) + dist (X 0 x) y₀ := dist_triangle _ _ _
    _ = _ := by rw [dist_comm (limit X x) (X 0 x)]; ring

end PermanssonResearch.Probability.SummableStepLimit
