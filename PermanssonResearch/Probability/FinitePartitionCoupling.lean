import PermanssonResearch.Probability.FinitePartitionMeasure
import PermanssonResearch.Probability.CouplingDualBound
import Mathlib.MeasureTheory.Integral.Prod

/-! A constructed integrable coupling with the finite center-transport cost
plus the two actual quantization errors. All normalization, marginals, and
integrability are derived; no transport-lift hypothesis is supplied. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch.Probability.FinitePartition
open ActionTrace

noncomputable section
variable {Y I : Type*} [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology Y] [Fintype I] [DecidableEq I]
  [MeasurableSpace I] [MeasurableSingletonClass I]

def error (t : Y → I) (c : I → Y) (y : Y) : ℝ := dist y (c (t y))

def centerCost (t : Y → I) (c : I → Y) (z : Y × Y) : ℝ := dist (c (t z.1)) (c (t z.2))

theorem error_measurable (t : Y → I) (ht : Measurable t) (c : I → Y) :
    Measurable (error t c) := measurable_id.dist ((measurable_of_finite c).comp ht)

theorem centerCost_measurable (t : Y → I) (ht : Measurable t) (c : I → Y) :
    Measurable (centerCost t c) :=
  ((measurable_of_finite c).comp (ht.comp measurable_fst)).dist
    ((measurable_of_finite c).comp (ht.comp measurable_snd))

theorem error_integrable (μ : Measure Y) [IsProbabilityMeasure μ] (y0 : Y)
    (hμ : Integrable (fun y => dist y y0) μ) (t : Y → I) (ht : Measurable t) (c : I → Y) :
    Integrable (error t c) μ := by
  let B := ∑ i : I, dist (c i) y0
  have hB (i : I) : dist (c i) y0≤B :=
    Finset.single_le_sum (fun j _ => dist_nonneg) (Finset.mem_univ i)
  apply (hμ.add (integrable_const B)).mono' (error_measurable t ht c).aestronglyMeasurable
  apply ae_of_all
  intro y
  change ‖dist y (c (t y))‖≤dist y y0+B
  rw [Real.norm_eq_abs,abs_of_nonneg dist_nonneg]
  have hh := dist_triangle y y0 (c (t y))
  rw [dist_comm y0] at hh
  exact hh.trans (add_le_add le_rfl (hB (t y)))

theorem centerCost_integrable (θ : Measure (Y × Y)) [IsFiniteMeasure θ]
    (t : Y → I) (ht : Measurable t) (c : I → Y) : Integrable (centerCost t c) θ := by
  apply Integrable.of_bound (centerCost_measurable t ht c).aestronglyMeasurable
    (∑ ij : I × I, dist (c ij.1) (c ij.2))
  apply ae_of_all
  intro z
  change ‖dist (c (t z.1)) (c (t z.2))‖≤∑ ij : I × I, dist (c ij.1) (c ij.2)
  rw [Real.norm_eq_abs,abs_of_nonneg dist_nonneg]
  exact Finset.single_le_sum
    (fun (ij : I × I) _ => (show 0≤dist (c ij.1) (c ij.2) from dist_nonneg))
    (Finset.mem_univ (t z.1,t z.2))

theorem distance_integrable_of_marginals (μ ν : Measure Y) (θ : Measure (Y × Y))
    (hf : θ.map Prod.fst=μ) (hs : θ.map Prod.snd=ν) (y0 : Y)
    (hμ : Integrable (fun y => dist y y0) μ) (hν : Integrable (fun y => dist y y0) ν) :
    Integrable (fun z : Y × Y => dist z.1 z.2) θ := by
  have hfm : Integrable (fun y => dist y y0) (θ.map Prod.fst) := by rw [hf]; exact hμ
  have hsm : Integrable (fun y => dist y y0) (θ.map Prod.snd) := by rw [hs]; exact hν
  have hfi := hfm.comp_measurable measurable_fst
  have hsi := hsm.comp_measurable measurable_snd
  apply (hfi.add hsi).mono' (measurable_fst.dist measurable_snd).aestronglyMeasurable
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg dist_nonneg]
  change dist z.1 z.2≤dist z.1 y0+dist z.2 y0
  simpa only [dist_comm y0] using dist_triangle z.1 y0 z.2

def coupling (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (y0 : Y) (hμ : Integrable (fun y => dist y y0) μ) (hν : Integrable (fun y => dist y y0) ν)
    (t : Y → I) (ht : Measurable t) (g : Row (I × I))
    (hrow : ∀ i, ∑ j, g.mass (i,j)=μ.real (cell t i))
    (hcol : ∀ j, ∑ i, g.mass (i,j)=ν.real (cell t j)) : IntegrableCoupling μ ν where
  law := liftLaw μ ν y0 t g
  isProbability := inferInstance
  first := liftLaw_first μ ν y0 t ht g hrow
  second := liftLaw_second μ ν y0 t ht g hcol
  cost_integrable := distance_integrable_of_marginals μ ν (liftLaw μ ν y0 t g)
    (liftLaw_first μ ν y0 t ht g hrow) (liftLaw_second μ ν y0 t ht g hcol) y0 hμ hν

theorem liftLaw_centerCost (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (y0 : Y) (t : Y → I) (ht : Measurable t) (g : Row (I × I))
    (hrow : ∀ i, ∑ j, g.mass (i,j)=μ.real (cell t i))
    (hcol : ∀ j, ∑ i, g.mass (i,j)=ν.real (cell t j)) (c : I → Y) :
    (∫ z, centerCost t c z ∂liftLaw μ ν y0 t g)=g.expect (fun ij => dist (c ij.1) (c ij.2)) := by
  rw [liftLaw,integral_finsetSum_measure (fun ij _ =>
    (centerCost_integrable ((normalizedCell μ y0 t ij.1).prod
      (normalizedCell ν y0 t ij.2)) t ht c).smul_measure ENNReal.ofReal_ne_top)]
  simp_rw [integral_smul_measure,ENNReal.toReal_ofReal (g.nonneg _),smul_eq_mul]
  unfold Row.expect
  apply Finset.sum_congr rfl
  intro ij _
  by_cases hg : g.mass ij=0
  · simp [hg]
  · have hμi : μ (cell t ij.1)≠0 := by
      intro hi
      exact hg (weight_zero_of_left_cell_zero μ t g hrow ij.1 ij.2 hi)
    have hνj : ν (cell t ij.2)≠0 := by
      intro hj
      exact hg (weight_zero_of_right_cell_zero ν t g hcol ij.1 ij.2 hj)
    let θ := (normalizedCell μ y0 t ij.1).prod (normalizedCell ν y0 t ij.2)
    have hfst : ∀ᵐ z ∂θ, t z.1=ij.1 := by
      apply ae_of_ae_map (μ := θ) (f := Prod.fst) (p := fun x : Y => t x=ij.1)
        measurable_fst.aemeasurable
      have hm : θ.map Prod.fst=normalizedCell μ y0 t ij.1 := by simp [θ]
      rw [hm]
      exact normalizedCell_ae μ y0 t ht ij.1 hμi
    have hsnd : ∀ᵐ z ∂θ, t z.2=ij.2 := by
      apply ae_of_ae_map (μ := θ) (f := Prod.snd) (p := fun x : Y => t x=ij.2)
        measurable_snd.aemeasurable
      have hm : θ.map Prod.snd=normalizedCell ν y0 t ij.2 := by simp [θ]
      rw [hm]
      exact normalizedCell_ae ν y0 t ht ij.2 hνj
    have he : centerCost t c =ᵐ[θ] fun _ => dist (c ij.1) (c ij.2) := by
      filter_upwards [hfst,hsnd] with z hz1 hz2
      simp only [centerCost,hz1,hz2]
    change g.mass ij*(∫ z, centerCost t c z ∂θ)=_
    rw [integral_congr_ae he]
    simp

theorem cost_le_centerCost_and_errors (μ ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (γ : IntegrableCoupling μ ν)
    (t : Y → I) (ht : Measurable t) (c : I → Y)
    (hμ : Integrable (error t c) μ) (hν : Integrable (error t c) ν) :
    γ.cost≤(∫ z, centerCost t c z ∂γ.law)+(∫ y, error t c y ∂μ)+(∫ y, error t c y ∂ν) := by
  have hfm : Integrable (error t c) (γ.law.map Prod.fst) := by rw [γ.first]; exact hμ
  have hsm : Integrable (error t c) (γ.law.map Prod.snd) := by rw [γ.second]; exact hν
  have hfi : Integrable (fun z : Y × Y => error t c z.1) γ.law := hfm.comp_measurable measurable_fst
  have hsi : Integrable (fun z : Y × Y => error t c z.2) γ.law := hsm.comp_measurable measurable_snd
  have hci := centerCost_integrable γ.law t ht c
  have hsum : Integrable (fun z : Y × Y => error t c z.1+centerCost t c z) γ.law := hfi.add hci
  have hiμ : (∫ z : Y × Y, error t c z.1 ∂γ.law)=∫ y, error t c y ∂μ := by
    calc
      _ = ∫ y, error t c y ∂γ.law.map Prod.fst :=
        (integral_map measurable_fst.aemeasurable (error_measurable t ht c).aestronglyMeasurable).symm
      _ = _ := by rw [γ.first]
  have hiν : (∫ z : Y × Y, error t c z.2 ∂γ.law)=∫ y, error t c y ∂ν := by
    calc
      _ = ∫ y, error t c y ∂γ.law.map Prod.snd :=
        (integral_map measurable_snd.aemeasurable (error_measurable t ht c).aestronglyMeasurable).symm
      _ = _ := by rw [γ.second]
  calc
    γ.cost≤∫ z, error t c z.1+centerCost t c z+error t c z.2 ∂γ.law := by
      apply integral_mono γ.cost_integrable ((hfi.add hci).add hsi)
      intro z
      have h1 := dist_triangle z.1 (c (t z.1)) z.2
      have h2 := dist_triangle (c (t z.1)) (c (t z.2)) z.2
      rw [dist_comm (c (t z.2)) z.2] at h2
      dsimp [error,centerCost]
      linarith
    _ = (∫ z, centerCost t c z ∂γ.law)+(∫ y, error t c y ∂μ)+(∫ y, error t c y ∂ν) := by
      rw [integral_add hsum hsi,integral_add hfi hci,hiμ,hiν]
      ring

end
end PermanssonResearch.Probability.FinitePartition

namespace PermanssonResearch.Probability
open ActionTrace FinitePartition
noncomputable section
variable {Y I : Type*} [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology Y] [Fintype I] [DecidableEq I]
  [MeasurableSpace I] [MeasurableSingletonClass I]

/-- The actual finite-partition transport lift. Neither a coupling, its
marginals, its normalization, nor its cost integrability is an input. -/
theorem exists_finite_partition_coupling (μ ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (y0 : Y)
    (hμ : Integrable (fun y => dist y y0) μ) (hν : Integrable (fun y => dist y y0) ν)
    (t : Y → I) (ht : Measurable t) (g : Row (I × I))
    (hrow : ∀ i, ∑ j, g.mass (i,j)=μ.real (t ⁻¹' {i}))
    (hcol : ∀ j, ∑ i, g.mass (i,j)=ν.real (t ⁻¹' {j})) (c : I → Y) :
    ∃ γ : IntegrableCoupling μ ν,
      γ.cost≤g.expect (fun ij => dist (c ij.1) (c ij.2))+
        (∫ y, dist y (c (t y)) ∂μ)+(∫ y, dist y (c (t y)) ∂ν) := by
  let γ := coupling μ ν y0 hμ hν t ht g hrow hcol
  refine ⟨γ,?_⟩
  have hh := cost_le_centerCost_and_errors μ ν γ t ht c
    (error_integrable μ y0 hμ t ht c) (error_integrable ν y0 hν t ht c)
  change γ.cost≤(∫ z, centerCost t c z ∂liftLaw μ ν y0 t g)+
    (∫ y, error t c y ∂μ)+(∫ y, error t c y ∂ν) at hh
  rw [liftLaw_centerCost μ ν y0 t ht g hrow hcol c] at hh
  exact hh

end
end PermanssonResearch.Probability
