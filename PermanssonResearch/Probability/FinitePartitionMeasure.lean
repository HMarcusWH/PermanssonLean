import PermanssonResearch.StrategicWorld.ActionTrace
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.AEMeasurable

/-! The actual normalized restricted-cell lift of a finite transport plan.
Zero-mass cells use a Dirac fallback; the row/column equations force their
transport weights to vanish. No normalization or marginal identity is assumed. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch.Probability.FinitePartition
open ActionTrace

noncomputable section
variable {Y I : Type*} [MeasurableSpace Y] [Fintype I] [DecidableEq I]
  [MeasurableSpace I] [MeasurableSingletonClass I]

def cell (t : Y → I) (i : I) : Set Y := t ⁻¹' {i}

theorem cell_measurable {t : Y → I} (ht : Measurable t) (i : I) :
    MeasurableSet (cell t i) := ht (measurableSet_singleton i)

def normalizedCell (μ : Measure Y) (y0 : Y) (t : Y → I) (i : I) : Measure Y := by
  classical
  exact if μ (cell t i)=0 then Measure.dirac y0 else ProbabilityTheory.cond μ (cell t i)

instance normalizedCell_probability (μ : Measure Y) [IsProbabilityMeasure μ]
    (y0 : Y) (t : Y → I) (i : I) : IsProbabilityMeasure (normalizedCell μ y0 t i) := by
  classical
  unfold normalizedCell
  split_ifs with hi
  · infer_instance
  · exact cond_isProbabilityMeasure hi

theorem cell_mass_smul (μ : Measure Y) [IsProbabilityMeasure μ]
    (y0 : Y) (t : Y → I) (i : I) :
    μ (cell t i) • normalizedCell μ y0 t i=μ.restrict (cell t i) := by
  classical
  by_cases hi : μ (cell t i)=0
  · simp [normalizedCell,hi,Measure.restrict_eq_zero.mpr hi]
  · simp only [normalizedCell,if_neg hi,ProbabilityTheory.cond,smul_smul]
    rw [ENNReal.mul_inv_cancel hi (measure_ne_top μ _),one_smul]

theorem sum_cell_restrict (μ : Measure Y) (t : Y → I) (ht : Measurable t) :
    (∑ i : I, μ.restrict (cell t i))=μ := by
  have hd : Pairwise (Function.onFun Disjoint (cell t)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro y hyi hyj
    exact hij (hyi.symm.trans hyj)
  have hu : (⋃ i : I, cell t i)=Set.univ := by
    ext y
    simp [cell]
  simpa only [hu,Measure.restrict_univ,Measure.sum_fintype] using
    (Measure.restrict_iUnion hd (cell_measurable ht)).symm

def liftLaw (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (y0 : Y) (t : Y → I) (g : Row (I × I)) : Measure (Y × Y) :=
  ∑ ij : I × I, ENNReal.ofReal (g.mass ij) •
    (normalizedCell μ y0 t ij.1).prod (normalizedCell ν y0 t ij.2)

instance liftLaw_probability (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (y0 : Y) (t : Y → I) (g : Row (I × I)) : IsProbabilityMeasure (liftLaw μ ν y0 t g) := by
  refine ⟨?_⟩
  simp only [liftLaw,Measure.finsetSum_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun ij _ => g.nonneg ij),g.total]
  simp

theorem liftLaw_first (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (y0 : Y) (t : Y → I) (ht : Measurable t) (g : Row (I × I))
    (hrow : ∀ i, ∑ j, g.mass (i,j)=μ.real (cell t i)) :
    (liftLaw μ ν y0 t g).map Prod.fst=μ := by
  rw [liftLaw,Measure.map_finset_sum' measurable_fst.aemeasurable]
  simp_rw [Measure.map_smul _ measurable_fst.aemeasurable,Measure.map_fst_prod,
    measure_univ,one_smul]
  rw [Fintype.sum_prod_type]
  calc
    (∑ i : I, ∑ j : I, ENNReal.ofReal (g.mass (i,j)) • normalizedCell μ y0 t i)=
        ∑ i : I, μ.restrict (cell t i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_smul,← ENNReal.ofReal_sum_of_nonneg (fun j _ => g.nonneg (i,j)),hrow]
      rw [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top μ _),cell_mass_smul]
    _ = μ := sum_cell_restrict μ t ht

theorem liftLaw_second (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (y0 : Y) (t : Y → I) (ht : Measurable t) (g : Row (I × I))
    (hcol : ∀ j, ∑ i, g.mass (i,j)=ν.real (cell t j)) :
    (liftLaw μ ν y0 t g).map Prod.snd=ν := by
  rw [liftLaw,Measure.map_finset_sum' measurable_snd.aemeasurable]
  simp_rw [Measure.map_smul _ measurable_snd.aemeasurable,Measure.map_snd_prod,
    measure_univ,one_smul]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  calc
    (∑ j : I, ∑ i : I, ENNReal.ofReal (g.mass (i,j)) • normalizedCell ν y0 t j)=
        ∑ j : I, ν.restrict (cell t j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_smul,← ENNReal.ofReal_sum_of_nonneg (fun i _ => g.nonneg (i,j)),hcol]
      rw [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top ν _),cell_mass_smul]
    _ = ν := sum_cell_restrict ν t ht

theorem weight_zero_of_left_cell_zero (μ : Measure Y) (t : Y → I) (g : Row (I × I))
    (hrow : ∀ i, ∑ j, g.mass (i,j)=μ.real (cell t i)) (i j : I) (hi : μ (cell t i)=0) :
    g.mass (i,j)=0 := by
  apply le_antisymm _ (g.nonneg (i,j))
  calc
    g.mass (i,j)≤∑ k : I, g.mass (i,k) :=
      Finset.single_le_sum (fun k _ => g.nonneg (i,k)) (Finset.mem_univ j)
    _ = 0 := by rw [hrow,measureReal_def,hi]; simp

theorem weight_zero_of_right_cell_zero (ν : Measure Y) (t : Y → I) (g : Row (I × I))
    (hcol : ∀ j, ∑ i, g.mass (i,j)=ν.real (cell t j)) (i j : I) (hj : ν (cell t j)=0) :
    g.mass (i,j)=0 := by
  apply le_antisymm _ (g.nonneg (i,j))
  calc
    g.mass (i,j)≤∑ k : I, g.mass (k,j) :=
      Finset.single_le_sum (fun k _ => g.nonneg (k,j)) (Finset.mem_univ i)
    _ = 0 := by rw [hcol,measureReal_def,hj]; simp

theorem normalizedCell_ae (μ : Measure Y) [IsProbabilityMeasure μ]
    (y0 : Y) (t : Y → I) (ht : Measurable t) (i : I) (hi : μ (cell t i)≠0) :
    ∀ᵐ y ∂normalizedCell μ y0 t i, t y=i := by
  classical
  simp only [normalizedCell,if_neg hi,ProbabilityTheory.cond]
  apply Measure.ae_smul_measure
  exact ae_restrict_mem (cell_measurable ht i)

end
end PermanssonResearch.Probability.FinitePartition
