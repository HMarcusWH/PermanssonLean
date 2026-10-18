import Mathlib.Probability.Kernel.Disintegration.Unique

/-! Whole-measure equality is detected by one countable family on a standard
Borel target. In particular no uncountable union of exceptional null sets is
used to pass from evaluation equalities to equality of kernel rows. -/

namespace PermanssonResearch.Probability

open MeasureTheory ProbabilityTheory Set

noncomputable section

variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z] [StandardBorelSpace Z]

def determiningSet (q : ℚ) : Set Z := embeddingReal Z ⁻¹' Iic (q : ℝ)

theorem determiningSet_measurable (q : ℚ) : MeasurableSet (determiningSet (Z := Z) q) :=
  (measurableEmbedding_embeddingReal Z).measurable measurableSet_Iic

theorem probability_eq_iff_determining (μ ν : Measure Z)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    μ = ν ↔ ∀ q : ℚ, μ (determiningSet q) = ν (determiningSet q) := by
  constructor
  · rintro rfl q
    rfl
  · intro h
    have hf := measurableEmbedding_embeddingReal Z
    apply hf.map_injective
    apply ext_of_generate_finite (⋃ q : ℚ, {Iic (q : ℝ)})
      Real.borel_eq_generateFrom_Iic_rat Real.isPiSystem_Iic_rat
    · intro s hs
      simp only [iUnion_singleton_eq_range, mem_range] at hs
      obtain ⟨q, rfl⟩ := hs
      simpa only [determiningSet, Measure.map_apply hf.measurable measurableSet_Iic] using h q
    · simp

theorem measurableSet_kernel_equality (K L : Kernel Y Z)
    [IsMarkovKernel K] [IsMarkovKernel L] : MeasurableSet {y | K y = L y} := by
  have he : {y | K y = L y} = ⋂ q : ℚ,
      {y | K y (determiningSet q) = L y (determiningSet q)} := by
    ext y
    simpa only [mem_setOf_eq, mem_iInter] using probability_eq_iff_determining (K y) (L y)
  rw [he]
  apply MeasurableSet.iInter
  intro q
  exact measurableSet_eq_fun (K.measurable_coe (determiningSet_measurable q))
    (L.measurable_coe (determiningSet_measurable q))

theorem kernel_ae_eq_of_determining (K L : Kernel Y Z)
    [IsMarkovKernel K] [IsMarkovKernel L] (μ : Measure Y)
    (h : ∀ q : ℚ, ∀ᵐ y ∂μ, K y (determiningSet q) = L y (determiningSet q)) :
    K =ᵐ[μ] L := by
  filter_upwards [ae_all_iff.mpr h] with y hy
  exact (probability_eq_iff_determining (K y) (L y)).mpr hy

theorem kernel_ae_eq_of_measurable_evaluations (K L : Kernel Y Z)
    [IsMarkovKernel K] [IsMarkovKernel L] (μ : Measure Y)
    (h : ∀ s, MeasurableSet s → ∀ᵐ y ∂μ, K y s = L y s) : K =ᵐ[μ] L :=
  kernel_ae_eq_of_determining K L μ (fun q => h _ (determiningSet_measurable q))

end
end PermanssonResearch.Probability
