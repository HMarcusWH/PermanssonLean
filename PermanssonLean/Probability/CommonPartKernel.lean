import PermanssonLean.Probability.TotalVariation
import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.MeasureTheory.Measure.CompleteLattice

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonLean
namespace ProbabilitySupport

universe uY uΩ

variable {Y : Type uY} {Ω : Type uΩ}
variable [MeasurableSpace Y] [MeasurableSpace Ω]
variable [MeasurableSpace.CountableOrCountablyGenerated Y Ω]

/-- The Radon--Nikodym density of `K` relative to the common dominating kernel
`K + Ktilde`, in the real-valued auxiliary representation supplied by mathlib. -/
noncomputable def leftDensity
    (K Ktilde : Kernel Y Ω) (y : Y) (x : Ω) : ℝ :=
  Kernel.rnDerivAux K (K + Ktilde) y x

/-- Pointwise overlap density relative to `K + Ktilde`. -/
noncomputable def commonDensity
    (K Ktilde : Kernel Y Ω) (y : Y) (x : Ω) : ℝ≥0∞ :=
  min
    (ENNReal.ofReal (leftDensity K Ktilde y x))
    (ENNReal.ofReal (1 - leftDensity K Ktilde y x))

theorem measurable_commonDensity (K Ktilde : Kernel Y Ω) :
    Measurable (Function.uncurry (commonDensity K Ktilde)) := by
  unfold commonDensity leftDensity
  apply Measurable.min
  · exact (Kernel.measurable_rnDerivAux K (K + Ktilde)).ennreal_ofReal
  · exact (measurable_const.sub
      (Kernel.measurable_rnDerivAux K (K + Ktilde))).ennreal_ofReal

/-- A measurable finite kernel carrying exactly the pointwise density shared by
`K` and `Ktilde` relative to the common dominating kernel `K + Ktilde`. -/
noncomputable def commonPartKernel
    (K Ktilde : Kernel Y Ω) [IsFiniteKernel K] [IsFiniteKernel Ktilde] :
    Kernel Y Ω :=
  Kernel.withDensity (K + Ktilde) (commonDensity K Ktilde)

theorem commonPartKernel_apply
    (K Ktilde : Kernel Y Ω) [IsFiniteKernel K] [IsFiniteKernel Ktilde]
    (y : Y) :
    commonPartKernel K Ktilde y =
      ((K + Ktilde) y).withDensity (commonDensity K Ktilde y) := by
  rw [commonPartKernel, Kernel.withDensity_apply _ (measurable_commonDensity K Ktilde)]

/-- The overlap density is pointwise dominated by the left RN density. -/
theorem commonDensity_le_left
    (K Ktilde : Kernel Y Ω) (y : Y) (x : Ω) :
    commonDensity K Ktilde y x ≤
      ENNReal.ofReal (leftDensity K Ktilde y x) := by
  exact min_le_left _ _

/-- The overlap density is pointwise dominated by the complementary/right RN density. -/
theorem commonDensity_le_right
    (K Ktilde : Kernel Y Ω) (y : Y) (x : Ω) :
    commonDensity K Ktilde y x ≤
      ENNReal.ofReal (1 - leftDensity K Ktilde y x) := by
  exact min_le_right _ _

/-- The common-part kernel is a subkernel of `K`. -/
theorem commonPartKernel_le_left
    (K Ktilde : Kernel Y Ω) [IsFiniteKernel K] [IsFiniteKernel Ktilde] :
    commonPartKernel K Ktilde ≤ K := by
  rw [← Kernel.withDensity_rnDerivAux K Ktilde]
  intro y
  rw [commonPartKernel_apply]
  apply MeasureTheory.withDensity_mono
  exact ae_of_all _ (commonDensity_le_left K Ktilde y)

/-- The common-part kernel is a subkernel of `Ktilde`. -/
theorem commonPartKernel_le_right
    (K Ktilde : Kernel Y Ω) [IsFiniteKernel K] [IsFiniteKernel Ktilde] :
    commonPartKernel K Ktilde ≤ Ktilde := by
  rw [← Kernel.withDensity_one_sub_rnDerivAux K Ktilde]
  intro y
  rw [commonPartKernel_apply]
  apply MeasureTheory.withDensity_mono
  exact ae_of_all _ (commonDensity_le_right K Ktilde y)

/-- The common part is finite whenever both source kernels are finite. -/
instance commonPartKernel_isFinite
    (K Ktilde : Kernel Y Ω) [IsFiniteKernel K] [IsFiniteKernel Ktilde] :
    IsFiniteKernel (commonPartKernel K Ktilde) := by
  apply IsFiniteKernel.mono (commonPartKernel_le_left K Ktilde)
  infer_instance

/-- Measurable Hahn-style slice on which the left RN density is at least one half. -/
def dominanceSlice
    (K Ktilde : Kernel Y Ω) (y : Y) : Set Ω :=
  {x | (1 / 2 : ℝ) ≤ leftDensity K Ktilde y x}

theorem measurableSet_dominanceSlice
    (K Ktilde : Kernel Y Ω) (y : Y) :
    MeasurableSet (dominanceSlice K Ktilde y) := by
  unfold dominanceSlice leftDensity
  exact measurableSet_le measurable_const
    (Kernel.measurable_rnDerivAux_right K (K + Ktilde) y)

theorem commonDensity_eq_right_of_mem_dominanceSlice
    (K Ktilde : Kernel Y Ω) (y : Y) {x : Ω}
    (hx : x ∈ dominanceSlice K Ktilde y) :
    commonDensity K Ktilde y x =
      ENNReal.ofReal (1 - leftDensity K Ktilde y x) := by
  unfold dominanceSlice at hx
  unfold commonDensity
  rw [min_eq_right]
  apply ENNReal.ofReal_le_ofReal
  linarith

theorem commonDensity_eq_left_of_not_mem_dominanceSlice
    (K Ktilde : Kernel Y Ω) (y : Y) {x : Ω}
    (hx : x ∉ dominanceSlice K Ktilde y) :
    commonDensity K Ktilde y x =
      ENNReal.ofReal (leftDensity K Ktilde y x) := by
  unfold dominanceSlice at hx
  have hx' : leftDensity K Ktilde y x < (1 / 2 : ℝ) := by
    simpa using hx
  unfold commonDensity
  rw [min_eq_left]
  apply ENNReal.ofReal_le_ofReal
  linarith

/-- On the dominance slice the common part agrees with the right kernel. -/
theorem commonPartKernel_apply_dominanceSlice
    (K Ktilde : Kernel Y Ω) [IsFiniteKernel K] [IsFiniteKernel Ktilde]
    (y : Y) :
    commonPartKernel K Ktilde y (dominanceSlice K Ktilde y) =
      Ktilde y (dominanceSlice K Ktilde y) := by
  let A := dominanceSlice K Ktilde y
  have hA : MeasurableSet A := measurableSet_dominanceSlice K Ktilde y
  rw [commonPartKernel, Kernel.withDensity_apply'
      _ (measurable_commonDensity K Ktilde) y A]
  rw [← Kernel.withDensity_one_sub_rnDerivAux K Ktilde]
  rw [Kernel.withDensity_apply']
  · apply setLIntegral_congr_fun hA
    intro x hx
    exact commonDensity_eq_right_of_mem_dominanceSlice K Ktilde y hx
  · exact (measurable_const.sub
      (Kernel.measurable_rnDerivAux K (K + Ktilde))).ennreal_ofReal

/-- Off the dominance slice the common part agrees with the left kernel. -/
theorem commonPartKernel_apply_compl_dominanceSlice
    (K Ktilde : Kernel Y Ω) [IsFiniteKernel K] [IsFiniteKernel Ktilde]
    (y : Y) :
    commonPartKernel K Ktilde y (dominanceSlice K Ktilde y)ᶜ =
      K y (dominanceSlice K Ktilde y)ᶜ := by
  let A := dominanceSlice K Ktilde y
  have hA : MeasurableSet A := measurableSet_dominanceSlice K Ktilde y
  rw [commonPartKernel, Kernel.withDensity_apply'
      _ (measurable_commonDensity K Ktilde) y Aᶜ]
  rw [← Kernel.withDensity_rnDerivAux K Ktilde]
  rw [Kernel.withDensity_apply']
  · apply setLIntegral_congr_fun hA.compl
    intro x hx
    exact commonDensity_eq_left_of_not_mem_dominanceSlice K Ktilde y hx
  · exact (Kernel.measurable_rnDerivAux K (K + Ktilde)).ennreal_ofReal

/-- The total common mass splits into the right mass on the dominance slice and
the left mass on its complement. -/
theorem commonPartKernel_univ_eq
    (K Ktilde : Kernel Y Ω) [IsFiniteKernel K] [IsFiniteKernel Ktilde]
    (y : Y) :
    commonPartKernel K Ktilde y Set.univ =
      Ktilde y (dominanceSlice K Ktilde y) +
        K y (dominanceSlice K Ktilde y)ᶜ := by
  have hA := measurableSet_dominanceSlice K Ktilde y
  rw [← union_compl_self (dominanceSlice K Ktilde y)]
  rw [measure_union hA hA.compl disjoint_compl_right]
  rw [commonPartKernel_apply_dominanceSlice,
      commonPartKernel_apply_compl_dominanceSlice]

end ProbabilitySupport
end PermanssonLean
