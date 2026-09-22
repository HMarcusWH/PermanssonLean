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

/-- The real-valued Radon--Nikodym auxiliary density of `K` relative to
the common dominating kernel `K + Ktilde`. -/
noncomputable def leftDensity
    (K Ktilde : Kernel Y Ω) (y : Y) (x : Ω) : ℝ :=
  Kernel.rnDerivAux K (K + Ktilde) y x

/-- The left density in the `ℝ≥0∞` codomain expected by `withDensity`. -/
noncomputable def leftWeight
    (K Ktilde : Kernel Y Ω) (y : Y) (x : Ω) : ℝ≥0∞ :=
  ((Real.toNNReal (leftDensity K Ktilde y x) : ℝ≥0) : ℝ≥0∞)

/-- The complementary/right density in the same common dominating measure. -/
noncomputable def rightWeight
    (K Ktilde : Kernel Y Ω) (y : Y) (x : Ω) : ℝ≥0∞ :=
  ((Real.toNNReal (1 - leftDensity K Ktilde y x) : ℝ≥0) : ℝ≥0∞)

/-- Pointwise overlap density relative to `K + Ktilde`. -/
noncomputable def commonDensity
    (K Ktilde : Kernel Y Ω) (y : Y) (x : Ω) : ℝ≥0∞ :=
  min (leftWeight K Ktilde y x) (rightWeight K Ktilde y x)

theorem measurable_leftWeight (K Ktilde : Kernel Y Ω) :
    Measurable (Function.uncurry (leftWeight K Ktilde)) := by
  unfold leftWeight leftDensity
  exact ((Kernel.measurable_rnDerivAux K (K + Ktilde)).real_toNNReal).coe_nnreal_ennreal

theorem measurable_rightWeight (K Ktilde : Kernel Y Ω) :
    Measurable (Function.uncurry (rightWeight K Ktilde)) := by
  unfold rightWeight leftDensity
  exact ((measurable_const.sub
    (Kernel.measurable_rnDerivAux K (K + Ktilde))).real_toNNReal).coe_nnreal_ennreal

theorem measurable_commonDensity (K Ktilde : Kernel Y Ω) :
    Measurable (Function.uncurry (commonDensity K Ktilde)) := by
  unfold commonDensity
  exact Measurable.min (measurable_leftWeight K Ktilde)
    (measurable_rightWeight K Ktilde)

/-- Mathlib's RN auxiliary decomposition, restated using the local left weight. -/
theorem withDensity_leftWeight_eq
    (K Ktilde : Kernel Y Ω) [IsFiniteKernel K] [IsFiniteKernel Ktilde] :
    Kernel.withDensity (K + Ktilde) (leftWeight K Ktilde) = K := by
  simpa [leftWeight, leftDensity] using
    (Kernel.withDensity_rnDerivAux K Ktilde)

/-- Mathlib's complementary RN decomposition, restated using the local right weight. -/
theorem withDensity_rightWeight_eq
    (K Ktilde : Kernel Y Ω) [IsFiniteKernel K] [IsFiniteKernel Ktilde] :
    Kernel.withDensity (K + Ktilde) (rightWeight K Ktilde) = Ktilde := by
  simpa [rightWeight, leftDensity] using
    (Kernel.withDensity_one_sub_rnDerivAux K Ktilde)

/-- A measurable finite kernel carrying the pointwise density shared by `K`
and `Ktilde` relative to the common dominating kernel `K + Ktilde`. -/
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
    commonDensity K Ktilde y x ≤ leftWeight K Ktilde y x :=
  min_le_left _ _

/-- The overlap density is pointwise dominated by the complementary/right RN density. -/
theorem commonDensity_le_right
    (K Ktilde : Kernel Y Ω) (y : Y) (x : Ω) :
    commonDensity K Ktilde y x ≤ rightWeight K Ktilde y x :=
  min_le_right _ _

/-- The common-part kernel is a subkernel of `K`. -/
theorem commonPartKernel_le_left
    (K Ktilde : Kernel Y Ω) [IsFiniteKernel K] [IsFiniteKernel Ktilde] :
    commonPartKernel K Ktilde ≤ K := by
  intro y
  rw [commonPartKernel_apply]
  calc
    ((K + Ktilde) y).withDensity (commonDensity K Ktilde y) ≤
        ((K + Ktilde) y).withDensity (leftWeight K Ktilde y) :=
      MeasureTheory.withDensity_mono
        (ae_of_all _ (commonDensity_le_left K Ktilde y))
    _ = (Kernel.withDensity (K + Ktilde) (leftWeight K Ktilde)) y := by
      rw [Kernel.withDensity_apply _ (measurable_leftWeight K Ktilde)]
    _ = K y := by
      exact congrArg (fun κ : Kernel Y Ω => κ y)
        (withDensity_leftWeight_eq K Ktilde)

/-- The common-part kernel is a subkernel of `Ktilde`. -/
theorem commonPartKernel_le_right
    (K Ktilde : Kernel Y Ω) [IsFiniteKernel K] [IsFiniteKernel Ktilde] :
    commonPartKernel K Ktilde ≤ Ktilde := by
  intro y
  rw [commonPartKernel_apply]
  calc
    ((K + Ktilde) y).withDensity (commonDensity K Ktilde y) ≤
        ((K + Ktilde) y).withDensity (rightWeight K Ktilde y) :=
      MeasureTheory.withDensity_mono
        (ae_of_all _ (commonDensity_le_right K Ktilde y))
    _ = (Kernel.withDensity (K + Ktilde) (rightWeight K Ktilde)) y := by
      rw [Kernel.withDensity_apply _ (measurable_rightWeight K Ktilde)]
    _ = Ktilde y := by
      exact congrArg (fun κ : Kernel Y Ω => κ y)
        (withDensity_rightWeight_eq K Ktilde)

/-- The common part is finite whenever both source kernels are finite. -/
instance commonPartKernel_isFinite
    (K Ktilde : Kernel Y Ω) [IsFiniteKernel K] [IsFiniteKernel Ktilde] :
    IsFiniteKernel (commonPartKernel K Ktilde) :=
  isFiniteKernel_of_le (commonPartKernel_le_left K Ktilde)

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
    commonDensity K Ktilde y x = rightWeight K Ktilde y x := by
  change (1 / 2 : ℝ) ≤ leftDensity K Ktilde y x at hx
  unfold commonDensity
  rw [min_eq_right]
  unfold leftWeight rightWeight
  exact ENNReal.coe_le_coe.mpr (Real.toNNReal_mono (by linarith))

theorem commonDensity_eq_left_of_not_mem_dominanceSlice
    (K Ktilde : Kernel Y Ω) (y : Y) {x : Ω}
    (hx : x ∉ dominanceSlice K Ktilde y) :
    commonDensity K Ktilde y x = leftWeight K Ktilde y x := by
  have hx' : leftDensity K Ktilde y x < (1 / 2 : ℝ) := by
    change ¬ (1 / 2 : ℝ) ≤ leftDensity K Ktilde y x at hx
    exact lt_of_not_ge hx
  unfold commonDensity
  rw [min_eq_left]
  unfold leftWeight rightWeight
  exact ENNReal.coe_le_coe.mpr (Real.toNNReal_mono (by linarith))

/-- On the dominance slice the common part agrees with the right kernel. -/
theorem commonPartKernel_apply_dominanceSlice
    (K Ktilde : Kernel Y Ω) [IsFiniteKernel K] [IsFiniteKernel Ktilde]
    (y : Y) :
    commonPartKernel K Ktilde y (dominanceSlice K Ktilde y) =
      Ktilde y (dominanceSlice K Ktilde y) := by
  let A := dominanceSlice K Ktilde y
  have hA : MeasurableSet A := measurableSet_dominanceSlice K Ktilde y
  calc
    commonPartKernel K Ktilde y A =
        ∫⁻ x in A, commonDensity K Ktilde y x ∂(K + Ktilde) y := by
      rw [commonPartKernel, Kernel.withDensity_apply'
        _ (measurable_commonDensity K Ktilde) y A]
    _ = ∫⁻ x in A, rightWeight K Ktilde y x ∂(K + Ktilde) y := by
      apply setLIntegral_congr_fun hA
      intro x hx
      exact commonDensity_eq_right_of_mem_dominanceSlice K Ktilde y hx
    _ = Kernel.withDensity (K + Ktilde) (rightWeight K Ktilde) y A := by
      rw [Kernel.withDensity_apply'
        _ (measurable_rightWeight K Ktilde) y A]
    _ = Ktilde y A := by
      rw [withDensity_rightWeight_eq K Ktilde]

/-- Off the dominance slice the common part agrees with the left kernel. -/
theorem commonPartKernel_apply_compl_dominanceSlice
    (K Ktilde : Kernel Y Ω) [IsFiniteKernel K] [IsFiniteKernel Ktilde]
    (y : Y) :
    commonPartKernel K Ktilde y (dominanceSlice K Ktilde y)ᶜ =
      K y (dominanceSlice K Ktilde y)ᶜ := by
  let A := dominanceSlice K Ktilde y
  have hA : MeasurableSet A := measurableSet_dominanceSlice K Ktilde y
  calc
    commonPartKernel K Ktilde y Aᶜ =
        ∫⁻ x in Aᶜ, commonDensity K Ktilde y x ∂(K + Ktilde) y := by
      rw [commonPartKernel, Kernel.withDensity_apply'
        _ (measurable_commonDensity K Ktilde) y Aᶜ]
    _ = ∫⁻ x in Aᶜ, leftWeight K Ktilde y x ∂(K + Ktilde) y := by
      apply setLIntegral_congr_fun hA.compl
      intro x hx
      exact commonDensity_eq_left_of_not_mem_dominanceSlice K Ktilde y hx
    _ = Kernel.withDensity (K + Ktilde) (leftWeight K Ktilde) y Aᶜ := by
      rw [Kernel.withDensity_apply'
        _ (measurable_leftWeight K Ktilde) y Aᶜ]
    _ = K y Aᶜ := by
      rw [withDensity_leftWeight_eq K Ktilde]

/-- The total common mass splits into the right mass on the dominance slice and
the left mass on its complement. -/
theorem commonPartKernel_univ_eq
    (K Ktilde : Kernel Y Ω) [IsFiniteKernel K] [IsFiniteKernel Ktilde]
    (y : Y) :
    commonPartKernel K Ktilde y Set.univ =
      Ktilde y (dominanceSlice K Ktilde y) +
        K y (dominanceSlice K Ktilde y)ᶜ := by
  let A := dominanceSlice K Ktilde y
  have hA : MeasurableSet A := measurableSet_dominanceSlice K Ktilde y
  calc
    commonPartKernel K Ktilde y Set.univ =
        commonPartKernel K Ktilde y (A ∪ Aᶜ) := by simp [A]
    _ = commonPartKernel K Ktilde y A +
        commonPartKernel K Ktilde y Aᶜ := by
      rw [measure_union disjoint_compl_right hA.compl]
    _ = Ktilde y A + K y Aᶜ := by
      rw [commonPartKernel_apply_dominanceSlice,
        commonPartKernel_apply_compl_dominanceSlice]


/-- On the RN dominance slice the right probability mass is no larger than the
left probability mass. -/
theorem right_le_left_on_dominanceSlice
    (K Ktilde : Kernel Y Ω) [IsFiniteKernel K] [IsFiniteKernel Ktilde]
    (y : Y) :
    Ktilde y (dominanceSlice K Ktilde y) ≤
      K y (dominanceSlice K Ktilde y) := by
  rw [← commonPartKernel_apply_dominanceSlice K Ktilde y]
  exact (commonPartKernel_le_left K Ktilde y)
    (dominanceSlice K Ktilde y)

/-- Real-valued form of the common-mass decomposition for Markov kernels. -/
theorem commonPartKernel_real_univ_eq
    (K Ktilde : Kernel Y Ω) [IsMarkovKernel K] [IsMarkovKernel Ktilde]
    (y : Y) :
    (commonPartKernel K Ktilde y).real Set.univ =
      (Ktilde y).real (dominanceSlice K Ktilde y) +
        (K y).real (dominanceSlice K Ktilde y)ᶜ := by
  have h := congrArg ENNReal.toReal (commonPartKernel_univ_eq K Ktilde y)
  simpa [Measure.real, ENNReal.toReal_add] using h

/-- The missing mass of the measurable common subkernel is bounded by the
paper's event-supremum total variation.  This is the one-step bridge needed
for the finite-prefix propagation proof of Proposition 5.4. -/
theorem one_sub_commonPartKernel_real_univ_le_eventTotalVariation
    (K Ktilde : Kernel Y Ω) [IsMarkovKernel K] [IsMarkovKernel Ktilde]
    (y : Y) :
    1 - (commonPartKernel K Ktilde y).real Set.univ ≤
      eventTotalVariation (K y) (Ktilde y) := by
  let A := dominanceSlice K Ktilde y
  have hA : MeasurableSet A := measurableSet_dominanceSlice K Ktilde y
  have hQ :
      (commonPartKernel K Ktilde y).real Set.univ =
        (Ktilde y).real A + (K y).real Aᶜ := by
    simpa [A] using commonPartKernel_real_univ_eq K Ktilde y
  have hK :
      (K y).real A + (K y).real Aᶜ = 1 :=
    probReal_add_probReal_compl hA
  have hdomENN :
      Ktilde y A ≤ K y A := by
    simpa [A] using right_le_left_on_dominanceSlice K Ktilde y
  have hdom :
      (Ktilde y).real A ≤ (K y).real A :=
    ENNReal.toReal_mono (by finiteness) hdomENN
  have hdiff : 0 ≤ (K y).real A - (Ktilde y).real A :=
    sub_nonneg.mpr hdom
  have hchosen :=
    abs_measureReal_sub_le_eventTotalVariation
      (K y) (Ktilde y) hA
  calc
    1 - (commonPartKernel K Ktilde y).real Set.univ =
        (K y).real A - (Ktilde y).real A := by linarith
    _ = |(K y).real A - (Ktilde y).real A| := by
      rw [abs_of_nonneg hdiff]
    _ ≤ eventTotalVariation (K y) (Ktilde y) := hchosen

/-- A uniform one-step TV bound leaves at least `1 - ε` common mass at every
state. -/
theorem one_sub_le_commonPartKernel_real_univ_of_uniformTV
    (K Ktilde : Kernel Y Ω) [IsMarkovKernel K] [IsMarkovKernel Ktilde]
    {ε : ℝ} (hTV : HasUniformEventTVBound K Ktilde ε) (y : Y) :
    1 - ε ≤ (commonPartKernel K Ktilde y).real Set.univ := by
  have hmiss :=
    one_sub_commonPartKernel_real_univ_le_eventTotalVariation K Ktilde y
  have hstep := hTV y
  linarith

end ProbabilitySupport
end PermanssonLean
