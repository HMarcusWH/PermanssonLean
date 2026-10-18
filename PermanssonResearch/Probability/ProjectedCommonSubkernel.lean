import PermanssonLean.Probability.CommonPartKernel
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! Q-LIFT: pull a jointly measurable coarse density back to the fine space.
The RN wrapper retains the exact countable-or-countably-generated instance.
It uses no disintegration of quotient fibres. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.Probability

variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]

noncomputable def liftProjectedDensity (q : Y → Z) (K : Kernel Y Y)
    [IsSFiniteKernel K] (r : Y → Z → ℝ≥0∞) : Kernel Y Y :=
  Kernel.withDensity K (fun y z => r y (q z))

theorem measurable_liftProjectedDensity_weight {q : Y → Z} (hq : Measurable q)
    {r : Y → Z → ℝ≥0∞} (hr : Measurable (Function.uncurry r)) :
    Measurable (Function.uncurry (fun y z => r y (q z))) :=
  hr.comp (measurable_fst.prodMk (hq.comp measurable_snd))

theorem liftProjectedDensity_le {q : Y → Z} (hq : Measurable q)
    (K : Kernel Y Y) [IsSFiniteKernel K]
    {r : Y → Z → ℝ≥0∞} (hr : Measurable (Function.uncurry r))
    (hr1 : ∀ y z, r y z ≤ 1) : liftProjectedDensity q K r ≤ K := by
  intro y
  rw [liftProjectedDensity, Kernel.withDensity_apply _
    (measurable_liftProjectedDensity_weight hq hr)]
  calc (K y).withDensity (fun z => r y (q z))
      ≤ (K y).withDensity (fun _ => 1) :=
        withDensity_mono (Filter.Eventually.of_forall fun z => hr1 y (q z))
    _ = K y := by simp

/-- Projection of the fine weighted row is exactly the prescribed coarse
density measure, including zero-mass fibres. -/
theorem map_liftProjectedDensity {q : Y → Z} (hq : Measurable q)
    (K : Kernel Y Y) [IsSFiniteKernel K]
    {r : Y → Z → ℝ≥0∞} (hr : Measurable (Function.uncurry r)) (y : Y) :
    (liftProjectedDensity q K r y).map q = ((K y).map q).withDensity (r y) := by
  ext E hE
  rw [Measure.map_apply hq hE, liftProjectedDensity,
    Kernel.withDensity_apply _ (measurable_liftProjectedDensity_weight hq hr),
    withDensity_apply _ (hq hE), withDensity_apply _ hE,
    setLIntegral_map hE (Measurable.of_uncurry_left hr) hq]

section RN

variable [MeasurableSpace.CountableOrCountablyGenerated Y Z]

/-- Clip the measurable kernel RN density; domination makes clipping AE inert. -/
noncomputable def clippedProjectedDensity (M P : Kernel Y Z) : Y → Z → ℝ≥0∞ :=
  fun y z => min 1 (M.rnDeriv P y z)

theorem measurable_clippedProjectedDensity (M P : Kernel Y Z) :
    Measurable (Function.uncurry (clippedProjectedDensity M P)) :=
  measurable_const.min (Kernel.measurable_rnDeriv M P)

theorem clippedProjectedDensity_le_one (M P : Kernel Y Z) (y : Y) (z : Z) :
    clippedProjectedDensity M P y z ≤ 1 := min_le_left _ _

/-- RN recovery from a genuinely dominated finite kernel. -/
theorem withDensity_clippedProjectedDensity (M P : Kernel Y Z)
    [IsFiniteKernel M] [IsFiniteKernel P] (hMP : M ≤ P) (y : Y) :
    (P y).withDensity (clippedProjectedDensity M P y) = M y := by
  have hle : ∀ᵐ z ∂P y, M.rnDeriv P y z ≤ 1 := by
    filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := M) (η := P) (a := y),
      Measure.rnDeriv_le_one_of_le (hMP y)] with z hz hle
    exact hz ▸ hle
  have heq : clippedProjectedDensity M P y =ᵐ[P y] M.rnDeriv P y := by
    filter_upwards [hle] with z hz
    exact min_eq_right hz
  rw [withDensity_congr_ae heq]
  have h := Kernel.withDensity_rnDeriv_eq (κ := M) (η := P)
    (Measure.absolutelyContinuous_of_le (hMP y))
  rw [Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv M P)] at h
  exact h

end RN

end PermanssonResearch.Probability
