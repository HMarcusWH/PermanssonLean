import PermanssonResearch.ReverseSolver.FiniteStrategicRealization
import PermanssonLean.Regime.GeneratedRegime
import Mathlib.Tactic

/-!
# C-Exit independent typed finite test models

These are actual rational α→P→U strategic-world realizations, not assumed
joint matrices.  They provide exact finite rational rows and falsifiers
for false QSD-to-all-state or arrival-to-stay conclusions.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit.ExitModels

open PermanssonLean
open PermanssonResearch.ReverseSolver
open PermanssonResearch.ReverseSolver.FiniteStrategicRealization

/-- One transient b=0, absorbing outside destinations a=1,c=2. -/
def f1Matrix : RationalMarkovMatrix 3 where
  entry := fun y z =>
    if y = 0 then
      if z = 0 then 1/2 else if z = 1 then 1/3 else 1/6
    else if z = y then 1 else 0
  entry_nonneg := by
    intro y z
    split_ifs <;> norm_num
  row_sum_one := by
    intro y
    fin_cases y <;> norm_num [Fin.sum_univ_three]

/-- Transient d=0, permanent inside b=1, absorbing exit a=2. -/
def f2Matrix : RationalMarkovMatrix 3 where
  entry := fun y z =>
    if y = 0 then
      if z = 0 then 1/2 else if z = 1 then 1/4 else 1/4
    else if z = y then 1 else 0
  entry_nonneg := by
    intro y z
    split_ifs <;> norm_num
  row_sum_one := by
    intro y
    fin_cases y <;> norm_num [Fin.sum_univ_three]

/-- b=0 is permanently inside, d=1 exits to a=2,
and the outside a=2 leaves itself for c=3. -/
def f4Matrix : RationalMarkovMatrix 4 where
  entry := fun y z =>
    if y = 0 then
      if z = 0 then 1 else 0
    else if y = 1 then
      if z = 2 then 1 else 0
    else if z = 3 then 1 else 0
  entry_nonneg := by
    intro y z
    split_ifs <;> norm_num
  row_sum_one := by
    intro y
    fin_cases y <;> norm_num [Fin.sum_univ_four]

abbrev Y3 := JointState Unit (Fin 3)
abbrev Y4 := JointState Unit (Fin 4)

noncomputable def f1Model : StrategicWorldModel Unit (Fin 3) (Fin 3) :=
  realizedModel f1Matrix

noncomputable def f2Model : StrategicWorldModel Unit (Fin 3) (Fin 3) :=
  realizedModel f2Matrix

noncomputable def f4Model : StrategicWorldModel Unit (Fin 4) (Fin 4) :=
  realizedModel f4Matrix

noncomputable def f1Spec : RegimeSpecification Y3 (Fin 3) where
  region := {y | y.2 = 0}
  region_measurable := MeasurableSet.of_discrete
  basin := {y | y.2 = 0}
  basin_measurable := MeasurableSet.of_discrete
  basin_subset_region := Set.Subset.rfl
  descriptor := Prod.snd
  descriptor_measurable := measurable_snd
  target := ⟨Measure.dirac 0, inferInstance⟩
  convergenceMode := RegimeSpecification.ConvergenceMode.almostSureWeak Y3 (Fin 3)

noncomputable def f2Spec : RegimeSpecification Y3 (Fin 3) where
  region := {y | y.2 = 0 ∨ y.2 = 1}
  region_measurable := MeasurableSet.of_discrete
  basin := {y | y.2 = 0 ∨ y.2 = 1}
  basin_measurable := MeasurableSet.of_discrete
  basin_subset_region := Set.Subset.rfl
  descriptor := Prod.snd
  descriptor_measurable := measurable_snd
  target := ⟨Measure.dirac 1, inferInstance⟩
  convergenceMode := RegimeSpecification.ConvergenceMode.almostSureWeak Y3 (Fin 3)

noncomputable def f4Spec : RegimeSpecification Y4 (Fin 4) where
  region := {y | y.2 = 0 ∨ y.2 = 1}
  region_measurable := MeasurableSet.of_discrete
  basin := {y | y.2 = 0 ∨ y.2 = 1}
  basin_measurable := MeasurableSet.of_discrete
  basin_subset_region := Set.Subset.rfl
  descriptor := Prod.snd
  descriptor_measurable := measurable_snd
  target := ⟨Measure.dirac 0, inferInstance⟩
  convergenceMode := RegimeSpecification.ConvergenceMode.almostSureWeak Y4 (Fin 4)

theorem f1_kernel_b_to_a :
    f1Model.inducedKernel (decode (0 : Fin 3))
        (encode ⁻¹' ({1} : Set (Fin 3))) =
      ENNReal.ofReal (1/3 : ℝ) := by
  change (realizedModel f1Matrix).inducedKernel (decode 0)
    (encode ⁻¹' ({1} : Set (Fin 3))) = _
  rw [inducedKernel_encodedEntry f1Matrix 0 1]
  norm_num [f1Matrix]

theorem f1_kernel_b_to_c :
    f1Model.inducedKernel (decode (0 : Fin 3))
        (encode ⁻¹' ({2} : Set (Fin 3))) =
      ENNReal.ofReal (1/6 : ℝ) := by
  change (realizedModel f1Matrix).inducedKernel (decode 0)
    (encode ⁻¹' ({2} : Set (Fin 3))) = _
  rw [inducedKernel_encodedEntry f1Matrix 0 2]
  norm_num [f1Matrix]

theorem f4_kernel_d_to_a :
    f4Model.inducedKernel (decode (1 : Fin 4))
        (encode ⁻¹' ({2} : Set (Fin 4))) = 1 := by
  change (realizedModel f4Matrix).inducedKernel (decode 1)
    (encode ⁻¹' ({2} : Set (Fin 4))) = _
  rw [inducedKernel_encodedEntry f4Matrix 1 2]
  norm_num [f4Matrix]

theorem f4_kernel_a_to_c :
    f4Model.inducedKernel (decode (2 : Fin 4))
        (encode ⁻¹' ({3} : Set (Fin 4))) = 1 := by
  change (realizedModel f4Matrix).inducedKernel (decode 2)
    (encode ⁻¹' ({3} : Set (Fin 4))) = _
  rw [inducedKernel_encodedEntry f4Matrix 2 3]
  norm_num [f4Matrix]

end PermanssonResearch.RegimeExit.ExitModels
