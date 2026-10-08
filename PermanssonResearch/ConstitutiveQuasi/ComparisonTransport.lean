import PermanssonResearch.ConstitutiveQuasi.Certificate
import PermanssonLean.Regime.Assumption41

/-!
# CQ-1: transport of the original frozen comparison set

Point-started canonical path laws distinguish different initial states whenever
the measurable joint-state space separates points. This does not require equality
of induced kernels and does not assert any property-value invariance.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace PermanssonResearch
namespace ConstitutiveQuasi

universe uS uX uA uH
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]

/-- Distinct point starts induce different canonical whole-path laws for
*any* strategic-world model, by the time-zero marginal. -/
theorem pointStarted_pathLaw_ne_of_ne
    [MeasurableSpace.SeparatesPoints (PermanssonLean.JointState S X)]
    (M : PermanssonLean.StrategicWorldModel S X A)
    {y₁ y₂ : PermanssonLean.JointState S X}
    (hne : y₁ ≠ y₂) :
    M.pathLaw (Measure.dirac y₁) ≠ M.pathLaw (Measure.dirac y₂) := by
  intro hpaths
  have hpref := congrArg
    (fun μ : Measure (ℕ → PermanssonLean.JointState S X) =>
      μ.map (Preorder.frestrictLe 0)) hpaths
  rw [PermanssonLean.StrategicWorldModel.pathLaw_prefix_zero M (Measure.dirac y₁),
      PermanssonLean.StrategicWorldModel.pathLaw_prefix_zero M (Measure.dirac y₂)]
    at hpref
  let e := MeasurableEquiv.piUnique
    (fun _ : Finset.Iic (0 : ℕ) => PermanssonLean.JointState S X)
  have hdirac :
      Measure.dirac y₁ = Measure.dirac y₂ :=
    e.symm.measurableEmbedding.map_injective (by simpa [e] using hpref)
  exact hne (MeasureTheory.dirac_eq_dirac_iff.mp hdirac)

/-- Preserve the very same declared measurable comparison set between models
without asserting equality of transition kernels. -/
noncomputable def transportComparisonSet
    [MeasurableSpace.SeparatesPoints (PermanssonLean.JointState S X)]
    (M Mtilde : PermanssonLean.StrategicWorldModel S X A)
    (spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H)
    (B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec) :
    PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet Mtilde spec where
  states := B₁.states
  states_measurable := B₁.states_measurable
  states_subset_basin := B₁.states_subset_basin
  pathLawNontrivial := by
    rcases B₁.pathLawNontrivial with ⟨y₁, hy₁, y₂, hy₂, hne⟩
    have hdiff : y₁ ≠ y₂ := by
      intro hEq
      apply hne
      subst y₂
      rfl
    exact ⟨y₁, hy₁, y₂, hy₂, pointStarted_pathLaw_ne_of_ne Mtilde hdiff⟩

@[simp] theorem transportComparisonSet_states
    [MeasurableSpace.SeparatesPoints (PermanssonLean.JointState S X)]
    (M Mtilde : PermanssonLean.StrategicWorldModel S X A)
    (spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H)
    (B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec) :
    (transportComparisonSet M Mtilde spec B₁).states = B₁.states := rfl

end ConstitutiveQuasi
end PermanssonResearch
