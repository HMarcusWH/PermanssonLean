import PermanssonLean.Regime.Admissible
import PermanssonLean.StrategicWorld.WellPosedness
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Topology.Defs.Basic

open MeasureTheory Set

namespace PermanssonLean

universe uS uX uA uH

variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]
variable [TopologicalSpace S] [TopologicalSpace X]

namespace RegimeSpecification

/-- Paper Assumption 4.1(ii): the regime region has nonempty interior or
positive mass under the reference measure frozen with the model. -/
def RegionNontrivial
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X)) : Prop :=
  (interior spec.region).Nonempty ∨ 0 < m spec.region

/-- Paper Assumption 4.1(iii): the descriptor takes at least two values on B. -/
def DescriptorHasTwoValues
    (spec : RegimeSpecification (JointState S X) H) : Prop :=
  ∃ y₁ ∈ spec.region, ∃ y₂ ∈ spec.region,
    spec.descriptor y₁ ≠ spec.descriptor y₂

/-- Paper Assumption 4.1(iv), stated literally in path-law form. -/
def BasinPathLawNontrivial
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H) : Prop :=
  ∃ y₁ ∈ spec.basin, ∃ y₂ ∈ spec.basin,
    M.pathLaw (Measure.dirac y₁) ≠ M.pathLaw (Measure.dirac y₂)

/-- The simpler state-space form of Assumption 4.1(iv).  The paper notes
that this is equivalent to `BasinPathLawNontrivial` because coordinate zero
is deterministic under point initialization. -/
def BasinHasTwoStates
    (spec : RegimeSpecification (JointState S X) H) : Prop :=
  ∃ y₁ ∈ spec.basin, ∃ y₂ ∈ spec.basin, y₁ ≠ y₂

theorem basinPathLawNontrivial_implies_two_states
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (h : BasinPathLawNontrivial M spec) :
    BasinHasTwoStates spec := by
  rcases h with ⟨y₁, hy₁, y₂, hy₂, hneq⟩
  refine ⟨y₁, hy₁, y₂, hy₂, ?_⟩
  intro hEq
  apply hneq
  subst y₂
  rfl

/-- Under the paper's point-separating Borel state space, two distinct basin
states induce distinct baseline path laws. This proves the equivalence noted
immediately after Assumption 4.1(iv), rather than leaving it as prose. -/
theorem two_states_implies_basinPathLawNontrivial
    [MeasurableSpace.SeparatesPoints (JointState S X)]
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (h : BasinHasTwoStates spec) :
    BasinPathLawNontrivial M spec := by
  rcases h with ⟨y₁, hy₁, y₂, hy₂, hne⟩
  refine ⟨y₁, hy₁, y₂, hy₂, ?_⟩
  intro hpaths
  have hpref := congrArg
    (fun μ : Measure (ℕ → JointState S X) =>
      μ.map (Preorder.frestrictLe 0)) hpaths
  rw [StrategicWorldModel.pathLaw_prefix_zero M (Measure.dirac y₁),
      StrategicWorldModel.pathLaw_prefix_zero M (Measure.dirac y₂)] at hpref
  letI : Unique (Set.Iic (0 : ℕ)) := {
    default := ⟨0, by simp⟩
    uniq := fun i => by
      apply Subtype.ext
      exact Nat.eq_zero_of_le_zero (Set.mem_Iic.mp i.2)
  }
  let e := MeasurableEquiv.piUnique
    (fun _ : Set.Iic (0 : ℕ) => JointState S X)
  have hdirac : Measure.dirac y₁ = Measure.dirac y₂ :=
    e.symm.measurableEmbedding.map_injective hpref
  exact hne (MeasureTheory.dirac_eq_dirac_iff.mp hdirac)

theorem basinHasTwoStates_iff_pathLawNontrivial
    [MeasurableSpace.SeparatesPoints (JointState S X)]
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H) :
    BasinHasTwoStates spec ↔ BasinPathLawNontrivial M spec :=
  ⟨two_states_implies_basinPathLawNontrivial M spec,
    basinPathLawNontrivial_implies_two_states M spec⟩

/-- Ex-ante non-triviality gate from Assumption 4.1.

Clause (v), declaration before evaluated classification, is represented by the
formal API boundary: the complete immutable `RegimeSpecification` and reference
measure are inputs to the classifier. Lean does not pretend to infer historical
chronology from already-constructed values.
-/
def Assumption41
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X)) : Prop :=
  spec.basin.Nonempty ∧
  RegionNontrivial spec m ∧
  DescriptorHasTwoValues spec ∧
  BasinPathLawNontrivial M spec

theorem assumption41_basin_nonempty
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (h : Assumption41 M spec m) :
    spec.basin.Nonempty :=
  h.1

theorem assumption41_basin_has_two_states
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (h : Assumption41 M spec m) :
    BasinHasTwoStates spec :=
  basinPathLawNontrivial_implies_two_states M spec h.2.2.2

end RegimeSpecification

end PermanssonLean
