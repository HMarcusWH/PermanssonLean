import PermanssonResearch.ReverseSolver.RationalFiniteStoppingBounds
import PermanssonResearch.ReverseSolver.FiniteStrategicPathBridge
import PermanssonResearch.MultipleLimit.FiniteCanonicalPath
import Mathlib.Tactic

/-!
# C10 — finite stopped-class events on the genuine typed path law

The exact rational stopped-class recurrence is evaluated on the original
Ionescu–Tulcea infinite path measure of the actual D0 alpha/P/U process.
No equality between rational absorption weights and infinite-horizon
class selection is assumed here; the finite-event identity is the input
to that separate limiting argument.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

open FiniteStrategicRealization
open FiniteStrategicPathBridge
open PermanssonResearch.MultipleLimit.FiniteCanonicalPath

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

/-- The authentic finite prefix event: first enter bottom class C before
entering any other bottom recurrent state. -/
def typedStoppedClassEvent {n : ℕ}
    (K : RationalMarkovMatrix n) (C : Finset (Fin n)) (T : ℕ) :
    Set (ℕ → PermanssonLean.JointState Unit (Fin n)) :=
  (Preorder.frestrictLe T) ⁻¹'
    successPrefixEvent (typedTarget (classFirstTarget K C)) T

theorem typedStoppedClassEvent_measurable {n : ℕ}
    (K : RationalMarkovMatrix n) (C : Finset (Fin n)) (T : ℕ) :
    MeasurableSet (typedStoppedClassEvent K C T) :=
  (measurableSet_successPrefixEvent
    (typedTarget (classFirstTarget K C)) T).preimage
      (Preorder.measurable_frestrictLe T)

/-- Exact time-zero-inclusive path characterization; the forbidden set is
predeclared as all other recurrent states, with no stopping-time shortcut. -/
theorem typedStoppedClassEvent_iff {n : ℕ}
    (K : RationalMarkovMatrix n) (C : Finset (Fin n)) (T : ℕ)
    (w : ℕ → PermanssonLean.JointState Unit (Fin n)) :
    w ∈ typedStoppedClassEvent K C T ↔
      ∃ t : ℕ, t ≤ T ∧ encode (w t) ∈ C ∧
        ∀ s : ℕ, s < t → encode (w s) ∉ rationalRecurrentUnion K \ C := by
  constructor
  · intro hw
    change Preorder.frestrictLe T w ∈
      successPrefixEvent (typedTarget (classFirstTarget K C)) T at hw
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hw
    have hgoal : encode (w (i : ℕ)) ∈ C := by
      simpa [typedTarget, rationalTargetAsFrozen, classFirstTarget]
        using hi.1
    refine ⟨(i : ℕ), Finset.mem_Iic.mp i.property, hgoal, ?_⟩
    intro s hs
    have hsT : s ≤ T := (Nat.le_of_lt hs).trans
      (Finset.mem_Iic.mp i.property)
    have hno := (Set.mem_iInter.mp hi.2)
      (⟨s, Finset.mem_Iic.mpr hsT⟩ : Finset.Iic T)
    have hforbid := hno hs
    simpa [typedTarget, rationalTargetAsFrozen, classFirstTarget]
      using hforbid
  · rintro ⟨t, ht, hgoal, hno⟩
    change Preorder.frestrictLe T w ∈
      successPrefixEvent (typedTarget (classFirstTarget K C)) T
    apply Set.mem_iUnion.mpr
    refine ⟨⟨t, Finset.mem_Iic.mpr ht⟩, ?_⟩
    constructor
    · simpa [typedTarget, rationalTargetAsFrozen, classFirstTarget]
        using hgoal
    · apply Set.mem_iInter.mpr
      intro u
      intro hu
      have hh := hno (u : ℕ) hu
      simpa [typedTarget, rationalTargetAsFrozen, classFirstTarget]
        using hh

/-- The finite stopped event is monotone in the observed horizon. -/
theorem typedStoppedClassEvent_monotone {n : ℕ}
    (K : RationalMarkovMatrix n) (C : Finset (Fin n)) :
    Monotone (typedStoppedClassEvent K C) := by
  intro a b hab w hw
  obtain ⟨t, ht, hC, hno⟩ :=
    (typedStoppedClassEvent_iff K C a w).mp hw
  exact (typedStoppedClassEvent_iff K C b w).mpr
    ⟨t, ht.trans hab, hC, hno⟩

/-- Every future hit is already detected by some finite horizon. -/
theorem typedStoppedClassEvent_iUnion {n : ℕ}
    (K : RationalMarkovMatrix n) (C : Finset (Fin n)) :
    (⋃ T : ℕ, typedStoppedClassEvent K C T) =
      {w : ℕ → PermanssonLean.JointState Unit (Fin n) |
        ∃ t : ℕ, encode (w t) ∈ C ∧
          ∀ s : ℕ, s < t → encode (w s) ∉ rationalRecurrentUnion K \ C} := by
  ext w
  constructor
  · intro hw
    obtain ⟨T, hT⟩ := Set.mem_iUnion.mp hw
    obtain ⟨t, _, hc, hn⟩ :=
      (typedStoppedClassEvent_iff K C T w).mp hT
    exact ⟨t, hc, hn⟩
  · rintro ⟨t, hc, hn⟩
    exact Set.mem_iUnion.mpr
      ⟨t, (typedStoppedClassEvent_iff K C t w).mpr
        ⟨t, le_rfl, hc, hn⟩⟩

/-- No finite rational table is trusted as a path law: this equals the
EXACT probability of the finite stopped event on the genuine typed
infinite-path measure, for every rational stochastic matrix and horizon. -/
theorem typedStoppedClassEvent_real_eq_rational {n : ℕ}
    (K : RationalMarkovMatrix n) (C : Finset (Fin n))
    (x : Fin n) (T : ℕ) :
    ((realizedModel K).pathLaw (Measure.dirac (decode x))).real
      (typedStoppedClassEvent K C T) =
      (stoppedClassHit K C T x : ℝ) := by
  have hpref :
      ((realizedModel K).pathLaw (Measure.dirac (decode x))).map
          (Preorder.frestrictLe T) =
        PermanssonLean.ProbabilitySupport.finitePrefixLaw
          (realizedModel K).inducedKernel (decode x) T := by
    rw [PermanssonResearch.MultipleLimit.FiniteCanonicalPath.typed_pathLaw_eq_canonical]
    exact PermanssonResearch.MultipleLimit.FiniteCanonicalPath.canonicalPathLaw_prefix_dirac
      (realizedModel K).inducedKernel (decode x) T
  unfold typedStoppedClassEvent Measure.real
  rw [← Measure.map_apply (Preorder.measurable_frestrictLe T)
      (measurableSet_successPrefixEvent
        (typedTarget (classFirstTarget K C)) T)]
  rw [hpref]
  change hittingValue (typedTarget (classFirstTarget K C))
    (realizedModel K).inducedKernel (decode x) T =
      (stoppedClassHit K C T x : ℝ)
  rw [stoppedClassHit_eq_D0 K C T x]
  exact typedHittingValue_eq_rational_all_horizons
    K (classFirstTarget K C) x T

end
end C10
end ReverseSolver
end PermanssonResearch