import PermanssonResearch.ReverseSolver.HistoryTypedAtoms
import PermanssonResearch.ReverseSolver.FiniteStrategicPathBridge
import Mathlib.Tactic

/-!
# D1-C2: equality of complete typed and rational HISTORY-CONDITIONED prefix laws

The atom proof is driven by two INDEPENDENT genuine Mathlib partialTraj
laws. At each step it uses the ACTUAL alpha -> P -> U induced kernel
of the selected feedbackModel, with P/U held fixed. Exact equality of
all typed/rational atoms is lifted to an equality of probability MEASURES
on the complete finite history space.

This is not a statement about the ordinary stationary pathLaw of one
frozen intervention.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace HistoryDependentTyped

open Bellman
open ControlledKernel
open FiniteStrategicRealization
open FiniteStrategicPathBridge
open PermanssonLean
open PermanssonLean.ProbabilitySupport

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov
universe uC

/-- For EVERY original deadline D and observed prefix length t, every
typed strategic-world path atom at the decoded history has exactly the
rational D1-C1 history-conditioned path probability. -/
theorem typed_prefix_atom_transport
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D : ℕ) (x : Fin n) :
    ∀ (t : ℕ) (v : (i : Finset.Iic t) → Fin n),
      typedPrefixLaw sys σ D x t {prefixDecode t v} =
        HistoryDependent.prefixLaw sys σ D x t {v} := by
  intro t
  induction t with
  | zero =>
      intro v
      rw [typedPrefixLaw_zero, HistoryDependent.prefixLaw_zero]
      rw [Measure.dirac_apply' _ (measurableSet_singleton (prefixDecode 0 v))]
      rw [Measure.dirac_apply' _ (measurableSet_singleton v)]
      have hinit :
          prefixDecode 0 v = singletonPrefix (decode x) ↔
            v = singletonPrefix x := by
        constructor
        · intro h
          have hp := congrArg (prefixEncode 0) h
          have hconst : prefixEncode 0 (singletonPrefix (decode x)) =
              singletonPrefix x := by
            funext i
            rfl
          simpa only [prefixEncode_prefixDecode, hconst] using hp
        · intro h
          subst v
          funext i
          rfl
      by_cases h : v = singletonPrefix x
      · have ht : singletonPrefix (decode x) = prefixDecode 0 v :=
          (hinit.mpr h).symm
        simp [h, ht]
      · have ht : singletonPrefix (decode x) ≠ prefixDecode 0 v := by
          intro hh
          exact h (hinit.mp hh.symm)
        simp [h, ht]
  | succ t ih =>
      intro v
      let vpre := Preorder.frestrictLe₂
        (π := fun _ : ℕ => Fin n) t.le_succ v
      rw [typed_prefix_singleton_succ sys σ D x t (prefixDecode (t+1) v)]
      rw [HistoryDependent.prefix_singleton_succ sys σ D x t v]
      have hstep :
          typedHistoryStep sys σ D t (prefixDecode t vpre)
            {decode (v ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩)} =
          ENNReal.ofReal (HistoryDependent.selectedEntry sys σ D t vpre
            (v ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩) : ℝ) := by
        simpa only [prefixEncode_prefixDecode] using
          (typedHistoryStep_decode_singleton sys σ D t
            (prefixDecode t vpre)
            (v ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩))
      change
        typedPrefixLaw sys σ D x t {prefixDecode t vpre} *
          typedHistoryStep sys σ D t (prefixDecode t vpre)
            {decode (v ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩)} =
        HistoryDependent.prefixLaw sys σ D x t {vpre} *
          ENNReal.ofReal (HistoryDependent.selectedEntry sys σ D t vpre
            (v ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩) : ℝ)
      rw [ih vpre, hstep]

/-- Full, all-measurable-event equality of the pushforward of the true typed
history-dependent strategic-world law and the genuine D1-C1 rational law. -/
theorem typed_prefixLaw_map
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D : ℕ) (x : Fin n) (t : ℕ) :
    (typedPrefixLaw sys σ D x t).map (prefixEncode t) =
      HistoryDependent.prefixLaw sys σ D x t := by
  classical
  let mu := typedPrefixLaw sys σ D x t
  let nu := HistoryDependent.prefixLaw sys σ D x t
  let f := prefixEncode (n := n) t
  have hf : Measurable f := measurable_prefixEncode t
  have hmass (v : (i : Finset.Iic t) → Fin n) :
      (mu.map f) {v} = nu {v} := by
    rw [Measure.map_apply hf (measurableSet_singleton v)]
    rw [prefixEncode_preimage_singleton]
    exact typed_prefix_atom_transport sys σ D x t v
  ext E hE
  have hfilter :
      (↑(Finset.univ.filter
        (fun w : ((i : Finset.Iic t) → Fin n) => w ∈ E)) :
          Set ((i : Finset.Iic t) → Fin n)) = E := by
    ext w
    simp
  change (mu.map f) E = nu E
  calc
    (mu.map f) E =
        (mu.map f) (↑(Finset.univ.filter
          (fun w : ((i : Finset.Iic t) → Fin n) => w ∈ E)) :
            Set ((i : Finset.Iic t) → Fin n)) := by rw [hfilter]
    _ = ∑ w ∈ Finset.univ.filter
          (fun w : ((i : Finset.Iic t) → Fin n) => w ∈ E),
          (mu.map f) {w} := by
            rw [sum_measure_singleton]
    _ = ∑ w ∈ Finset.univ.filter
          (fun w : ((i : Finset.Iic t) → Fin n) => w ∈ E),
          nu {w} := by
            apply Finset.sum_congr rfl
            intro w _
            exact hmass w
    _ = nu E := by
          have hsum : nu (↑(Finset.univ.filter
              (fun w : ((i : Finset.Iic t) → Fin n) => w ∈ E)) :
                Set ((i : Finset.Iic t) → Fin n)) =
              ∑ w ∈ Finset.univ.filter
                (fun w : ((i : Finset.Iic t) → Fin n) => w ∈ E),
                nu {w} := by
            rw [sum_measure_singleton]
          exact hsum.symm.trans (congrArg nu hfilter)

end HistoryDependentTyped
end ReverseSolver
end PermanssonResearch
