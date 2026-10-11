import PermanssonResearch.MultipleLimit.TypedPrefixEncoding
import PermanssonResearch.ReverseSolver.FiniteStrategicPathBridge
import Mathlib.Tactic

/-!
# Lane C1 — typed four-state finite-prefix path-measure correspondence

We transport the actual alpha/P/U induced kernel, not the distinct
Unit × Fin n realization in D0-E. The proof uses the genuine canonical
partial-trajectory recurrence for every horizon and every path atom.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace TypedPrefixTransport

open TypedStrategicWitness TypedPrefixEncoding
open PermanssonResearch.ReverseSolver
open PermanssonResearch.ReverseSolver.FiniteStrategicPathBridge
  (finitePrefixLaw_singleton_succ)
open PermanssonLean.ProbabilitySupport

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

/-- Every finite path atom of the literal typed alpha/P/U process has the
same probability as its encoded rational counterpart, at every horizon. -/
theorem typed_prefix_atom (x : Fin 4) :
    ∀ (T : ℕ) (v : (i : Finset.Iic T) → Fin 4),
      finitePrefixLaw model.inducedKernel (decodeState x) T
        {prefixDecode T v} =
      finitePrefixLaw
        (rationalFiniteKernel ExactRationalAbsorption.fourStateMatrix)
        x T {v} := by
  intro T
  induction T with
  | zero =>
      intro v
      unfold finitePrefixLaw
      rw [Kernel.partialTraj_self, Kernel.id_apply,
        Kernel.partialTraj_self, Kernel.id_apply]
      rw [Measure.dirac_apply' _
        (measurableSet_singleton (prefixDecode 0 v))]
      rw [Measure.dirac_apply' _ (measurableSet_singleton v)]
      have hinit :
          prefixDecode 0 v = singletonPrefix (decodeState x) ↔
            v = singletonPrefix x := by
        constructor
        · intro h
          have hp := congrArg (prefixCode 0) h
          have hc : prefixCode 0 (singletonPrefix (decodeState x)) =
              singletonPrefix x := by
            funext i
            exact codeState_decodeState x
          simpa only [prefixCode_prefixDecode, hc] using hp
        · intro h
          subst v
          funext i
          rfl
      by_cases h : v = singletonPrefix x
      · have ht : singletonPrefix (decodeState x) =
            prefixDecode 0 v := (hinit.mpr h).symm
        simp [h, ht]
      · have ht : singletonPrefix (decodeState x) ≠
            prefixDecode 0 v := by
          intro hh
          exact h (hinit.mp hh.symm)
        simp [h, ht]
  | succ T ih =>
      intro v
      let vpre := Preorder.frestrictLe₂
        (π := fun _ : ℕ => Fin 4) T.le_succ v
      have hpoint : MeasurableSet
          ({Preorder.frestrictLe₂ (π := fun _ : ℕ => Y)
            T.le_succ (prefixDecode (T+1) v)} :
            Set ((i : Finset.Iic T) → Y)) :=
        measurableSet_singleton _
      have hlast : MeasurableSet
          ({(prefixDecode (T+1) v)
            ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩} : Set Y) :=
        measurableSet_singleton _
      have hwhole : MeasurableSet
          ({prefixDecode (T+1) v} :
            Set ((i : Finset.Iic (T+1)) → Y)) :=
        measurableSet_singleton _
      rw [finitePrefixLaw_singleton_succ
        model.inducedKernel (decodeState x) T
        (prefixDecode (T+1) v) hpoint hlast hwhole]
      rw [rationalFiniteKernel_prefix_singleton_succ
        ExactRationalAbsorption.fourStateMatrix x T v]
      rw [← rationalFiniteKernel_singleton
        ExactRationalAbsorption.fourStateMatrix
        (v ⟨T, Finset.mem_Iic.mpr T.le_succ⟩)
        (v ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩)]
      have hstep :
          model.inducedKernel
            (decodeState (v ⟨T, Finset.mem_Iic.mpr T.le_succ⟩))
            {decodeState (v ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩)} =
          rationalFiniteKernel ExactRationalAbsorption.fourStateMatrix
            (v ⟨T, Finset.mem_Iic.mpr T.le_succ⟩)
            {v ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩} := by
        rw [rationalFiniteKernel_singleton]
        simpa only [codeState_decodeState] using
          (inducedKernel_atom_entry
            (decodeState (v ⟨T, Finset.mem_Iic.mpr T.le_succ⟩))
            (decodeState (v ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩)))
      change
        finitePrefixLaw model.inducedKernel (decodeState x) T
          {prefixDecode T vpre} *
        model.inducedKernel
          (decodeState (v ⟨T, Finset.mem_Iic.mpr T.le_succ⟩))
          {decodeState (v ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩)} =
        finitePrefixLaw
          (rationalFiniteKernel ExactRationalAbsorption.fourStateMatrix)
          x T {vpre} *
        rationalFiniteKernel ExactRationalAbsorption.fourStateMatrix
          (v ⟨T, Finset.mem_Iic.mpr T.le_succ⟩)
          {v ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩}
      rw [ih vpre, hstep]

/-- Equality of complete finite-prefix measures, not only endpoint marginals
or the individual numerical transition probabilities. -/
theorem typed_prefixLaw_map_index (x : Fin 4) (T : ℕ) :
    (finitePrefixLaw model.inducedKernel (decodeState x) T).map
      (prefixCode T) =
    finitePrefixLaw
      (rationalFiniteKernel ExactRationalAbsorption.fourStateMatrix)
      x T := by
  apply Measure.ext_of_singleton
  intro v
  rw [Measure.map_apply (measurable_prefixCode T) (measurableSet_singleton v)]
  rw [prefixCode_preimage_singleton]
  exact typed_prefix_atom x T v

/-- Version indexed by the actual typed physical initial state. -/
theorem typed_prefixLaw_map (y : Y) (T : ℕ) :
    (finitePrefixLaw model.inducedKernel y T).map
      (prefixCode T) =
    finitePrefixLaw
      (rationalFiniteKernel ExactRationalAbsorption.fourStateMatrix)
      (codeState y) T := by
  simpa only [decodeState_codeState] using
    typed_prefixLaw_map_index (codeState y) T

end
end TypedPrefixTransport
end MultipleLimit
end PermanssonResearch
