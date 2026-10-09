import PermanssonResearch.ReverseSolver.GenericFinitePrefixAtoms
import PermanssonResearch.ReverseSolver.CanonicalAllHorizonCorrespondence
import Mathlib.Tactic

/-!
# D0-E: exact all-horizon transport from rational matrices to typed alpha/P/U

The encoding Unit × Fin n ≃ Fin n is an actual measurable bijection. This
module transports ALL finite-prefix path atoms, then the entire canonical
Ionescu--Tulcea finite-prefix measure and target-before-forbidden events.
No equality of model hitting values is postulated.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace FiniteStrategicPathBridge

open FiniteStrategicRealization
open PermanssonLean
open PermanssonLean.ProbabilitySupport

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

def prefixEncode {n : ℕ} (T : ℕ) :
    ((i : Finset.Iic T) → JointState Unit (Fin n)) →
      ((i : Finset.Iic T) → Fin n) :=
  fun w i => encode (w i)

def prefixDecode {n : ℕ} (T : ℕ) :
    ((i : Finset.Iic T) → Fin n) →
      ((i : Finset.Iic T) → JointState Unit (Fin n)) :=
  fun w i => decode (w i)

@[simp] theorem prefixEncode_prefixDecode {n : ℕ}
    (T : ℕ) (w : (i : Finset.Iic T) → Fin n) :
    prefixEncode T (prefixDecode T w) = w := by
  funext i
  exact encode_decode (w i)

@[simp] theorem prefixDecode_prefixEncode {n : ℕ}
    (T : ℕ) (w : (i : Finset.Iic T) → JointState Unit (Fin n)) :
    prefixDecode T (prefixEncode T w) = w := by
  funext i
  exact decode_encode (w i)

theorem measurable_prefixEncode {n : ℕ} (T : ℕ) :
    Measurable (prefixEncode (n := n) T) := by
  refine Measurable.of_eval fun i => ?_
  exact measurable_snd.comp (measurable_pi_apply i)

theorem measurable_prefixDecode {n : ℕ} (T : ℕ) :
    Measurable (prefixDecode (n := n) T) := by
  refine Measurable.of_eval fun i => ?_
  exact (measurable_const.prodMk (measurable_pi_apply i))

theorem prefixEncode_preimage_singleton {n : ℕ} (T : ℕ)
    (w : (i : Finset.Iic T) → Fin n) :
    prefixEncode (n := n) T ⁻¹' {w} = {prefixDecode T w} := by
  ext v
  change prefixEncode T v = w ↔ v = prefixDecode T w
  constructor
  · intro h
    calc
      v = prefixDecode T (prefixEncode T v) := (prefixDecode_prefixEncode T v).symm
      _ = prefixDecode T w := congrArg _ h
  · intro h
    rw [h, prefixEncode_prefixDecode]

/-- All canonical trajectory atom probabilities transport across the genuine
finite strategic-world realization, at EVERY horizon and starting state. -/
theorem realized_prefix_atom {n : ℕ} (K : RationalMarkovMatrix n)
    (x : Fin n) :
    ∀ (T : ℕ) (v : (i : Finset.Iic T) → Fin n),
      finitePrefixLaw (realizedModel K).inducedKernel (decode x) T
        {prefixDecode T v} =
      finitePrefixLaw (rationalFiniteKernel K) x T {v} := by
  intro T
  induction T with
  | zero =>
      intro v
      rw [← finitePrefixLaw_zero_eq
        (realizedModel K).inducedKernel (realizedModel K).inducedKernel (decode x)]
      unfold finitePrefixLaw
      rw [Kernel.partialTraj_self, Kernel.id_apply,
        Kernel.partialTraj_self, Kernel.id_apply]
      rw [Measure.dirac_apply'
        _ (measurableSet_singleton (prefixDecode 0 v))]
      rw [Measure.dirac_apply'
        _ (measurableSet_singleton v)]
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
      · have ht : singletonPrefix (decode x) =
            prefixDecode 0 v := by
          exact (hinit.mpr h).symm
        simp [h, ht]
      · have ht : singletonPrefix (decode x) ≠
            prefixDecode 0 v := by
          intro hh
          exact h (hinit.mp hh.symm)
        simp [h, ht]
  | succ T ih =>
      intro v
      let vpre := Preorder.frestrictLe₂
        (π := fun _ : ℕ => Fin n) T.le_succ v
      have hpoint : MeasurableSet
          ({Preorder.frestrictLe₂ (π := fun _ : ℕ => JointState Unit (Fin n))
            T.le_succ (prefixDecode (T+1) v)} :
            Set ((i : Finset.Iic T) → JointState Unit (Fin n))) :=
        measurableSet_singleton _
      have hlast : MeasurableSet
          ({(prefixDecode (T+1) v)
            ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩} :
            Set (JointState Unit (Fin n))) :=
        measurableSet_singleton _
      have hwhole : MeasurableSet
          ({prefixDecode (T+1) v} :
            Set ((i : Finset.Iic (T+1)) → JointState Unit (Fin n))) :=
        measurableSet_singleton _
      rw [finitePrefixLaw_singleton_succ
        (realizedModel K).inducedKernel (decode x) T
        (prefixDecode (T+1) v) hpoint hlast hwhole]
      rw [rationalFiniteKernel_prefix_singleton_succ K x T v]
      have hstep :
          (realizedModel K).inducedKernel
            (decode (v ⟨T, Finset.mem_Iic.mpr T.le_succ⟩))
            {decode (v ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩)} =
          rationalFiniteKernel K
            (v ⟨T, Finset.mem_Iic.mpr T.le_succ⟩)
            {v ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩} := by
        have hs :
            (encode ⁻¹' ({v ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩} :
              Set (Fin n))) =
              {decode (v ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩)} := by
          ext p
          rcases p with ⟨u, z⟩
          cases u
          simp [encode, decode]
        rw [← hs]
        exact inducedKernel_worldCylinder K
          (v ⟨T, Finset.mem_Iic.mpr T.le_succ⟩)
          (measurableSet_singleton _)
      change
        finitePrefixLaw (realizedModel K).inducedKernel (decode x) T
          {prefixDecode T vpre} *
        (realizedModel K).inducedKernel
          (decode (v ⟨T, Finset.mem_Iic.mpr T.le_succ⟩))
          {decode (v ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩)} =
        finitePrefixLaw (rationalFiniteKernel K) x T {vpre} *
        rationalFiniteKernel K
          (v ⟨T, Finset.mem_Iic.mpr T.le_succ⟩)
          {v ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩}
      rw [ih vpre, hstep]

/-- Pushforward of the *actual* typed path law agrees with the rational
canonical path law, not merely with the same one-step transition table. -/
theorem realized_prefixLaw_map {n : ℕ} (K : RationalMarkovMatrix n)
    (x : Fin n) (T : ℕ) :
    (finitePrefixLaw (realizedModel K).inducedKernel (decode x) T).map
      (prefixEncode T) =
    finitePrefixLaw (rationalFiniteKernel K) x T := by
  classical
  let μ := finitePrefixLaw (realizedModel K).inducedKernel (decode x) T
  let ν := finitePrefixLaw (rationalFiniteKernel K) x T
  let f := prefixEncode (n := n) T
  have hf : Measurable f := measurable_prefixEncode T
  have hmass (v : (i : Finset.Iic T) → Fin n) :
      (μ.map f) {v} = ν {v} := by
    rw [Measure.map_apply hf (measurableSet_singleton v)]
    rw [prefixEncode_preimage_singleton]
    exact realized_prefix_atom K x T v
  ext E hE
  have hfilter :
      (↑(Finset.univ.filter
        (fun w : ((i : Finset.Iic T) → Fin n) => w ∈ E)) :
          Set ((i : Finset.Iic T) → Fin n)) = E := by
    ext w
    simp
  change (μ.map f) E = ν E
  calc
    (μ.map f) E =
        (μ.map f) (↑(Finset.univ.filter
          (fun w : ((i : Finset.Iic T) → Fin n) => w ∈ E)) :
            Set ((i : Finset.Iic T) → Fin n)) := by rw [hfilter]
    _ = ∑ w ∈ Finset.univ.filter
          (fun w : ((i : Finset.Iic T) → Fin n) => w ∈ E), (μ.map f) {w} := by
            rw [sum_measure_singleton]
    _ = ∑ w ∈ Finset.univ.filter
          (fun w : ((i : Finset.Iic T) → Fin n) => w ∈ E), ν {w} := by
            apply Finset.sum_congr rfl
            intro w _
            exact hmass w
    _ = ν E := by
          have hsum : ν (↑(Finset.univ.filter
              (fun w : ((i : Finset.Iic T) → Fin n) => w ∈ E)) :
                Set ((i : Finset.Iic T) → Fin n)) =
              ∑ w ∈ Finset.univ.filter
                (fun w : ((i : Finset.Iic T) → Fin n) => w ∈ E),
                ν {w} := by
            rw [sum_measure_singleton]
          exact hsum.symm.trans (congrArg ν hfilter)

def typedTarget {n : ℕ} (rt : RationalHittingTarget n) :
    FrozenHittingTarget (JointState Unit (Fin n)) where
  goal := encode ⁻¹' (rationalTargetAsFrozen rt).goal
  forbidden := encode ⁻¹' (rationalTargetAsFrozen rt).forbidden
  goal_measurable :=
    (rationalTargetAsFrozen rt).goal_measurable.preimage measurable_snd
  forbidden_measurable :=
    (rationalTargetAsFrozen rt).forbidden_measurable.preimage measurable_snd
  disjoint := by
    exact Set.disjoint_left.mpr (by
      intro y hy hz
      exact Set.disjoint_left.mp (rationalTargetAsFrozen rt).disjoint hy hz)

theorem prefixEncode_success_preimage {n : ℕ}
    (rt : RationalHittingTarget n) (T : ℕ) :
    prefixEncode (n := n) T ⁻¹'
      successPrefixEvent (rationalTargetAsFrozen rt) T =
      successPrefixEvent (typedTarget rt) T := by
  ext w
  simp [successPrefixEvent, typedTarget, prefixEncode]

/-- The missing substantive bridge: exact hitting values in the *genuine*
typed alpha/P/U model are exactly the rationals, for all n, T, x, targets. -/
theorem typedHittingValue_eq_rational_all_horizons {n : ℕ}
    (K : RationalMarkovMatrix n) (rt : RationalHittingTarget n)
    (x : Fin n) (T : ℕ) :
    hittingValue (typedTarget rt) (realizedModel K).inducedKernel
        (decode x) T =
      (rationalHittingValue K rt T x : ℝ) := by
  letI : IsMarkovKernel (realizedModel K).inducedKernel :=
    StrategicWorldModel.inducedKernel_isMarkov _
  unfold hittingValue
  change (finitePrefixLaw (realizedModel K).inducedKernel (decode x) T).real
    (successPrefixEvent (typedTarget rt) T) = _
  have hmap := realized_prefixLaw_map K x T
  have htarget := prefixEncode_success_preimage rt T
  have hv :
      (finitePrefixLaw (realizedModel K).inducedKernel (decode x) T).real
        (successPrefixEvent (typedTarget rt) T) =
      (finitePrefixLaw (rationalFiniteKernel K) x T).real
        (successPrefixEvent (rationalTargetAsFrozen rt) T) := by
    unfold Measure.real
    rw [← hmap]
    rw [Measure.map_apply (measurable_prefixEncode T)
      (measurableSet_successPrefixEvent (rationalTargetAsFrozen rt) T)]
    rw [htarget]
  rw [hv]
  exact (rationalHittingValue_eq_canonical_all_horizons K rt T x).symm

end
end FiniteStrategicPathBridge
end ReverseSolver
end PermanssonResearch
