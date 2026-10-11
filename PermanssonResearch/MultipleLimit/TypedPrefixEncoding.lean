import PermanssonResearch.MultipleLimit.TypedStrategicWitness
import PermanssonResearch.ReverseSolver.GenericFinitePrefixAtoms
import Mathlib.Tactic

/-!
# Lane C1 — exact measurable coding for the literal Bool × Bool witness

The physically typed states and independently certified rational indices are
equivalent, both pointwise and on genuine finite prefixes. This file provides
only deterministic measurable encodings, with no assumed path-law equality.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit
namespace TypedPrefixEncoding

open TypedStrategicWitness

/-- Coordinatewise coding of a genuine typed trajectory prefix. -/
def prefixCode (T : ℕ) :
    ((i : Finset.Iic T) → Y) → ((i : Finset.Iic T) → Fin 4) :=
  fun w i => codeState (w i)

/-- Coordinatewise decoding of the rational indexed prefix. -/
def prefixDecode (T : ℕ) :
    ((i : Finset.Iic T) → Fin 4) → ((i : Finset.Iic T) → Y) :=
  fun w i => decodeState (w i)

@[simp] theorem prefixCode_prefixDecode (T : ℕ)
    (w : (i : Finset.Iic T) → Fin 4) :
    prefixCode T (prefixDecode T w) = w := by
  funext i
  exact codeState_decodeState (w i)

@[simp] theorem prefixDecode_prefixCode (T : ℕ)
    (w : (i : Finset.Iic T) → Y) :
    prefixDecode T (prefixCode T w) = w := by
  funext i
  exact decodeState_codeState (w i)

theorem measurable_prefixCode (T : ℕ) :
    Measurable (prefixCode T) := by
  refine Measurable.of_eval fun i => ?_
  exact (Measurable.of_discrete).comp (measurable_pi_apply i)

theorem measurable_prefixDecode (T : ℕ) :
    Measurable (prefixDecode T) := by
  refine Measurable.of_eval fun i => ?_
  exact (Measurable.of_discrete).comp (measurable_pi_apply i)

/-- Full singleton fibres follow from the proven inverse map, not a
presumed correspondence between the two probability measures. -/
theorem prefixCode_preimage_singleton (T : ℕ)
    (v : (i : Finset.Iic T) → Fin 4) :
    prefixCode T ⁻¹' {v} = {prefixDecode T v} := by
  ext w
  change prefixCode T w = v ↔ w = prefixDecode T v
  constructor
  · intro h
    calc
      w = prefixDecode T (prefixCode T w) :=
        (prefixDecode_prefixCode T w).symm
      _ = prefixDecode T v := congrArg _ h
  · intro h
    rw [h, prefixCode_prefixDecode]

/-- Encoding the deterministic time-zero history preserves its sole state. -/
theorem prefixCode_zero (y : Y) :
    prefixCode 0 (PermanssonLean.ProbabilitySupport.singletonPrefix y) =
      PermanssonLean.ProbabilitySupport.singletonPrefix (codeState y) := rfl

/-- The same bijection on entire paths, used after lifting finite-prefix
correspondence to the canonical infinite Ionescu–Tulcea law. -/
def pathCode : (ℕ → Y) → (ℕ → Fin 4) :=
  fun w n => codeState (w n)

def pathDecode : (ℕ → Fin 4) → (ℕ → Y) :=
  fun w n => decodeState (w n)

@[simp] theorem pathCode_pathDecode (w : ℕ → Fin 4) :
    pathCode (pathDecode w) = w := by
  funext n
  exact codeState_decodeState (w n)

@[simp] theorem pathDecode_pathCode (w : ℕ → Y) :
    pathDecode (pathCode w) = w := by
  funext n
  exact decodeState_codeState (w n)

theorem measurable_pathCode : Measurable pathCode := by
  refine Measurable.of_eval fun n => ?_
  exact (Measurable.of_discrete).comp (measurable_pi_apply n)

theorem measurable_pathDecode : Measurable pathDecode := by
  refine Measurable.of_eval fun n => ?_
  exact (Measurable.of_discrete).comp (measurable_pi_apply n)

end TypedPrefixEncoding
end MultipleLimit
end PermanssonResearch
