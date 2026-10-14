import PermanssonResearch.ReverseSolver.TypedStoppedClassLimit
import PermanssonResearch.ReverseSolver.RationalRecurrentAccess
import PermanssonResearch.MultipleLimit.CanonicalClassEntry
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# C10 — vanish of exact rational unabsorbed mass in the true path law

The original D0 typed strategic-world path hits the *native* recurrent
union almost surely by C2. Its decoded recurrent union is exactly the
computed rational one, so the independently certified finite-horizon
survival fraction must tend to zero, without a simulated horizon cutoff.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false
set_option maxHeartbeats 0

open FiniteStrategicRealization
open PermanssonResearch.MultipleLimit.FiniteCanonicalPath
open PermanssonResearch.MultipleLimit.CanonicalClassEntry
open PermanssonResearch.MultipleLimit.RecurrentClassDecomposition

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

/-- The full computed recurrent union is the goal and has no forbidden
member. Almost-sure physical eventual recurrence therefore makes the
union over finite stopped events a measure-one infinite path event. -/
theorem typedStoppedRecurrent_ae {n : ℕ} [NeZero n]
    (K : RationalMarkovMatrix n) (x : Fin n) :
    ∀ᵐ w ∂(realizedModel K).pathLaw (Measure.dirac (decode x)),
      w ∈ ⋃ T : ℕ,
        typedStoppedClassEvent K (rationalRecurrentUnion K) T := by
  have h := canonical_ae_enters_recurrent
    (realizedModel K).inducedKernel (diracProba (decode x))
  change ∀ᵐ w ∂(realizedModel K).pathLaw (Measure.dirac (decode x)),
      ∃ t : ℕ, w t ∈ RecurrentStates (realizedModel K).inducedKernel at h
  filter_upwards [h] with w hw
  obtain ⟨t, ht⟩ := hw
  rw [typedStoppedClassEvent_iUnion]
  refine ⟨t, ?_, ?_⟩
  · have hRec : decode (encode (w t)) ∈
        RecurrentStates
          (rationalStrategicIntervention K K).intervention.apply.inducedKernel := by
      simpa [rationalStrategicIntervention_applied, decode_encode] using ht
    exact (rational_recurrentUnion_native_iff K K (encode (w t))).mpr hRec
  · intro s hs hbad
    have hcontra := (Finset.mem_sdiff.mp hbad).2
    exact hcontra ((Finset.mem_sdiff.mp hbad).1)

/-- Native a.s. recurrence gives a genuine probability-one infinite event
for the same stopped-prefix observation used in the rational solver. -/
theorem typedStoppedRecurrent_probability_one {n : ℕ} [NeZero n]
    (K : RationalMarkovMatrix n) (x : Fin n) :
    (realizedModel K).pathLaw (Measure.dirac (decode x))
      (⋃ T : ℕ,
        typedStoppedClassEvent K (rationalRecurrentUnion K) T) = 1 := by
  let P := (realizedModel K).pathLaw (Measure.dirac (decode x))
  have hAE := typedStoppedRecurrent_ae K x
  rw [ae_iff] at hAE
  have hset : MeasurableSet
      (⋃ T : ℕ, typedStoppedClassEvent K (rationalRecurrentUnion K) T) :=
    MeasurableSet.iUnion (typedStoppedClassEvent_measurable K _)
  have hsum := measure_add_measure_compl hset (μ := P)
  change P (⋃ T : ℕ,
    typedStoppedClassEvent K (rationalRecurrentUnion K) T)ᶜ = 0 at hAE
  rw [hAE] at hsum
  simpa using hsum

/-- Exact rational partition at each stopped horizon: either a recurrent
state has already been encountered or all observed states remain transient.
No almost-sure hypothesis is needed for this finite recursion identity. -/
theorem beforeRecurrent_add_stoppedUnion {n : ℕ}
    (K : RationalMarkovMatrix n) :
    ∀ T : ℕ, ∀ x : Fin n,
      beforeRecurrent K T x +
        stoppedClassHit K (rationalRecurrentUnion K) T x = 1 := by
  intro T
  induction T with
  | zero =>
      intro x
      by_cases hx : x ∈ rationalRecurrentUnion K
      · simp [beforeRecurrent, stoppedClassHit, hx]
      · simp [beforeRecurrent, stoppedClassHit, hx]
  | succ T ih =>
      intro x
      by_cases hx : x ∈ rationalRecurrentUnion K
      · simp [beforeRecurrent, stoppedClassHit, hx]
      · simp only [beforeRecurrent, stoppedClassHit, if_neg hx]
        change
          (∑ y : Fin n, K.entry x y * beforeRecurrent K T y) +
          (∑ y : Fin n,
            K.entry x y * stoppedClassHit K (rationalRecurrentUnion K) T y) = 1
        calc
          (∑ y : Fin n, K.entry x y * beforeRecurrent K T y) +
              (∑ y : Fin n,
                K.entry x y * stoppedClassHit K (rationalRecurrentUnion K) T y) =
            (∑ y : Fin n, K.entry x y *
              (beforeRecurrent K T y +
                stoppedClassHit K (rationalRecurrentUnion K) T y)) := by
                  simp only [mul_add, Finset.sum_add_distrib]
          _ = (∑ y : Fin n, K.entry x y) := by
            apply Finset.sum_congr rfl
            intro y _
            rw [ih y]
            ring
          _ = 1 := K.row_sum_one x

/-- The exact rational probability of still being transient tends to
zero on the genuine infinite typed path, without requiring a spectral
or numerical convergence rate. -/
theorem beforeRecurrent_tendsto_zero {n : ℕ} [NeZero n]
    (K : RationalMarkovMatrix n) (x : Fin n) :
    Tendsto (fun T : ℕ => (beforeRecurrent K T x : ℝ)) atTop (𝓝 0) := by
  have hlim :=
    typedStoppedClassEvent_real_tendsto K (rationalRecurrentUnion K) x
  have hunit := typedStoppedRecurrent_probability_one K x
  have hlim1 : Tendsto
      (fun T : ℕ => (stoppedClassHit K (rationalRecurrentUnion K) T x : ℝ))
      atTop (𝓝 1) := by
    simpa [Measure.real, hunit] using hlim
  have hOne : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hdiff := hOne.sub hlim1
  have heq (T : ℕ) :
      (beforeRecurrent K T x : ℝ) =
        1 - (stoppedClassHit K (rationalRecurrentUnion K) T x : ℝ) := by
    have h := congrArg (fun v : ℚ => (v : ℝ))
      (beforeRecurrent_add_stoppedUnion K T x)
    push_cast at h
    linarith
  simpa only [heq, sub_self] using hdiff

end
end C10
end ReverseSolver
end PermanssonResearch