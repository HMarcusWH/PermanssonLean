import PermanssonResearch.ReverseSolver.RationalBSCCNative
import PermanssonResearch.ReverseSolver.RationalAbsorptionSolve
import PermanssonResearch.ReverseSolver.RationalDirichletUniqueness
import PermanssonResearch.MultipleLimit.RecurrentClassDecomposition
import Mathlib.Tactic

/-!
# C10 — discharge the non-vacuous recurrent-boundary access gate

Via the exact D0 positive-atom/graph transport and C2 generic finite
recurrent-class theorem, every state of a rational stochastic matrix can
reach some member of its *computed* BSCC union. This discharges the
access premise of the rational Dirichlet maximum principle. The theorem
uses the source-specific D0 typed realization, not an external factorization
or an assumed generic Markov chain's rational entries.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

open PermanssonLean
open RationalTypedSupportBridge
open FiniteStrategicRealization
open PermanssonResearch.MultipleLimit.KernelCommunication
open PermanssonResearch.MultipleLimit.RecurrentClassDecomposition
attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- Computed membership in the BSCC union iff membership in the genuine
native typed kernel's recurrent states, no representative identification. -/
theorem rational_recurrentUnion_native_iff {n : ℕ}
    (baseline L : RationalMarkovMatrix n) (x : Fin n) :
    x ∈ rationalRecurrentUnion L ↔
      decode x ∈ RecurrentStates
        (rationalStrategicIntervention baseline L).intervention.apply.inducedKernel := by
  let K := (rationalStrategicIntervention baseline L).intervention.apply.inducedKernel
  constructor
  · intro hx
    obtain ⟨C, hC, hxC⟩ := (Finset.mem_biUnion).mp hx
    have hCnative : decodedClass C ∈ RecurrentClasses K :=
      (bottomClasses_native_iff baseline L C).mp hC
    have hxnative : decode x ∈ decodedClass C := by
      simpa [decodedClass] using hxC
    exact (recurrentStates_iff_mem_recurrentClass K (decode x)).mpr
      ⟨decodedClass C, hCnative, hxnative⟩
  · intro hx
    obtain ⟨C, hC, hxC⟩ :=
      (recurrentStates_iff_mem_recurrentClass K (decode x)).mp hx
    obtain ⟨y, hy, heq⟩ := (recurrentClasses_mem_iff K C).mp hC
    rcases y with ⟨u, z⟩
    cases u
    have hz : IsRecurrentState K (decode z) := by
      simpa only [decode] using hy
    have hD : component L z ∈ bottomClasses L :=
      (bottom_component_iff_native_recurrent baseline L z).mpr hz
    have hEq : decodedClass (component L z) = C :=
      (decodedClass_component_eq_native baseline L z).trans heq
    have hxD : x ∈ component L z := by
      have hmem : decode x ∈ decodedClass (component L z) := by
        rw [hEq]
        exact hxC
      simpa [decodedClass] using hmem
    exact (Finset.mem_biUnion).mpr ⟨component L z, hD, hxD⟩

/-- C2's proven reachable closed recurrent class is represented exactly
by a computed rational BSCC, hence the maximum-principle hypothesis holds. -/
theorem every_state_reaches_rational_recurrent {n : ℕ} [NeZero n]
    (L : RationalMarkovMatrix n) (x : Fin n) :
    ∃ z ∈ rationalRecurrentUnion L, RationalReachable L x z := by
  let K := (rationalStrategicIntervention L L).intervention.apply.inducedKernel
  obtain ⟨y, hy, hpath⟩ := exists_reachable_recurrent_state K (decode x)
  refine ⟨encode y, ?_, ?_⟩
  · apply (rational_recurrentUnion_native_iff L L (encode y)).mpr
    simpa only [decode_encode] using hy
  · apply (rationalTyped_reachable_iff L L x (encode y)).mpr
    simpa only [decode_encode] using hpath

/-- Universal uniqueness of each finite rational class-absorption
Dirichlet system for the truly computed BSCC union. -/
theorem rationalBSCC_dirichlet_unique {n : ℕ} [NeZero n]
    (L : RationalMarkovMatrix n) (f g : Fin n → ℚ)
    (hfB : ∀ x ∈ rationalRecurrentUnion L, f x = g x)
    (hfH : ∀ x ∉ rationalRecurrentUnion L,
      f x = ∑ z : Fin n, L.entry x z * f z)
    (hgH : ∀ x ∉ rationalRecurrentUnion L,
      g x = ∑ z : Fin n, L.entry x z * g z) :
    f = g := by
  exact harmonic_solution_unique_of_boundary_access L
    (rationalRecurrentUnion L)
    (every_state_reaches_rational_recurrent L) f g hfB hfH hgH

end C10
end ReverseSolver
end PermanssonResearch