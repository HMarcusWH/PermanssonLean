import PermanssonResearch.ReverseSolver.RationalGraphCompleteness
import PermanssonResearch.ReverseSolver.RationalTypedSupportBridge
import PermanssonResearch.MultipleLimit.RecurrentClassDecomposition
import Mathlib.Tactic

/-!
# C10 — computed rational BSCCs equal genuine canonical recurrent classes

Every computed bottom class denotes exactly one full communicating class
of the genuine D0 action-selection intervention's induced Markov kernel,
and every native recurrent class appears. Comparison is made on the exact
joint-state encoding and on strictly positive singleton transitions.
No finite absorption probability or causal claim follows from this alone.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

open PermanssonLean
open FiniteStrategicRealization
open RationalTypedSupportBridge
open PermanssonResearch.MultipleLimit.KernelCommunication
open PermanssonResearch.MultipleLimit.RecurrentClassDecomposition

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- Every computed mutual-support component is the exact native
communicating class on the D0-realized typed joint state. -/
theorem component_native_iff {n : ℕ}
    (baseline L : RationalMarkovMatrix n) (x z : Fin n) :
    z ∈ component L x ↔
      decode z ∈ CommunicatingClass
        (rationalStrategicIntervention baseline L).intervention.apply.inducedKernel
        (decode x) := by
  let K := (rationalStrategicIntervention baseline L).intervention.apply.inducedKernel
  simp only [component, Finset.mem_filter, Finset.mem_univ, true_and]
  change communicatesB L x z = true ↔ Communicates K (decode x) (decode z)
  constructor
  · intro h
    obtain ⟨ha, hb⟩ := (andB_eq_true_iff _ _).mp h
    exact ⟨(rationalTyped_reachable_iff baseline L x z).mp
        ((reachesB_iff_rationalReachable L x z).mp ha),
      (rationalTyped_reachable_iff baseline L z x).mp
        ((reachesB_iff_rationalReachable L z x).mp hb)⟩
  · intro h
    apply (andB_eq_true_iff _ _).mpr
    exact ⟨(reachesB_iff_rationalReachable L x z).mpr
        ((rationalTyped_reachable_iff baseline L x z).mpr h.1),
      (reachesB_iff_rationalReachable L z x).mpr
        ((rationalTyped_reachable_iff baseline L z x).mpr h.2)⟩

/-- The numerical state-comparison set transported to an actual
joint-state Borel set without adding unreachable decorative states. -/
def decodedClass {n : ℕ}
    (C : Finset (Fin n)) : Set (JointState Unit (Fin n)) :=
  {y | encode y ∈ C}

theorem decodedClass_component_eq_native {n : ℕ}
    (baseline L : RationalMarkovMatrix n) (x : Fin n) :
    decodedClass (component L x) =
      CommunicatingClass
        (rationalStrategicIntervention baseline L).intervention.apply.inducedKernel
        (decode x) := by
  ext y
  rcases y with ⟨u, z⟩
  cases u
  exact component_native_iff baseline L x z

/-- This faithful encoding of finite physical subsets is injective. -/
theorem decodedClass_injective {n : ℕ}
    {C D : Finset (Fin n)} (h : decodedClass C = decodedClass D) :
    C = D := by
  apply Finset.ext
  intro x
  have hx := congrArg
    (fun S : Set (JointState Unit (Fin n)) => decode x ∈ S) h
  simpa [decodedClass, encode, decode] using hx

/-- Rational no-outgoing-edges iff genuine kernel closedness, with
both directions transported through the typed singleton atom iff. -/
theorem closedB_native_iff {n : ℕ}
    (baseline L : RationalMarkovMatrix n) (x : Fin n) :
    closedB L (component L x) = true ↔
      ClosedSubset
        (rationalStrategicIntervention baseline L).intervention.apply.inducedKernel
        (CommunicatingClass
          (rationalStrategicIntervention baseline L).intervention.apply.inducedKernel
          (decode x)) := by
  let K := (rationalStrategicIntervention baseline L).intervention.apply.inducedKernel
  constructor
  · intro h y hy z hz
    rcases y with ⟨u,i⟩
    cases u
    rcases z with ⟨v,j⟩
    cases v
    have hi : i ∈ component L x :=
      (component_native_iff baseline L x i).mpr hy
    have hp : 0 < L.entry i j :=
      (rationalTyped_positiveEdge_iff baseline L i j).mp hz
    have hclosed : ∀ a ∈ component L x,
        ∀ b : Fin n, 0 < L.entry a b → b ∈ component L x := by
      simpa [closedB] using h
    exact (component_native_iff baseline L x j).mp
      (hclosed i hi j hp)
  · intro h
    have hlogic : ∀ i ∈ component L x,
        ∀ j : Fin n, 0 < L.entry i j → j ∈ component L x := by
      intro i hi j hp
      have hy := (component_native_iff baseline L x i).mp hi
      have hz : PositiveEdge K (decode i) (decode j) :=
        (rationalTyped_positiveEdge_iff baseline L i j).mpr hp
      exact (component_native_iff baseline L x j).mpr
        (h (decode i) hy (decode j) hz)
    simpa [closedB] using hlogic

/-- Nonempty computed components are never a source of vacuous
bottom-class certificates. -/
theorem component_nonempty {n : ℕ}
    (baseline L : RationalMarkovMatrix n) (x : Fin n) :
    (component L x).Nonempty := by
  refine ⟨x, ?_⟩
  exact (component_native_iff baseline L x x).mpr
    (mem_communicatingClass
      (rationalStrategicIntervention baseline L).intervention.apply.inducedKernel
      (decode x))

/-- Class-membership equivalence on every representative state. -/
theorem bottom_component_iff_native_recurrent {n : ℕ}
    (baseline L : RationalMarkovMatrix n) (x : Fin n) :
    component L x ∈ bottomClasses L ↔
      IsRecurrentState
        (rationalStrategicIntervention baseline L).intervention.apply.inducedKernel
        (decode x) := by
  constructor
  · intro hc
    have hh := (Finset.mem_filter.mp hc).2.2
    exact (closedB_native_iff baseline L x).mp hh
  · intro h
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
    · exact ⟨component_nonempty baseline L x,
        (closedB_native_iff baseline L x).mpr h⟩

/-- Full completeness of computed bottom classes against the ACTUAL
native finite canonical recurrent-class collection, not just closure
of the output entries or positivity along discovered paths. -/
theorem bottomClasses_native_iff {n : ℕ}
    (baseline L : RationalMarkovMatrix n)
    (C : Finset (Fin n)) :
    C ∈ bottomClasses L ↔
      decodedClass C ∈ RecurrentClasses
        (rationalStrategicIntervention baseline L).intervention.apply.inducedKernel := by
  let K := (rationalStrategicIntervention baseline L).intervention.apply.inducedKernel
  constructor
  · intro h
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h).1
    subst C
    exact (recurrentClasses_mem_iff K _).mpr
      ⟨decode x,
        (bottom_component_iff_native_recurrent baseline L x).mp h,
        (decodedClass_component_eq_native baseline L x).symm⟩
  · intro h
    obtain ⟨y, hy, hclass⟩ := (recurrentClasses_mem_iff K _).mp h
    rcases y with ⟨u, x⟩
    cases u
    have hEq : component L x = C := decodedClass_injective
      ((decodedClass_component_eq_native baseline L x).trans hclass)
    rw [← hEq]
    exact (bottom_component_iff_native_recurrent baseline L x).mpr hy

end C10
end ReverseSolver
end PermanssonResearch