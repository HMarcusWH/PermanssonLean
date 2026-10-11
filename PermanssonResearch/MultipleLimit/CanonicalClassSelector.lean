import PermanssonResearch.MultipleLimit.CanonicalRecurrentResidence
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Tactic

/-!
# Lane C2 — canonical measurable recurrent-class representative

This module constructs one fixed finite-class representative per communication
class, using the least recurrent hitting TIME of an actual infinite path.
It yields a total measurable selector and its complete finite atomic law,
for arbitrary initial probability measures and arbitrary finite Markov kernels.

No invariant class probability measures, occupation convergence or Exact GR
are assumed or claimed. The later class occupation theorem will push this
selector through its *proved* invariant-law assignment.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace CanonicalClassSelector

open KernelCommunication
open RecurrentClassDecomposition
open CanonicalRecurrentResidence
open CanonicalClassEntry
open CanonicalClassContinuation
open FiniteCanonicalPath

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [Nonempty Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- This is defined on ALL paths; its complement is canonical-null under
all initial laws by the already certified recurrent-entry theorem. -/
def HasRecurrentHit (w : ℕ → Y) : Prop :=
  ∃ n : ℕ, w n ∈ RecurrentStates K

private theorem recurrent_measurable :
    MeasurableSet (RecurrentStates K) :=
  (Set.toFinite (RecurrentStates K)).measurableSet

theorem hasRecurrentHit_measurable :
    MeasurableSet {w : ℕ → Y | HasRecurrentHit K w} := by
  have heq : {w : ℕ → Y | HasRecurrentHit K w} =
      ⋃ n : ℕ, (fun w : ℕ → Y => w n) ⁻¹' (RecurrentStates K) := by
    ext w
    simp [HasRecurrentHit]
  rw [heq]
  exact MeasurableSet.iUnion (fun n =>
    (recurrent_measurable K).preimage (measurable_pi_apply n))

/-- A total finite-search condition: use the first real recurrent hit
when one exists, and time zero ONLY on exceptional never-hit paths. -/
def EntryPredicate (w : ℕ → Y) (n : ℕ) : Prop :=
  w n ∈ RecurrentStates K ∨ (n = 0 ∧ ¬HasRecurrentHit K w)

theorem entryPredicate_exists (w : ℕ → Y) :
    ∃ n : ℕ, EntryPredicate K w n := by
  by_cases h : HasRecurrentHit K w
  · obtain ⟨n, hn⟩ := h
    exact ⟨n, Or.inl hn⟩
  · exact ⟨0, Or.inr ⟨rfl, h⟩⟩

theorem entryPredicate_measurable (n : ℕ) :
    MeasurableSet {w : ℕ → Y | EntryPredicate K w n} := by
  have hstate : MeasurableSet {w : ℕ → Y | w n ∈ RecurrentStates K} :=
    (recurrent_measurable K).preimage (measurable_pi_apply n)
  by_cases hn : n = 0
  · have heq :
        {w : ℕ → Y | EntryPredicate K w n} =
          {w : ℕ → Y | w n ∈ RecurrentStates K} ∪
            {w : ℕ → Y | ¬HasRecurrentHit K w} := by
      ext w
      simp [EntryPredicate, hn]
    rw [heq]
    exact hstate.union (hasRecurrentHit_measurable K).compl
  · have heq :
        {w : ℕ → Y | EntryPredicate K w n} =
          {w : ℕ → Y | w n ∈ RecurrentStates K} := by
      ext w
      simp [EntryPredicate, hn]
    rw [heq]
    exact hstate

noncomputable def firstRecurrentIndex (w : ℕ → Y) : ℕ := by
  classical
  exact Nat.find (entryPredicate_exists K w)

noncomputable def firstRecurrentState (w : ℕ → Y) : Y :=
  w (firstRecurrentIndex K w)

theorem firstRecurrentState_measurable :
    Measurable (firstRecurrentState K) := by
  classical
  exact Measurable.find (fun n => measurable_pi_apply n)
    (entryPredicate_measurable K) (entryPredicate_exists K)

theorem firstRecurrentState_mem (w : ℕ → Y)
    (h : HasRecurrentHit K w) :
    firstRecurrentState K w ∈ RecurrentStates K := by
  classical
  have hs := Nat.find_spec (entryPredicate_exists K w)
  change EntryPredicate K w (Nat.find (entryPredicate_exists K w)) at hs
  change EntryPredicate K w (firstRecurrentIndex K w) at hs
  rcases hs with hmem | ⟨_, hnever⟩
  · exact hmem
  · exact (hnever h).elim

/-- An arbitrary but frozen recurrent fallback on paths whose
recurrent-hitting event fails. It is never used on the canonical
probability-one recurrent-entry event. -/
noncomputable def fallbackRecurrentState : Y :=
  Classical.choose
    (exists_reachable_recurrent_state K (Classical.choice inferInstance))

theorem fallbackRecurrentState_mem :
    fallbackRecurrentState K ∈ RecurrentStates K :=
  (Classical.choose_spec
    (exists_reachable_recurrent_state K (Classical.choice inferInstance))).1

/-- A total set-based choice function. The same SET gives the same
representative by congruence; the nonempty-case choice proof is
irrelevant. Empty sets receive a fixed default from Nonempty Y. -/
private noncomputable def chooseSet (C : Set Y) : Y := by
  classical
  exact if h : C.Nonempty then Classical.choose h else Classical.choice inferInstance

private theorem chooseSet_mem {C : Set Y} (hC : C.Nonempty) :
    chooseSet (Y := Y) C ∈ C := by
  classical
  simp only [chooseSet, dif_pos hC]
  exact Classical.choose_spec hC

/-- Equal communicating classes have the EXACT same chosen
representative, independent of which physical state names the class. -/
noncomputable def classRepresentative (i : Y) : Y :=
  chooseSet (CommunicatingClass K i)

theorem classRepresentative_mem (i : Y) :
    classRepresentative K i ∈ CommunicatingClass K i :=
  chooseSet_mem ⟨i, mem_communicatingClass K i⟩

theorem classRepresentative_eq_of_communicates
    {i j : Y} (hij : Communicates K i j) :
    classRepresentative K i = classRepresentative K j := by
  exact congrArg (chooseSet (Y := Y))
    (communicatingClass_eq_of_communicates K hij)

theorem classRepresentative_idempotent (i : Y) :
    classRepresentative K (classRepresentative K i) =
      classRepresentative K i := by
  exact classRepresentative_eq_of_communicates K
    (communicates_symm K (classRepresentative_mem K i))

theorem classRepresentative_recurrent
    {i : Y} (hi : i ∈ RecurrentStates K) :
    classRepresentative K i ∈ RecurrentStates K := by
  exact recurrent_of_communicates K hi (classRepresentative_mem K i)

/-- The same representative is returned for any finite trajectory
that enters the same recurrent communication class. -/
noncomputable def selectedRepresentative (w : ℕ → Y) : Y := by
  classical
  exact if HasRecurrentHit K w then
    classRepresentative K (firstRecurrentState K w)
  else classRepresentative K (fallbackRecurrentState K)

theorem selectedRepresentative_measurable :
    Measurable (selectedRepresentative K) := by
  classical
  unfold selectedRepresentative
  exact (hasRecurrentHit_measurable K).ite
    ((measurable_of_finite (classRepresentative K)).comp
      (firstRecurrentState_measurable K))
    measurable_const

theorem selectedRepresentative_recurrent (w : ℕ → Y) :
    selectedRepresentative K w ∈ RecurrentStates K := by
  classical
  unfold selectedRepresentative
  split_ifs with h
  · exact classRepresentative_recurrent K
      (firstRecurrentState_mem K w h)
  · exact classRepresentative_recurrent K (fallbackRecurrentState_mem K)

theorem selectedRepresentative_fixed (w : ℕ → Y) :
    classRepresentative K (selectedRepresentative K w) =
      selectedRepresentative K w := by
  classical
  unfold selectedRepresentative
  split_ifs <;> exact classRepresentative_idempotent K _

/-- The finite *deduplicated* class representatives, not all physical
states. Different members of one communicating class appear only once. -/
noncomputable def recurrentRepresentatives : Finset Y := by
  classical
  exact Finset.univ.filter (fun i =>
    i ∈ RecurrentStates K ∧ classRepresentative K i = i)

theorem selectedRepresentative_mem (w : ℕ → Y) :
    selectedRepresentative K w ∈ recurrentRepresentatives K := by
  classical
  simp only [recurrentRepresentatives, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ⟨selectedRepresentative_recurrent K w,
    selectedRepresentative_fixed K w⟩

/-- Complete probability distribution of the ACTUAL measurable
random recurrent-class representative under every canonical initial
law. This is the measure identity, not just its point masses. -/
theorem selectedRepresentative_full_law (μ : ProbabilityMeasure Y) :
    (canonicalPathLaw K μ.toMeasure).map (selectedRepresentative K) =
      ∑ i ∈ recurrentRepresentatives K,
        (canonicalPathLaw K μ.toMeasure)
            ((selectedRepresentative K) ⁻¹' {i}) • Measure.dirac i := by
  classical
  exact (Measure.ae_mem_finset_iff_map_eq_sum_dirac
    (s := recurrentRepresentatives K)
    (f := selectedRepresentative K)
    (μ := canonicalPathLaw K μ.toMeasure)
    (selectedRepresentative_measurable K).aemeasurable).mp
      (Filter.Eventually.of_forall (selectedRepresentative_mem K))

/-- A finite law on class representatives can be transported through
any measurable class-level observable, including later constructed
invariant probability measures, without changing class weights. -/
theorem selectedRepresentative_transport
    {H : Type*} [MeasurableSpace H]
    (μ : ProbabilityMeasure Y)
    (f : Y → H) (hf : Measurable f) :
    (canonicalPathLaw K μ.toMeasure).map
      (fun w => f (selectedRepresentative K w)) =
      ∑ i ∈ recurrentRepresentatives K,
        (canonicalPathLaw K μ.toMeasure)
          ((selectedRepresentative K) ⁻¹' {i}) • Measure.dirac (f i) := by
  classical
  rw [show (fun w => f (selectedRepresentative K w)) =
      f ∘ selectedRepresentative K from rfl]
  rw [← Measure.map_map hf (selectedRepresentative_measurable K)]
  rw [selectedRepresentative_full_law K μ]
  rw [Measure.map_finset_sum (hf.aemeasurable)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Measure.map_smul _ hf.aemeasurable]
  rw [Measure.map_dirac' hf i]

end CanonicalClassSelector
end MultipleLimit
end PermanssonResearch
