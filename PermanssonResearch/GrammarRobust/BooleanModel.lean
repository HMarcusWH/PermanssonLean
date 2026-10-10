import PermanssonResearch.GrammarRobust.RefinementTransport
import Mathlib.Probability.Kernel.Deterministic
import Mathlib.Tactic

/-!
# Lane B — fully typed two-atom Boolean strategic-world model

These are actual stochastic kernels, not a table of assumed effects.
The action atom sets α to false. The update atom sets U to false.
World P always copies the chosen action to the next world state.
-/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch
namespace GrammarRobust
namespace BooleanModel

open PermanssonLean

abbrev Y := JointState Bool Bool
abbrev PhysicalAtom := Atom (Fin 1) (Fin 1)

def actionTrue : Kernel Y Bool :=
  Kernel.deterministic (fun _ => true) (by fun_prop)
def actionFalse : Kernel Y Bool :=
  Kernel.deterministic (fun _ => false) (by fun_prop)
def updateTrue : Kernel (UpdateInput Bool Bool Bool) Bool :=
  Kernel.deterministic (fun _ => true) (by fun_prop)
def updateFalse : Kernel (UpdateInput Bool Bool Bool) Bool :=
  Kernel.deterministic (fun _ => false) (by fun_prop)
def worldCopy : Kernel (WorldInput Bool Bool Bool) Bool :=
  Kernel.deterministic (fun z => z.2) (by fun_prop)

/-- The baseline always moves to (true,true) after one transition. -/
def baseline : StrategicWorldModel Bool Bool Bool where
  generator := {
    action := actionTrue
    update := updateTrue
    action_isMarkov := by unfold actionTrue; infer_instance
    update_isMarkov := by unfold updateTrue; infer_instance }
  world := worldCopy
  world_isMarkov := by unfold worldCopy; infer_instance

/-- Two physical patches of *different* strategic primitives, each active on
all rows of its own input domain. -/
noncomputable def bank : AtomicBank baseline (Fin 1) (Fin 1) where
  action := fun _ => {
    region := Set.univ
    measurable_region := MeasurableSet.univ
    replacement := actionFalse
    replacement_isMarkov := by unfold actionFalse; infer_instance }
  update := fun _ => {
    region := Set.univ
    measurable_region := MeasurableSet.univ
    replacement := updateFalse
    replacement_isMarkov := by unfold updateFalse; infer_instance }
  action_disjoint := by
    intro i j hij
    exact False.elim (hij (Subsingleton.elim _ _))
  update_disjoint := by
    intro i j hij
    exact False.elim (hij (Subsingleton.elim _ _))

/-- Fine components separately name the physical action/update atoms. -/
noncomputable def fine : PartitionGrammar (Fin 1) (Fin 1) (Fin 2) where
  atomsOf := fun c =>
    if c = 0 then {Sum.inl (0 : Fin 1)}
    else {Sum.inr (0 : Fin 1)}
  nonempty := by
    intro c
    fin_cases c <;> simp
  disjoint := by
    intro c d h
    fin_cases c <;> fin_cases d <;> simp_all
  cover := by
    intro a
    cases a with
    | inl i =>
      refine ⟨0, ?_⟩
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      simp [hi]
    | inr i =>
      refine ⟨1, ?_⟩
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      simp [hi]
  allowed := fun _ => True
  allowed_empty := trivial

/-- Coarse grammar has ONE component containing both physical atoms. -/
noncomputable def coarse : PartitionGrammar (Fin 1) (Fin 1) (Fin 1) where
  atomsOf := fun _ => Finset.univ
  nonempty := by
    intro _
    exact ⟨Sum.inl 0, Finset.mem_univ _⟩
  disjoint := by
    intro c d h
    exact False.elim (h (Subsingleton.elim _ _))
  cover := by
    intro a
    exact ⟨0, Finset.mem_univ a⟩
  allowed := fun _ => True
  allowed_empty := trivial

/-- A genuine *non-injective* component coarsening. -/
noncomputable def coarsening : Coarsening fine coarse where
  map := fun _ => 0
  onto := by
    intro c
    refine ⟨0, ?_⟩
    exact Subsingleton.elim _ _
  coarse_atoms := by
    intro c
    ext a
    have hc : c = (0 : Fin 1) := Subsingleton.elim _ _
    subst c
    cases a with
    | inl i =>
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      simp [coarse, fine]
    | inr i =>
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      simp [coarse, fine]
  respects_allowed := by
    intro D _
    trivial

/-- The actual fine two-atom process is the actual coarse one-component
process, including both strategic primitives and the unchanged world P. -/
theorem true_refinement_equality :
    blockModel baseline bank fine ({0,1} : Finset (Fin 2)) =
    blockModel baseline bank coarse ({0} : Finset (Fin 1)) := by
  have hlift : coarsening.lift ({0} : Finset (Fin 1)) =
      ({0,1} : Finset (Fin 2)) := by
    ext c
    fin_cases c <;> simp [Coarsening.lift, coarsening]
  rw [← hlift]
  exact coarsening.blockModel_lift_eq baseline bank ({0} : Finset (Fin 1))

end BooleanModel
end GrammarRobust
end PermanssonResearch
