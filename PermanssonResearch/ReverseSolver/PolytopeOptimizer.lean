import PermanssonResearch.ReverseSolver.PolytopeCompleteness
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.MinMax

/-!
# Executable exhaustive rational linear optimization

The result is an `Option`: infeasible compact polytopes return `none` and a
returned rational vector dominates every real feasible linear objective value.
-/

namespace PermanssonResearch.ReverseSolver.ExactPolytope

open Matrix Set

variable {I J : Type*} [Fintype I] [LinearOrder I] [Fintype J] [DecidableEq J]

def activeSelections : List (Finset I) :=
  ((Finset.univ : Finset I).sort (· ≤ ·)).sublists.map List.toFinset

theorem activeSelections_complete (s : Finset I) : s ∈ activeSelections (I := I) := by
  let l := (Finset.univ : Finset I).sort (· ≤ ·)
  have he : (l.filter (fun i => i ∈ s)).toFinset = s := by
    ext i
    simp [l]
  exact List.mem_map.mpr ⟨l.filter (fun i => i ∈ s),
    List.mem_sublists.mpr (List.filter_sublist), he⟩

def rationalCandidateList (A : Matrix I J ℚ) (b : I → ℚ) : List (J → ℚ) :=
  ((activeSelections.filter fun s => (selectedGram A s).det ≠ 0).map
    (rationalCandidate A b)).filter (rationalFeasible A b)

theorem mem_rationalCandidateList (A : Matrix I J ℚ) (b : I → ℚ) (q : J → ℚ) :
    q ∈ rationalCandidateList A b ↔ q ∈ rationalCandidates A b := by
  simp only [rationalCandidateList, rationalCandidates, List.mem_filter, List.mem_map,
    Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨⟨s,⟨_,hd⟩,he⟩,hf⟩
    exact ⟨⟨s,hd,he⟩,hf⟩
  · rintro ⟨⟨s,hd,he⟩,hf⟩
    exact ⟨⟨s,⟨activeSelections_complete s,hd⟩,he⟩,hf⟩

def optimizeRational (A : Matrix I J ℚ) (b : I → ℚ) (c : J → ℚ) : Option (J → ℚ) :=
  (rationalCandidateList A b).argmax (dotProduct c)

def realObjective (c : J → ℚ) : (J → ℝ) →L[ℝ] ℝ :=
  ∑ j : J, (c j : ℝ) • ContinuousLinearMap.proj j

theorem realObjective_apply (c : J → ℚ) (x : J → ℝ) :
    realObjective c x = ∑ j : J, (c j : ℝ) * x j := by
  simp [realObjective]

theorem optimizeRational_none_iff (A : Matrix I J ℚ) (b : I → ℚ) (c : J → ℚ)
    (hc : IsCompact (feasible (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)))) :
    optimizeRational A b c = none ↔
      feasible (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)) = ∅ := by
  rw [optimizeRational, List.argmax_eq_none]
  have he : rationalCandidateList A b = [] ↔ ¬(rationalCandidates A b).Nonempty := by
    rw [List.eq_nil_iff_forall_not_mem]
    simp [mem_rationalCandidateList, Finset.Nonempty]
  rw [he, rationalCandidates_nonempty_iff A b hc, Set.not_nonempty_iff_eq_empty]

theorem optimizeRational_some_feasible (A : Matrix I J ℚ) (b : I → ℚ)
    (c q : J → ℚ) (hq : optimizeRational A b c = some q) : rationalFeasible A b q := by
  apply rationalCandidates_feasible A b q
  apply (mem_rationalCandidateList A b q).mp
  exact List.argmax_mem hq

theorem optimizeRational_some_optimal (A : Matrix I J ℚ) (b : I → ℚ)
    (c q : J → ℚ) (hq : optimizeRational A b c = some q)
    (hc : IsCompact (feasible (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)))) :
    ∀ x ∈ feasible (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)),
      (∑ j : J, (c j : ℝ) * x j) ≤ (dotProduct c q : ℚ) := by
  have hqf := (rationalFeasible_iff_cast A b q).mp (optimizeRational_some_feasible A b c q hq)
  obtain ⟨v,hv,hm⟩ := exists_rational_optimal_candidate A b hc ⟨_,hqf⟩ (realObjective c)
  have hle : dotProduct c v ≤ dotProduct c q :=
    List.le_of_mem_argmax ((mem_rationalCandidateList A b v).mpr hv) hq
  have hcast : (∑ j : J, (c j : ℝ) * (v j : ℝ)) ≤ (dotProduct c q : ℚ) := by
    exact_mod_cast hle
  intro x hx
  have hle' : (∑ j : J, (c j : ℝ) * x j) ≤ ∑ j : J, (c j : ℝ) * (v j : ℝ) := by
    simpa only [realObjective_apply] using hm x hx
  exact hle'.trans hcast

end PermanssonResearch.ReverseSolver.ExactPolytope
