import PermanssonResearch.ReverseSolver.PolytopeRational

/-!
# Completeness of exact rational Gram/Cramer enumeration

Every real vertex is one of the finitely enumerated rational candidates. The
active subset is used only in this proof; the reference enumerates every subset
using rational arithmetic.
-/

namespace PermanssonResearch.ReverseSolver.ExactPolytope

open Matrix Set

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem cast_selectedGram (A : Matrix I J ℚ) (s : Finset I) :
    ((selectedGram A s).map fun a => (a : ℝ)) =
      selectedGram (fun i j => (A i j : ℝ)) s := by
  ext j k
  simp [selectedGram, selectedRows, Matrix.mul_apply, Matrix.transpose_apply,
    Rat.cast_sum, Rat.cast_mul]

theorem cast_gramRhs (A : Matrix I J ℚ) (b : I → ℚ) (s : Finset I) (j : J) :
    (gramRhs A b s j : ℝ) =
      (selectedRows (fun i k => (A i k : ℝ)) s).transpose.mulVec
        (fun i => if i ∈ s then (b i : ℝ) else 0) j := by
  simp [gramRhs, selectedRows, Matrix.mulVec, dotProduct, Rat.cast_sum, Rat.cast_mul]

theorem extreme_eq_rationalCandidate (A : Matrix I J ℚ) (b : I → ℚ)
    (x : J → ℝ)
    (hx : x ∈ (feasible (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ))).extremePoints ℝ) :
    ∃ s : Finset I, (selectedGram A s).det ≠ 0 ∧
      (fun j => (rationalCandidate A b s j : ℝ)) = x := by
  classical
  let s : Finset I := Finset.univ.filter fun i =>
    dotProduct (fun j => (A i j : ℝ)) x = (b i : ℝ)
  have hdreal : (selectedGram (fun i j => (A i j : ℝ)) s).det ≠ 0 :=
    extreme_active_gram_det_ne_zero _ _ x hx
  have hd : (selectedGram A s).det ≠ 0 := by
    intro he
    apply hdreal
    rw [← cast_selectedGram, ← Rat.cast_det, he, Rat.cast_zero]
  refine ⟨s, hd, ?_⟩
  apply Matrix.mulVec_injective_of_det_ne_zero hdreal
  have hrows : (selectedRows (fun i j => (A i j : ℝ)) s).mulVec x =
      (fun i => if i ∈ s then (b i : ℝ) else 0) := by
    funext i
    by_cases hi : i ∈ s
    · have he : dotProduct (fun j => (A i j : ℝ)) x = (b i : ℝ) :=
        (Finset.mem_filter.mp hi).2
      simpa [Matrix.mulVec, dotProduct, selectedRows, hi] using he
    · simp [Matrix.mulVec, dotProduct, selectedRows, hi]
  have he := rationalCandidate_equation A b s hd
  have hc : (selectedGram (fun i j => (A i j : ℝ)) s).mulVec
      (fun j => (rationalCandidate A b s j : ℝ)) = fun j => (gramRhs A b s j : ℝ) := by
    funext j
    have hh := congrArg (fun a : ℚ => (a : ℝ)) (congrFun he j)
    simpa only [← cast_selectedGram, Matrix.mulVec, dotProduct, Matrix.map_apply,
      Rat.cast_sum, Rat.cast_mul] using hh
  rw [hc]
  funext j
  rw [cast_gramRhs]
  simp only [selectedGram, ← Matrix.mulVec_mulVec, hrows]

theorem rationalFeasible_iff_cast (A : Matrix I J ℚ) (b : I → ℚ) (x : J → ℚ) :
    rationalFeasible A b x ↔
      (fun j => (x j : ℝ)) ∈ feasible (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)) := by
  unfold rationalFeasible feasible
  simp only [Set.mem_setOf_eq, dotProduct]
  constructor <;> intro h i
  · exact_mod_cast h i
  · exact_mod_cast h i

theorem every_vertex_is_enumerated (A : Matrix I J ℚ) (b : I → ℚ)
    (x : J → ℝ)
    (hx : x ∈ (feasible (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ))).extremePoints ℝ) :
    ∃ q ∈ rationalCandidates A b, (fun j => (q j : ℝ)) = x := by
  obtain ⟨s, hd, he⟩ := extreme_eq_rationalCandidate A b x hx
  refine ⟨rationalCandidate A b s, ?_, he⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨s, ?_, rfl⟩, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩
  · apply (rationalFeasible_iff_cast A b _).mpr
    rw [he]
    exact hx.1

/-- Enumeration is empty exactly when the actual compact rational polytope is empty. -/
theorem rationalCandidates_nonempty_iff (A : Matrix I J ℚ) (b : I → ℚ)
    (hc : IsCompact (feasible (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)))) :
    (rationalCandidates A b).Nonempty ↔
      (feasible (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ))).Nonempty := by
  constructor
  · rintro ⟨q,hq⟩
    exact ⟨_, (rationalFeasible_iff_cast A b q).mp (rationalCandidates_feasible A b q hq)⟩
  · intro hn
    obtain ⟨x,hx⟩ := hc.extremePoints_nonempty hn
    obtain ⟨q,hq,_⟩ := every_vertex_is_enumerated A b x hx
    exact ⟨q,hq⟩

/-- A rational enumerated candidate dominates every real feasible objective value. -/
theorem exists_rational_optimal_candidate (A : Matrix I J ℚ) (b : I → ℚ)
    (hc : IsCompact (feasible (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ))))
    (hn : (feasible (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ))).Nonempty)
    (objective : (J → ℝ) →L[ℝ] ℝ) :
    ∃ q ∈ rationalCandidates A b,
      ∀ x ∈ feasible (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)),
        objective x ≤ objective (fun j => (q j : ℝ)) := by
  obtain ⟨v,hv,hm⟩ := compact_exists_optimal_vertex _ _ hc hn objective
  obtain ⟨q,hq,he⟩ := every_vertex_is_enumerated A b v hv
  exact ⟨q,hq,fun x hx => by rw [he]; exact hm x hx⟩

end PermanssonResearch.ReverseSolver.ExactPolytope
