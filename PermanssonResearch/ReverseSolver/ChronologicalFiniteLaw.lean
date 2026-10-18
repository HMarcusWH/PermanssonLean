import PermanssonResearch.ReverseSolver.BehavioralFinitePolicy

/-!
# The normalized finite chronological state/control law

This finite probability law is constructed from the actual product atoms,
independently of any Bellman value or objective. Its support contains exactly
the enumerated words of the declared horizon, without duplicate words.
-/

namespace PermanssonResearch.ReverseSolver.FiniteMonitor

open ControlledKernel

universe uC

variable {C : Type uC} [DecidableEq C] [Fintype C] {n : ℕ}

theorem traceWords_nodup (r : ℕ) : (traceWords C n r).Nodup := by
  induction r with
  | zero => simp [traceWords]
  | succ r ih =>
      apply List.nodup_flatMap.mpr
      refine ⟨fun a _ => ih.map (fun _ _ h => (List.cons.inj h).2), ?_⟩
      apply (Finset.nodup_toList (Finset.univ : Finset (C × Fin n))).imp
      intro a b hab xs hax hbx
      rcases List.mem_map.mp hax with ⟨wa, _, hea⟩
      rcases List.mem_map.mp hbx with ⟨wb, _, heb⟩
      exact hab (List.cons.inj (hea.trans heb.symm)).1

theorem traceWords_length (r : ℕ) (xs : List (C × Fin n)) (hx : xs ∈ traceWords C n r) :
    xs.length=r := by
  induction r generalizing xs with
  | zero => simpa [traceWords] using hx
  | succ r ih =>
      rcases List.mem_flatMap.mp hx with ⟨a, _, hxa⟩
      rcases List.mem_map.mp hxa with ⟨ys, hys, rfl⟩
      simp [ih ys hys]

theorem traceMass_nonnegative (sys : FiniteControlSystem C n) (σ : BehavioralPolicy sys)
    (t : ℕ) (h : TraceHistory C n) (y : Fin n) (xs : List (C × Fin n)) :
    0 ≤ traceMass sys σ t h y xs := by
  induction xs generalizing t h y with
  | nil => norm_num [traceMass]
  | cons a xs ih =>
      exact mul_nonneg (mul_nonneg (σ.nonnegative t h y a.1)
        (by exact_mod_cast (sys.matrix a.1).entry_nonneg y a.2)) (ih _ _ _)

/-- Normalization follows from the stochastic rows and behavioral simplex,
with no reference to the optimizing recursion. -/
theorem traceMass_total_one (sys : FiniteControlSystem C n) (σ : BehavioralPolicy sys)
    (r t : ℕ) (h : TraceHistory C n) (y : Fin n) :
    ((traceWords C n r).map (traceMass sys σ t h y)).sum = 1 := by
  let M : Monitor C n Unit := ⟨fun _ => (), fun _ _ _ _ _ => (), fun _ _ => 1⟩
  have he := traceExpectation_eq_behavioralValue sys M σ r t h y ()
  have hv := behavioralValue_constant_one sys M σ (by intros; rfl) r t h y ()
  rw [hv] at he
  simpa [traceExpectation, M] using he

/-- A finite probability law with real atoms and explicit finite support. -/
structure FiniteProbabilityLaw (A : Type*) [DecidableEq A] where
  support : Finset A
  atom : A → ℝ
  nonnegative : ∀ a, 0 ≤ atom a
  supported : ∀ a, a ∉ support → atom a=0
  normalized : ∑ a ∈ support, atom a = 1

noncomputable def chronologicalLaw (sys : FiniteControlSystem C n)
    (σ : BehavioralPolicy sys) (r t : ℕ) (h : TraceHistory C n) (y : Fin n) :
    FiniteProbabilityLaw (List (C × Fin n)) where
  support := (traceWords C n r).toFinset
  atom xs := if xs ∈ (traceWords C n r).toFinset then traceMass sys σ t h y xs else 0
  nonnegative xs := by split <;> simp [traceMass_nonnegative]
  supported xs hx := by simp [hx]
  normalized := by
    simp only [Finset.sum_ite_mem, Finset.inter_self]
    rw [List.sum_toFinset _ (traceWords_nodup r)]
    exact traceMass_total_one sys σ r t h y

end PermanssonResearch.ReverseSolver.FiniteMonitor
