import PermanssonResearch.ReverseSolver.PolytopeLinearProgram
import PermanssonResearch.StrategicWorld.ActionTrace

/-! Nature chooses a finite parameter after seeing the control distribution,
but before the private realized control draw. This stage game is separate
from the realized-control-observing rectangular chronological game. -/

namespace PermanssonResearch.ReverseSolver.PrivateControlStage
open ExactPolytope ActionTrace
variable {C Θ : Type*} [Fintype C] [LinearOrder C] [Nonempty C]
  [Fintype Θ] [LinearOrder Θ] [Nonempty Θ]

def lowerPayoff (Q : Θ → C → ℚ) : ℚ :=
  Finset.univ.inf' Finset.univ_nonempty (fun p : Θ × C => Q p.1 p.2)

def upperPayoff (Q : Θ → C → ℚ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty (fun p : Θ × C => Q p.1 p.2)

theorem lowerPayoff_le (Q : Θ → C → ℚ) (θ : Θ) (c : C) : lowerPayoff Q≤Q θ c :=
  Finset.inf'_le _ (Finset.mem_univ (θ,c))

theorem le_upperPayoff (Q : Θ → C → ℚ) (θ : Θ) (c : C) : Q θ c≤upperPayoff Q :=
  Finset.le_sup' (fun p : Θ × C => Q p.1 p.2) (Finset.mem_univ (θ,c))

noncomputable def stagePayoff (Q : Θ → C → ℚ) (p : Row C) (θ : Θ) : ℝ :=
  p.expect (fun c => (Q θ c : ℝ))

noncomputable def minimizingNature (Q : Θ → C → ℚ) (p : Row C) : Θ :=
  Classical.choose (Finset.exists_min_image Finset.univ (stagePayoff Q p) Finset.univ_nonempty)

noncomputable def privateValue (Q : Θ → C → ℚ) (p : Row C) : ℝ :=
  stagePayoff Q p (minimizingNature Q p)

theorem privateValue_le (Q : Θ → C → ℚ) (p : Row C) (θ : Θ) :
    privateValue Q p≤stagePayoff Q p θ :=
  (Classical.choose_spec (Finset.exists_min_image Finset.univ (stagePayoff Q p)
    Finset.univ_nonempty)).2 θ (Finset.mem_univ _)

theorem stagePayoff_bounds (Q : Θ → C → ℚ) (p : Row C) (θ : Θ) :
    (lowerPayoff Q : ℝ)≤stagePayoff Q p θ ∧ stagePayoff Q p θ≤(upperPayoff Q : ℝ) := by
  constructor
  · simpa only [stagePayoff,Row.expect_const] using p.expect_mono
      (fun c => show (lowerPayoff Q : ℝ)≤(Q θ c : ℝ) by exact_mod_cast lowerPayoff_le Q θ c)
  · simpa only [stagePayoff,Row.expect_const] using p.expect_mono
      (fun c => show (Q θ c : ℝ)≤(upperPayoff Q : ℝ) by exact_mod_cast le_upperPayoff Q θ c)

theorem privateValue_bounds (Q : Θ → C → ℚ) (p : Row C) :
    (lowerPayoff Q : ℝ)≤privateValue Q p ∧ privateValue Q p≤(upperPayoff Q : ℝ) :=
  stagePayoff_bounds Q p _

/-- The actual order of draws: nature's parameter is drawn first, without
observing the subsequent private control realization. -/
noncomputable def stageLaw (p : Row C) (η : Row Θ) : Row (Θ × C) :=
  η.bind (fun θ => p.map (fun c => (θ,c)))

theorem actual_stage_expectation (Q : Θ → C → ℚ) (p : Row C) (η : Row Θ) :
    (stageLaw p η).expect (fun a => (Q a.1 a.2 : ℝ))=η.expect (stagePayoff Q p) := by
  rw [stageLaw,Row.expect_bind]
  congr 1
  funext θ
  rw [Row.expect_map]
  rfl

theorem actual_nature_lower_bound (Q : Θ → C → ℚ) (p : Row C) (η : Row Θ) :
    privateValue Q p≤(stageLaw p η).expect (fun a => (Q a.1 a.2 : ℝ)) := by
  rw [actual_stage_expectation]
  simpa only [Row.expect_const] using η.expect_mono (privateValue_le Q p)

theorem actual_minimizing_nature (Q : Θ → C → ℚ) (p : Row C) :
    (stageLaw p (Row.pure (minimizingNature Q p))).expect (fun a => (Q a.1 a.2 : ℝ))=
      privateValue Q p := by simp [actual_stage_expectation,privateValue]

def nonnegativeConstraint (c : C) : RationalConstraint (Option C) :=
  ⟨fun j => if j=some c then -1 else 0,0⟩

def simplexUpper : RationalConstraint (Option C) :=
  ⟨fun j => match j with | none => 0 | some _ => 1,1⟩

def simplexLower : RationalConstraint (Option C) :=
  ⟨fun j => match j with | none => 0 | some _ => -1,-1⟩

def valueLower (Q : Θ → C → ℚ) : RationalConstraint (Option C) :=
  ⟨fun j => if j=none then -1 else 0,-lowerPayoff Q⟩

def natureConstraint (Q : Θ → C → ℚ) (θ : Θ) : RationalConstraint (Option C) :=
  ⟨fun j => match j with | none => 1 | some c => -Q θ c,0⟩

def stageConstraints (Q : Θ → C → ℚ) : List (RationalConstraint (Option C)) :=
  ((Finset.univ : Finset C).sort (·≤·)).map nonnegativeConstraint ++
    [simplexUpper,simplexLower,valueLower Q] ++
    ((Finset.univ : Finset Θ).sort (·≤·)).map (natureConstraint Q)

theorem nonnegativeConstraint_iff (x : Option C → ℝ) (c : C) :
    (nonnegativeConstraint c).holds x ↔ 0≤x (some c) := by
  have he (j : Option C) : ((if j=some c then (-1:ℚ) else 0 : ℚ) : ℝ)*x j=
      if j=some c then -x j else 0 := by split_ifs <;> simp
  simp only [nonnegativeConstraint,RationalConstraint.holds,Rat.cast_zero]
  simp_rw [he]
  simp

theorem simplexUpper_iff (x : Option C → ℝ) :
    simplexUpper.holds x ↔ (∑ c : C, x (some c))≤1 := by
  simp [simplexUpper,RationalConstraint.holds,Fintype.sum_option]

theorem simplexLower_iff (x : Option C → ℝ) :
    simplexLower.holds x ↔ 1≤(∑ c : C, x (some c)) := by
  simp [simplexLower,RationalConstraint.holds,Fintype.sum_option,Finset.sum_neg_distrib]

theorem valueLower_iff (Q : Θ → C → ℚ) (x : Option C → ℝ) :
    (valueLower Q).holds x ↔ (lowerPayoff Q : ℝ)≤x none := by
  simp [valueLower,RationalConstraint.holds,ite_mul]

theorem natureConstraint_iff (Q : Θ → C → ℚ) (θ : Θ) (x : Option C → ℝ) :
    (natureConstraint Q θ).holds x ↔ x none≤∑ c : C, x (some c)*(Q θ c : ℝ) := by
  simp only [natureConstraint,RationalConstraint.holds,Fintype.sum_option,
    Rat.cast_one,Rat.cast_zero,Rat.cast_neg,one_mul,neg_mul,Finset.sum_neg_distrib]
  simp_rw [mul_comm (Q θ _ : ℝ)]
  constructor <;> intro h <;> linarith

theorem stageConstraints_iff (Q : Θ → C → ℚ) (x : Option C → ℝ) :
    x∈listFeasible (stageConstraints Q) ↔
      (∀ c,0≤x (some c)) ∧ (∑ c : C,x (some c))=1 ∧
      (lowerPayoff Q : ℝ)≤x none ∧
      ∀ θ,x none≤∑ c : C,x (some c)*(Q θ c : ℝ) := by
  have he : x∈listFeasible (stageConstraints Q) ↔
      (∀ c,0≤x (some c)) ∧
      ((∑ c : C,x (some c))≤1 ∧ 1≤(∑ c : C,x (some c)) ∧ (lowerPayoff Q : ℝ)≤x none) ∧
      ∀ θ,x none≤∑ c : C,x (some c)*(Q θ c : ℝ) := by
    change (∀ a∈stageConstraints Q,a.holds x) ↔ _
    simp only [stageConstraints,List.forall_mem_append,List.forall_mem_map,
      Finset.mem_sort,Finset.mem_univ,forall_const,List.forall_mem_cons,List.forall_mem_nil,
      and_true,nonnegativeConstraint_iff,simplexUpper_iff,simplexLower_iff,valueLower_iff,
      natureConstraint_iff]
    simp [and_assoc]
  rw [he]
  constructor
  · rintro ⟨hn,⟨hu,hl,hv⟩,hθ⟩
    exact ⟨hn,le_antisymm hu hl,hv,hθ⟩
  · rintro ⟨hn,hs,hv,hθ⟩
    exact ⟨hn,⟨hs.le,hs.ge,hv⟩,hθ⟩

end PermanssonResearch.ReverseSolver.PrivateControlStage
