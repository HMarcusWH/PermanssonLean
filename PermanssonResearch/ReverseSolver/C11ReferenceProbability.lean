import PermanssonResearch.ReverseSolver.C11ReferenceMatrix

namespace PermanssonResearch.ReverseSolver.C11

open PermanssonResearch.MultipleLimit.FiniteInvariantExistence
open PermanssonResearch.MultipleLimit.FiniteCesaroAlgebra

variable {Y : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-- The Cramer solution is a probability stationary vector. Nonnegativity is
proved by identifying its real embedding with the independently existing
genuine finite-chain invariant probability, rather than assumed in a receipt. -/
theorem referenceWeights_probability (P : Matrix Y Y ℚ)
    (hP : ∀ x y, 0≤P x y) (hrow : ∀ x, ∑ y : Y, P x y=1)
    (hirr : ∀ x y, Relation.ReflTransGen (fun a b => 0<P a b) x y) :
    (∀ y, 0≤referenceWeights P y) ∧
    (∑ y : Y, referenceWeights P y)=1 ∧
    ∀ y, referenceWeights P y=∑ x : Y, referenceWeights P x*P x y := by
  let K : Y → Y → ℝ := fun x y => (P x y : ℝ)
  have hK : ∀ x y, 0≤K x y := by
    intro x y
    change (0:ℝ)≤(P x y:ℝ)
    exact_mod_cast hP x y
  have hKrow : ∀ x, ∑ y : Y, K x y=1 := by
    intro x
    change (∑ y : Y, (P x y:ℝ))=1
    exact_mod_cast hrow x
  obtain ⟨π,hπ,hπsum,hπstat⟩ := exists_stationary_real K hK hKrow
  let A : Matrix Y Y ℝ := fun x y => (referenceMatrix P x y : ℝ)
  have hπA : A.mulVec π=(fun _ => 1) := by
    funext x
    change (∑ y : Y, ((referenceMatrix P x y : ℚ) : ℝ)*π y)=1
    simp only [referenceMatrix]
    push_cast
    have hdiag (y : Y) : ((if x=y then 1 else 0 : ℚ) : ℝ)=
        (if x=y then 1 else 0) := by split_ifs <;> norm_num
    simp_rw [hdiag]
    simp_rw [add_mul, sub_mul]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hs : (∑ y : Y, (P y x : ℝ)*π y)=π x := by
      simpa only [pushVector, K, mul_comm] using hπstat x
    simp [eq_comm,hs,hπsum]
  have hd := referenceMatrix_det_ne_zero P hP hrow hirr
  have hdA : A.det≠0 := by
    change ((referenceMatrix P).map (fun q : ℚ => (q : ℝ))).det≠0
    rw [← Rat.cast_det]
    exact_mod_cast hd
  have hpA : A.mulVec (fun y => (referenceWeights P y : ℝ))=(fun _ => 1) := by
    funext x
    change (∑ y : Y, (referenceMatrix P x y : ℝ)*(referenceWeights P y : ℝ))=1
    exact_mod_cast referenceWeights_matrix_equation P hd x
  have he : (fun y => (referenceWeights P y : ℝ))=π :=
    Matrix.mulVec_injective_of_det_ne_zero hdA (hpA.trans hπA.symm)
  refine ⟨?_,?_,?_⟩
  · intro y
    have hh := hπ y
    rw [← congrFun he y] at hh
    exact_mod_cast hh
  · have hh := congrArg (fun v : Y → ℝ => ∑ y : Y, v y) he
    rw [hπsum] at hh
    exact_mod_cast hh
  · intro y
    have hh : (referenceWeights P y : ℝ)=
        ∑ x : Y, (referenceWeights P x : ℝ)*(P x y : ℝ) := by
      simp_rw [congrFun he]
      exact (hπstat y).symm
    exact_mod_cast hh

end PermanssonResearch.ReverseSolver.C11
