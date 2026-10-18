import PermanssonResearch.StrategicWorld.ActionTrace
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Finite transportation duality from separation of the actual transport
epigraph. The feasible set and its compactness are constructed here. -/

open scoped BigOperators Pointwise
namespace PermanssonResearch.Probability.FiniteTransport
open ActionTrace
set_option autoImplicit false

variable {Y : Type*} [Fintype Y]

abbrev Coordinates (Y : Type*) := (Y → ℝ) × ((Y → ℝ) × ℝ)

noncomputable def summary (d : Y × Y → ℝ) : (Y × Y → ℝ) →ₗ[ℝ] Coordinates Y where
  toFun g := (fun i => ∑ j, g (i,j), fun j => ∑ i, g (i,j), ∑ z, g z * d z)
  map_add' g h := by
    ext i <;> simp [Finset.sum_add_distrib, add_mul]
  map_smul' a g := by
    ext i <;> simp [Finset.mul_sum, mul_assoc]

def verticalRay (Y : Type*) : Set (Coordinates Y) :=
  {z | z.1 = 0 ∧ z.2.1 = 0 ∧ 0 ≤ z.2.2}

theorem verticalRay_closed : IsClosed (verticalRay Y) :=
  (isClosed_eq continuous_fst continuous_const).inter
    ((isClosed_eq (continuous_fst.comp continuous_snd) continuous_const).inter
      (isClosed_le continuous_const (continuous_snd.comp continuous_snd)))

theorem verticalRay_convex : Convex ℝ (verticalRay Y) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · change a • x.1 + b • y.1 = 0
    simp [hx.1, hy.1]
  · change a • x.2.1 + b • y.2.1 = 0
    simp [hx.2.1, hy.2.1]
  · change 0 ≤ a * x.2.2 + b * y.2.2
    exact add_nonneg (mul_nonneg ha hx.2.2) (mul_nonneg hb hy.2.2)

noncomputable def epigraph (d : Y × Y → ℝ) : Set (Coordinates Y) :=
  summary d '' stdSimplex ℝ (Y × Y) + verticalRay Y

theorem epigraph_closed (d : Y × Y → ℝ) : IsClosed (epigraph d) :=
  verticalRay_closed.add_left_of_isCompact
    ((isCompact_stdSimplex ℝ (Y × Y)).image (summary d).continuous_of_finiteDimensional)

theorem epigraph_convex (d : Y × Y → ℝ) : Convex ℝ (epigraph d) :=
  ((convex_stdSimplex ℝ (Y × Y)).linear_image (summary d)).add verticalRay_convex

theorem summary_mem_epigraph (d : Y × Y → ℝ) (g : Row (Y × Y)) {t : ℝ}
    (ht : 0 ≤ t) : summary d g.mass + (0,0,t) ∈ epigraph d := by
  exact ⟨summary d g.mass, ⟨g.mass, ⟨g.nonneg,g.total⟩, rfl⟩,
    (0,0,t), ⟨rfl,rfl,ht⟩, rfl⟩

theorem mem_epigraph_iff (d : Y × Y → ℝ) (p q : Row Y) (c : ℝ) :
    (p.mass,q.mass,c) ∈ epigraph d ↔
      ∃ g : Row (Y × Y),
        (∀ i, ∑ j, g.mass (i,j) = p.mass i) ∧
        (∀ j, ∑ i, g.mass (i,j) = q.mass j) ∧ g.expect d ≤ c := by
  constructor
  · rintro ⟨x,⟨g,hg,rfl⟩,z,hz,heq⟩
    let G : Row (Y × Y) := ⟨g,hg.1,hg.2⟩
    refine ⟨G,?_,?_,?_⟩
    · intro i
      have h := congrFun (congrArg Prod.fst heq) i
      simpa [summary,G,hz.1] using h
    · intro j
      have h := congrFun (congrArg (fun x : Coordinates Y => x.2.1) heq) j
      simpa [summary,G,hz.2.1] using h
    · have h := congrArg (fun x : Coordinates Y => x.2.2) heq
      change (∑ x, g x * d x) + z.2.2 = c at h
      change (∑ x, g x * d x) ≤ c
      linarith [hz.2.2]
  · rintro ⟨g,hp,hq,hc⟩
    have h := summary_mem_epigraph d g (t := c-g.expect d) (sub_nonneg.mpr hc)
    have heq : summary d g.mass + (0,0,c-g.expect d) = (p.mass,q.mass,c) := by
      ext i <;> simp [summary,Row.expect,hp,hq]
    rwa [heq] at h

noncomputable def product (p q : Row Y) : Row (Y × Y) where
  mass z := p.mass z.1 * q.mass z.2
  nonneg z := mul_nonneg (p.nonneg z.1) (q.nonneg z.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp [← Finset.mul_sum,q.total,p.total]

theorem product_summary (d : Y × Y → ℝ) (p q : Row Y) :
    summary d (product p q).mass = (p.mass,q.mass,(product p q).expect d) := by
  ext i <;> simp [summary,product,Row.expect,← Finset.mul_sum,← Finset.sum_mul,
    p.total,q.total]

theorem pure_summary (d : Y × Y → ℝ) (i j : Y) [DecidableEq Y] :
    summary d (Row.pure (i,j)).mass = (Pi.single i 1,Pi.single j 1,d (i,j)) := by
  classical
  apply Prod.ext
  · funext k
    by_cases h : k = i
    · subst k
      simp [summary,Row.pure,Pi.single_apply,Prod.mk.injEq]
      have he : (Finset.univ.filter (fun x : Y => j = x)) = {j} := by
        ext x
        simp [eq_comm]
      rw [he]
      simp
    · simp [summary,Row.pure,Pi.single_apply,Prod.mk.injEq,h,Ne.symm h]
  · apply Prod.ext
    · funext k
      by_cases h : k = j
      · subst k
        simp [summary,Row.pure,Pi.single_apply,Prod.mk.injEq]
        have he : (Finset.univ.filter (fun x : Y => i = x)) = {i} := by
          ext x
          simp [eq_comm]
        rw [he]
        simp
      · simp [summary,Row.pure,Pi.single_apply,Prod.mk.injEq,h,Ne.symm h]
    · simp [summary,Row.pure]

theorem functional_decomposition [DecidableEq Y] (F : Coordinates Y →L[ℝ] ℝ)
    (r s : Y → ℝ) (t : ℝ) :
    F (r,s,t) = (∑ i, r i * F (Pi.single i 1,0,0)) +
      (∑ j, s j * F (0,Pi.single j 1,0)) + t * F (0,0,1) := by
  classical
  have h : (r,s,t) = (∑ i, r i • (Pi.single i 1,0,0)) +
      (∑ j, s j • (0,Pi.single j 1,0)) + t • (0,0,1) := by
    ext i <;> simp [Prod.fst_sum,Prod.snd_sum,Finset.sum_apply,Pi.single_apply]
  rw [h,map_add,map_add,map_sum,map_sum,map_smul]
  simp only [map_smul,smul_eq_mul]

theorem functional_vertical (F : Coordinates Y →L[ℝ] ℝ) (z : Coordinates Y) (t : ℝ) :
    F (z + (0,0,t)) = F z + t * F (0,0,1) := by
  have h : (0,0,t) = t • ((0,0,1) : Coordinates Y) := by ext <;> simp
  rw [map_add,h,map_smul,smul_eq_mul]

/-- A finite feasible transport is generated from all feasible transport dual
potentials. There is no assumed LP duality or optimal-coupling premise. -/
theorem exists_plan_of_dual (d : Y × Y → ℝ) (p q : Row Y) (c : ℝ)
    (hd : ∀ a b : Y → ℝ, (∀ i j, a i + b j ≤ d (i,j)) →
      p.expect a + q.expect b ≤ c) :
    ∃ g : Row (Y × Y),
      (∀ i, ∑ j, g.mass (i,j) = p.mass i) ∧
      (∀ j, ∑ i, g.mass (i,j) = q.mass j) ∧ g.expect d ≤ c := by
  classical
  rw [← mem_epigraph_iff]
  by_contra hnot
  obtain ⟨F,u,hpoint,hsep⟩ := geometric_hahn_banach_point_closed
    (epigraph_convex d) (epigraph_closed d) hnot
  let α : ℝ := F (0,0,1)
  let a : Y → ℝ := fun i => F (Pi.single i 1,0,0)
  let b : Y → ℝ := fun j => F (0,Pi.single j 1,0)
  let g₀ := product p q
  have hg₀ : u < F (summary d g₀.mass) := by
    have h := hsep _ (summary_mem_epigraph d g₀ (t := 0) le_rfl)
    change u < F (summary d g₀.mass + 0) at h
    simpa using h
  have hα0 : 0 ≤ α := by
    by_contra hn
    have hα : α < 0 := lt_of_not_ge hn
    let t : ℝ := (F (summary d g₀.mass)-u+1)/(-α)
    have ht : 0 ≤ t := div_nonneg (by linarith) (by linarith)
    have htα : t * α = -(F (summary d g₀.mass)-u+1) := by
      dsimp [t]
      field_simp [ne_of_lt hα]
      <;> ring
    have h := hsep _ (summary_mem_epigraph d g₀ ht)
    rw [functional_vertical] at h
    change u < F (summary d g₀.mass) + t * α at h
    rw [htα] at h
    linarith
  have hpoint' : p.expect a + q.expect b + c*α < u := by
    rw [functional_decomposition] at hpoint
    simpa [Row.expect,a,b,α] using hpoint
  have hg₀' : u < p.expect a + q.expect b + g₀.expect d*α := by
    rw [show summary d g₀.mass = (p.mass,q.mass,g₀.expect d) from product_summary d p q,
      functional_decomposition] at hg₀
    simpa [Row.expect,a,b,α] using hg₀
  have hα : 0 < α := by
    by_contra hn
    have hz : α = 0 := le_antisymm (le_of_not_gt hn) hα0
    rw [hz] at hpoint' hg₀'
    linarith
  let A : Y → ℝ := fun i => (u/2-a i)/α
  let B : Y → ℝ := fun j => (u/2-b j)/α
  have hAB : ∀ i j, A i + B j ≤ d (i,j) := by
    intro i j
    have h := hsep _ (summary_mem_epigraph d (Row.pure (i,j)) (t := 0) le_rfl)
    change u < F (summary d (Row.pure (i,j)).mass + 0) at h
    rw [add_zero,pure_summary] at h
    rw [functional_decomposition] at h
    simp only [Pi.single_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',
      Finset.mem_univ,ite_true] at h
    change u < a i + b j + d (i,j) * α at h
    dsimp [A,B]
    rw [← add_div]
    apply (div_le_iff₀ hα).2
    linarith
  have hp : α * p.expect A = u/2-p.expect a := by
    rw [Row.expect,Finset.mul_sum]
    calc
      ∑ i, α * (p.mass i * A i) = ∑ i, p.mass i * (u/2-a i) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [A]
        field_simp [hα.ne']
        <;> ring
      _ = _ := by simp [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,p.total,Row.expect]
  have hq : α * q.expect B = u/2-q.expect b := by
    rw [Row.expect,Finset.mul_sum]
    calc
      ∑ j, α * (q.mass j * B j) = ∑ j, q.mass j * (u/2-b j) := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp [B]
        field_simp [hα.ne']
        <;> ring
      _ = _ := by simp [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,q.total,Row.expect]
  have hh := mul_le_mul_of_nonneg_left (hd A B hAB) hα.le
  nlinarith

end PermanssonResearch.Probability.FiniteTransport
