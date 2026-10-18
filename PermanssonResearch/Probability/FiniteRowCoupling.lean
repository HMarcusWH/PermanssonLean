import PermanssonResearch.Probability.FiniteKantorovichDuality

/-! Genuine finite joint rows, their compositional marginals, and actual
integrable coupling measures. Transport plans are constructed by proved
finite KR when a primitive dual bound is supplied. -/

open MeasureTheory
namespace PermanssonResearch.Probability
open ActionTrace
noncomputable section
variable {Y Z : Type*} [Fintype Y] [Fintype Z]

theorem finiteRow_eq_of_mass (p q : Row Y) (h : ∀ y,p.mass y=q.mass y) : p=q := by
  cases p with
  | mk p hp ht =>
    cases q with
    | mk q hq hqt =>
      have he : p=q := funext h
      subst q
      rfl

theorem finiteRow_eq_of_expect (p q : Row Y) (h : ∀ f,p.expect f=q.expect f) : p=q := by
  classical
  apply finiteRow_eq_of_mass
  intro y
  have hh := h (fun z => if z=y then 1 else 0)
  simpa [Row.expect,mul_ite] using hh

structure RowCoupling (p q : Row Y) where
  joint : Row (Y × Y)
  first : joint.map Prod.fst=p
  second : joint.map Prod.snd=q

namespace RowCoupling
variable {p q : Row Y}

theorem first_expect (g : RowCoupling p q) (f : Y → ℝ) :
    g.joint.expect (fun z => f z.1)=p.expect f := by
  simpa only [Row.expect_map] using congrArg (fun r => r.expect f) g.first

theorem second_expect (g : RowCoupling p q) (f : Y → ℝ) :
    g.joint.expect (fun z => f z.2)=q.expect f := by
  simpa only [Row.expect_map] using congrArg (fun r => r.expect f) g.second

theorem first_sum (g : RowCoupling p q) (y : Y) : ∑ z,g.joint.mass (y,z)=p.mass y := by
  classical
  have hh := g.first_expect (fun z => if z=y then 1 else 0)
  simp only [Row.expect,Fintype.sum_prod_type,mul_ite,mul_one,mul_zero] at hh
  rw [Finset.sum_comm] at hh
  simpa using hh

theorem second_sum (g : RowCoupling p q) (y : Y) : ∑ z,g.joint.mass (z,y)=q.mass y := by
  classical
  have hh := g.second_expect (fun z => if z=y then 1 else 0)
  simpa [Row.expect,Fintype.sum_prod_type,mul_ite] using hh

def mapPair (g : RowCoupling p q) (f h : Y → Z) : RowCoupling (p.map f) (q.map h) where
  joint := g.joint.map (fun z => (f z.1,h z.2))
  first := by
    apply finiteRow_eq_of_expect
    intro v
    simp only [Row.expect_map]
    exact g.first_expect (fun y => v (f y))
  second := by
    apply finiteRow_eq_of_expect
    intro v
    simp only [Row.expect_map]
    exact g.second_expect (fun y => v (h y))

/-- Conditional finite joint rows compose without any assumed lifting law. -/
def bind (g : RowCoupling p q) (r s : Y → Row Z)
    (h : ∀ z : Y × Y,RowCoupling (r z.1) (s z.2)) : RowCoupling (p.bind r) (q.bind s) where
  joint := g.joint.bind (fun z => (h z).joint)
  first := by
    apply finiteRow_eq_of_expect
    intro v
    simp only [Row.expect_map,Row.expect_bind]
    calc
      _ = g.joint.expect (fun z => (r z.1).expect v) := by
        congr 1
        funext z
        exact (h z).first_expect v
      _ = _ := g.first_expect (fun y => (r y).expect v)
  second := by
    apply finiteRow_eq_of_expect
    intro v
    simp only [Row.expect_map,Row.expect_bind]
    calc
      _ = g.joint.expect (fun z => (s z.2).expect v) := by
        congr 1
        funext z
        exact (h z).second_expect v
      _ = _ := g.second_expect (fun y => (s y).expect v)

variable [PseudoMetricSpace Y] [MeasurableSpace Y] [MeasurableSingletonClass Y] [Nonempty Y]

def toCoupling (g : RowCoupling p q) : IntegrableCoupling p.measure q.measure where
  law := g.joint.measure
  isProbability := inferInstance
  first := by
    classical
    apply FiniteTransport.first_marginal
    intro y
    rw [g.first_sum]
    simp [Measure.real,Row.measure_singleton,p.nonneg]
  second := by
    classical
    apply FiniteTransport.second_marginal
    intro y
    rw [g.second_sum]
    simp [Measure.real,Row.measure_singleton,q.nonneg]
  cost_integrable := Integrable.of_finite

theorem toCoupling_cost (g : RowCoupling p q) :
    g.toCoupling.cost=g.joint.expect (fun z => dist z.1 z.2) :=
  (Row.expect_eq_integral _ _).symm

theorem exists_of_w1DualLE {δ : ℝ} (hδ : W1DualLE p.measure q.measure δ) :
    ∃ g : RowCoupling p q,g.joint.expect (fun z => dist z.1 z.2)≤δ := by
  classical
  obtain ⟨g,hgμ,hgν,hgc⟩ := FiniteTransport.exists_plan_of_w1DualLE p.measure q.measure hδ
  let h : RowCoupling p q := {
    joint := g
    first := by
      apply finiteRow_eq_of_expect
      intro f
      rw [Row.expect_map]
      simp only [Row.expect,Fintype.sum_prod_type]
      simp only [← Finset.sum_mul,hgμ]
      simp [Row.expect,Measure.real,Row.measure_singleton,p.nonneg]
    second := by
      apply finiteRow_eq_of_expect
      intro f
      rw [Row.expect_map]
      simp only [Row.expect,Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul,hgν]
      simp [Row.expect,Measure.real,Row.measure_singleton,q.nonneg] }
  exact ⟨h,hgc⟩

end RowCoupling
end
end PermanssonResearch.Probability
