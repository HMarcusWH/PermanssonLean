import PermanssonResearch.Perturbation.FiniteTypedRows

/-! Typed metric errors produce actual sequential transport plans and the
boxed weighted induced-row bound. All reference Lipschitz assumptions concern
the original primitive kernels on every input, including off-graph rows. -/

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace PermanssonResearch.Perturbation.FiniteSequential
open ActionTrace PermanssonResearch.Probability PermanssonLean
noncomputable section
variable {S X A : Type*} [Fintype S] [Fintype X] [Fintype A]
  [Nonempty S] [Nonempty X] [Nonempty A]
  [PseudoMetricSpace S] [PseudoMetricSpace X] [PseudoMetricSpace A]
  [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
  [MeasurableSingletonClass S] [MeasurableSingletonClass X] [MeasurableSingletonClass A]

structure PrimitiveMetricBounds (M N : StrategicWorldModel S X A) where
  actionError : ℝ
  worldError : ℝ
  updateError : ℝ
  worldAction : ℝ≥0
  updateAction : ℝ≥0
  updateWorld : ℝ≥0
  action : ∀ y,W1DualLE (M.generator.action y) (N.generator.action y) actionError
  world : ∀ y c,W1DualLE (M.world (y,c)) (N.world (y,c)) worldError
  update : ∀ y c x,W1DualLE (M.generator.update ((y,c),x))
    (N.generator.update ((y,c),x)) updateError
  referenceWorldAction : ∀ y c d,W1DualLE (N.world (y,c)) (N.world (y,d))
    ((worldAction:ℝ)*dist c d)
  referenceUpdateAction : ∀ y c d x,W1DualLE (N.generator.update ((y,c),x))
    (N.generator.update ((y,d),x)) ((updateAction:ℝ)*dist c d)
  referenceUpdateWorld : ∀ y c x z,W1DualLE (N.generator.update ((y,c),x))
    (N.generator.update ((y,c),z)) ((updateWorld:ℝ)*dist x z)

def PrimitiveMetricBounds.budget {M N : StrategicWorldModel S X A}
    (D : PrimitiveMetricBounds M N) (a b : ℝ≥0) : ℝ :=
  metricBudget a b D.worldAction D.updateAction D.updateWorld
    D.actionError D.worldError D.updateError

/-- Finite KR constructs every conditional coupling. The resulting joint
row's exact marginals are the original typed induced rows. -/
theorem PrimitiveMetricBounds.exists_sequential_plan {M N : StrategicWorldModel S X A}
    (D : PrimitiveMetricBounds M N) (a b : ℝ≥0) (y : JointState S X) :
    ∃ g : RowCoupling (typedRow M y) (typedRow N y),
      g.joint.expect (fun yy => weightedDistance a b yy.1 yy.2)≤D.budget a b := by
  have hA : W1DualLE (actionRow M y).measure (actionRow N y).measure D.actionError := by
    simpa only [actionRow_measure] using D.action y
  obtain ⟨gA,hgA⟩ := RowCoupling.exists_of_w1DualLE hA
  have hP : ∀ ab : A × A,∃ g : RowCoupling (worldRow M y ab.1) (worldRow N y ab.2),
      g.joint.expect (fun xx => dist xx.1 xx.2)≤D.worldError+(D.worldAction:ℝ)*dist ab.1 ab.2 := by
    intro ab
    have hh := (D.world y ab.1).trans (D.referenceWorldAction y ab.1 ab.2)
    apply RowCoupling.exists_of_w1DualLE
    simpa only [worldRow_measure] using hh
  choose gP hgP using hP
  have hU : ∀ (ab : A × A) (xx : X × X),
      ∃ g : RowCoupling (updateRow M y ab.1 xx.1) (updateRow N y ab.2 xx.2),
      g.joint.expect (fun ss => dist ss.1 ss.2)≤
        D.updateError+(D.updateAction:ℝ)*dist ab.1 ab.2+(D.updateWorld:ℝ)*dist xx.1 xx.2 := by
    intro ab xx
    have hh := ((D.update y ab.1 xx.1).trans
      (D.referenceUpdateAction y ab.1 ab.2 xx.1)).trans
      (D.referenceUpdateWorld y ab.2 xx.1 xx.2)
    apply RowCoupling.exists_of_w1DualLE
    simpa only [updateRow_measure] using hh
  choose gU hgU using hU
  exact ⟨sequentialCoupling gA gP gU,
    sequential_weighted_cost gA gP gU a b D.worldAction D.updateAction D.updateWorld
      D.actionError D.worldError D.updateError hgA hgP hgU⟩

/-- Actual normalized coupling of the unchanged original induced measures,
in the explicitly declared weighted metric. -/
theorem PrimitiveMetricBounds.exists_weighted_coupling {M N : StrategicWorldModel S X A}
    (D : PrimitiveMetricBounds M N) (a b : ℝ≥0) (y : JointState S X) :
    letI : PseudoMetricSpace (JointState S X) := weightedMetric a b
    ∃ γ : IntegrableCoupling (M.inducedKernel y) (N.inducedKernel y),γ.cost≤D.budget a b := by
  letI : PseudoMetricSpace (JointState S X) := weightedMetric a b
  obtain ⟨g,hg⟩ := D.exists_sequential_plan a b y
  have hh : ∃ γ : IntegrableCoupling (typedRow M y).measure (typedRow N y).measure,
      γ.cost≤D.budget a b := by
    refine ⟨g.toCoupling,?_⟩
    rw [RowCoupling.toCoupling_cost]
    exact hg
  rw [typedRow_measure M y,typedRow_measure N y] at hh
  exact hh

theorem PrimitiveMetricBounds.weighted_induced_bound {M N : StrategicWorldModel S X A}
    (D : PrimitiveMetricBounds M N) (a b : ℝ≥0) (y : JointState S X) :
    letI : PseudoMetricSpace (JointState S X) := weightedMetric a b
    W1DualLE (M.inducedKernel y) (N.inducedKernel y) (D.budget a b) := by
  letI : PseudoMetricSpace (JointState S X) := weightedMetric a b
  obtain ⟨g,hg⟩ := D.exists_weighted_coupling a b y
  exact g.dual_bound.mono hg

theorem productDist_le_weighted (a b : ℝ≥0) (ha : 0<(a:ℝ)) (hb : 0<(b:ℝ))
    (y z : S × X) : dist y z≤weightedDistance a b y z/min (a:ℝ) (b:ℝ) := by
  apply (le_div_iff₀ (lt_min ha hb)).mpr
  rw [Prod.dist_eq]
  by_cases hs : dist y.1 z.1≤dist y.2 z.2
  · rw [max_eq_right hs]
    have hh := mul_le_mul_of_nonneg_right (min_le_right (a:ℝ) (b:ℝ))
      (dist_nonneg : 0≤dist y.2 z.2)
    have hp := mul_nonneg a.property (dist_nonneg : 0≤dist y.1 z.1)
    unfold weightedDistance
    calc
      _ = min (a:ℝ) (b:ℝ)*dist y.2 z.2 := mul_comm _ _
      _ ≤ (b:ℝ)*dist y.2 z.2 := hh
      _ ≤ _ := le_add_of_nonneg_left hp
  · rw [max_eq_left (le_of_not_ge hs)]
    have hh := mul_le_mul_of_nonneg_right (min_le_left (a:ℝ) (b:ℝ))
      (dist_nonneg : 0≤dist y.1 z.1)
    have hp := mul_nonneg b.property (dist_nonneg : 0≤dist y.2 z.2)
    unfold weightedDistance
    calc
      _ = min (a:ℝ) (b:ℝ)*dist y.1 z.1 := mul_comm _ _
      _ ≤ (a:ℝ)*dist y.1 z.1 := hh
      _ ≤ _ := le_add_of_nonneg_right hp

/-- Honest conversion to the frozen typed API's product-max metric. The
weight factor is retained rather than silently replacing the ambient metric. -/
theorem PrimitiveMetricBounds.original_induced_bound {M N : StrategicWorldModel S X A}
    (D : PrimitiveMetricBounds M N) (a b : ℝ≥0) (ha : 0<(a:ℝ)) (hb : 0<(b:ℝ))
    (y : JointState S X) :
    W1DualLE (M.inducedKernel y) (N.inducedKernel y) (D.budget a b/min (a:ℝ) (b:ℝ)) := by
  obtain ⟨g,hg⟩ := D.exists_sequential_plan a b y
  have hc : g.toCoupling.cost≤D.budget a b/min (a:ℝ) (b:ℝ) := by
    rw [RowCoupling.toCoupling_cost]
    calc
      _ ≤ g.joint.expect (fun yy => weightedDistance a b yy.1 yy.2/min (a:ℝ) (b:ℝ)) :=
        g.joint.expect_mono (fun yy => productDist_le_weighted a b ha hb yy.1 yy.2)
      _ = g.joint.expect (fun yy => weightedDistance a b yy.1 yy.2)/min (a:ℝ) (b:ℝ) := by
        simp only [Row.expect,div_eq_mul_inv,Finset.sum_mul,mul_assoc]
      _ ≤ _ := div_le_div_of_nonneg_right hg (lt_min ha hb).le
  have hh := g.toCoupling.dual_bound.mono hc
  simpa only [typedRow_measure] using hh

end
end PermanssonResearch.Perturbation.FiniteSequential
