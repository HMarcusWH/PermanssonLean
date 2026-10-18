import PermanssonResearch.Perturbation.FinitePrimitiveMetric
import PermanssonResearch.Perturbation.DobrushinContraction

/-! Same-model primitive Lipschitz bounds derive actual row couplings and
the unchanged all-laws contraction predicate. The incoming state distance
is explicit, allowing the weighted and frozen product-max metrics separately. -/

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
attribute [local instance] StrategicWorldModel.inducedKernel_isMarkov

structure StateMetricBounds (M : StrategicWorldModel S X A)
    (dold : JointState S X → JointState S X → ℝ) where
  actionState : ℝ≥0
  worldState : ℝ≥0
  updateState : ℝ≥0
  worldAction : ℝ≥0
  updateAction : ℝ≥0
  updateWorld : ℝ≥0
  action : ∀ y z,W1DualLE (M.generator.action y) (M.generator.action z) ((actionState:ℝ)*dold y z)
  world : ∀ y z c,W1DualLE (M.world (y,c)) (M.world (z,c)) ((worldState:ℝ)*dold y z)
  update : ∀ y z c x,W1DualLE (M.generator.update ((y,c),x))
    (M.generator.update ((z,c),x)) ((updateState:ℝ)*dold y z)
  world_action : ∀ y c d,W1DualLE (M.world (y,c)) (M.world (y,d)) ((worldAction:ℝ)*dist c d)
  update_action : ∀ y c d x,W1DualLE (M.generator.update ((y,c),x))
    (M.generator.update ((y,d),x)) ((updateAction:ℝ)*dist c d)
  update_world : ∀ y c x z,W1DualLE (M.generator.update ((y,c),x))
    (M.generator.update ((y,c),z)) ((updateWorld:ℝ)*dist x z)

def StateMetricBounds.factor {M : StrategicWorldModel S X A} {dold}
    (D : StateMetricBounds M dold) (a b : ℝ≥0) : ℝ :=
  metricBudget a b D.worldAction D.updateAction D.updateWorld
    D.actionState D.worldState D.updateState

theorem StateMetricBounds.factor_nonneg {M : StrategicWorldModel S X A} {dold}
    (D : StateMetricBounds M dold) (a b : ℝ≥0) : 0≤D.factor a b := by
  unfold StateMetricBounds.factor metricBudget
  positivity

theorem StateMetricBounds.exists_sequential_plan {M : StrategicWorldModel S X A} {dold}
    (D : StateMetricBounds M dold) (a b : ℝ≥0) (y z : JointState S X) :
    ∃ g : RowCoupling (typedRow M y) (typedRow M z),
      g.joint.expect (fun yy => weightedDistance a b yy.1 yy.2)≤D.factor a b*dold y z := by
  have hA : W1DualLE (actionRow M y).measure (actionRow M z).measure
      ((D.actionState:ℝ)*dold y z) := by simpa only [actionRow_measure] using D.action y z
  obtain ⟨gA,hgA⟩ := RowCoupling.exists_of_w1DualLE hA
  have hP : ∀ ab : A × A,∃ g : RowCoupling (worldRow M y ab.1) (worldRow M z ab.2),
      g.joint.expect (fun xx => dist xx.1 xx.2)≤
        (D.worldState:ℝ)*dold y z+(D.worldAction:ℝ)*dist ab.1 ab.2 := by
    intro ab
    apply RowCoupling.exists_of_w1DualLE
    simpa only [worldRow_measure] using (D.world y z ab.1).trans (D.world_action z ab.1 ab.2)
  choose gP hgP using hP
  have hU : ∀ (ab : A × A) (xx : X × X),
      ∃ g : RowCoupling (updateRow M y ab.1 xx.1) (updateRow M z ab.2 xx.2),
      g.joint.expect (fun ss => dist ss.1 ss.2)≤
        (D.updateState:ℝ)*dold y z+(D.updateAction:ℝ)*dist ab.1 ab.2+
        (D.updateWorld:ℝ)*dist xx.1 xx.2 := by
    intro ab xx
    apply RowCoupling.exists_of_w1DualLE
    simpa only [updateRow_measure] using ((D.update y z ab.1 xx.1).trans
      (D.update_action z ab.1 ab.2 xx.1)).trans (D.update_world z ab.2 xx.1 xx.2)
  choose gU hgU using hU
  refine ⟨sequentialCoupling gA gP gU,?_⟩
  calc
    _ ≤ metricBudget a b D.worldAction D.updateAction D.updateWorld
        ((D.actionState:ℝ)*dold y z) ((D.worldState:ℝ)*dold y z) ((D.updateState:ℝ)*dold y z) :=
      sequential_weighted_cost gA gP gU a b D.worldAction D.updateAction D.updateWorld
        _ _ _ hgA hgP hgU
    _ = D.factor a b*dold y z := by unfold StateMetricBounds.factor metricBudget; ring

theorem StateMetricBounds.exists_weighted_coupling {M : StrategicWorldModel S X A} {dold}
    (D : StateMetricBounds M dold) (a b : ℝ≥0) (y z : JointState S X) :
    letI : PseudoMetricSpace (JointState S X) := weightedMetric a b
    ∃ γ : IntegrableCoupling (M.inducedKernel y) (M.inducedKernel z),γ.cost≤D.factor a b*dold y z := by
  letI : PseudoMetricSpace (JointState S X) := weightedMetric a b
  obtain ⟨g,hg⟩ := D.exists_sequential_plan a b y z
  have hh : ∃ γ : IntegrableCoupling (typedRow M y).measure (typedRow M z).measure,
      γ.cost≤D.factor a b*dold y z := by
    refine ⟨g.toCoupling,?_⟩
    rw [RowCoupling.toCoupling_cost]
    exact hg
  rw [typedRow_measure M y,typedRow_measure M z] at hh
  exact hh

theorem StateMetricBounds.weighted_isW1Contraction {M : StrategicWorldModel S X A}
    (a b : ℝ≥0) (D : StateMetricBounds M (weightedDistance a b)) :
    letI : PseudoMetricSpace (JointState S X) := weightedMetric a b
    IsW1Contraction M.inducedKernel (D.factor a b) := by
  letI : PseudoMetricSpace (JointState S X) := weightedMetric a b
  apply isW1Contraction_of_row_couplings _ (D.factor_nonneg a b)
  intro y z
  exact D.exists_weighted_coupling a b y z

/-- Product-max contraction with the explicit output metric conversion. -/
theorem StateMetricBounds.original_isW1Contraction {M : StrategicWorldModel S X A}
    (D : StateMetricBounds M (fun y z => dist y z)) (a b : ℝ≥0)
    (ha : 0<(a:ℝ)) (hb : 0<(b:ℝ)) :
    IsW1Contraction M.inducedKernel (D.factor a b/min (a:ℝ) (b:ℝ)) := by
  apply isW1Contraction_of_row_couplings _ (div_nonneg (D.factor_nonneg a b) (lt_min ha hb).le)
  intro y z
  obtain ⟨g,hg⟩ := D.exists_sequential_plan a b y z
  have hc : g.toCoupling.cost≤(D.factor a b/min (a:ℝ) (b:ℝ))*dist y z := by
    rw [RowCoupling.toCoupling_cost]
    calc
      _ ≤ g.joint.expect (fun yy => weightedDistance a b yy.1 yy.2/min (a:ℝ) (b:ℝ)) :=
        g.joint.expect_mono (fun yy => productDist_le_weighted a b ha hb yy.1 yy.2)
      _ = g.joint.expect (fun yy => weightedDistance a b yy.1 yy.2)/min (a:ℝ) (b:ℝ) := by
        simp only [Row.expect,div_eq_mul_inv,Finset.sum_mul,mul_assoc]
      _ ≤ (D.factor a b*dist y z)/min (a:ℝ) (b:ℝ) :=
        div_le_div_of_nonneg_right hg (lt_min ha hb).le
      _ = _ := by ring
  have hh : ∃ γ : IntegrableCoupling (typedRow M y).measure (typedRow M z).measure,
      γ.cost≤(D.factor a b/min (a:ℝ) (b:ℝ))*dist y z := ⟨g.toCoupling,hc⟩
  rw [typedRow_measure M y,typedRow_measure M z] at hh
  exact hh

end
end PermanssonResearch.Perturbation.FiniteSequential
