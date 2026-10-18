import PermanssonResearch.Probability.FiniteRowCoupling

/-! Explicit normalized finite action/world/update joint-row composition.
Each conditional transport row is retained until its dependencies have been
consumed. Weighted costs are derived by repeated expectation, not assumed. -/

namespace PermanssonResearch.Perturbation.FiniteSequential
open ActionTrace PermanssonResearch.Probability
open scoped NNReal
noncomputable section
variable {S X A : Type*} [Fintype S] [Fintype X] [Fintype A]

def inducedRow (α : Row A) (P : A → Row X) (U : A → X → Row S) : Row (S × X) :=
  α.bind (fun a => (P a).bind (fun x => (U a x).map (fun s => (s,x))))

def sequentialCoupling {α β : Row A} {P Q : A → Row X} {U V : A → X → Row S}
    (gA : RowCoupling α β)
    (gP : ∀ ab : A × A,RowCoupling (P ab.1) (Q ab.2))
    (gU : ∀ (ab : A × A) (xx : X × X),RowCoupling (U ab.1 xx.1) (V ab.2 xx.2)) :
    RowCoupling (inducedRow α P U) (inducedRow β Q V) :=
  gA.bind
    (fun a => (P a).bind (fun x => (U a x).map (fun s => (s,x))))
    (fun a => (Q a).bind (fun x => (V a x).map (fun s => (s,x))))
    (fun ab => (gP ab).bind
      (fun x => (U ab.1 x).map (fun s => (s,x)))
      (fun x => (V ab.2 x).map (fun s => (s,x)))
      (fun xx => (gU ab xx).mapPair (fun s => (s,xx.1)) (fun s => (s,xx.2))))

theorem sequential_expect {α β : Row A} {P Q : A → Row X} {U V : A → X → Row S}
    (gA : RowCoupling α β)
    (gP : ∀ ab : A × A,RowCoupling (P ab.1) (Q ab.2))
    (gU : ∀ (ab : A × A) (xx : X × X),RowCoupling (U ab.1 xx.1) (V ab.2 xx.2))
    (F : (S × X) × (S × X) → ℝ) :
    (sequentialCoupling gA gP gU).joint.expect F=
      gA.joint.expect (fun ab => (gP ab).joint.expect (fun xx =>
        (gU ab xx).joint.expect (fun ss => F ((ss.1,xx.1),(ss.2,xx.2))))) := by
  simp only [sequentialCoupling,RowCoupling.bind,RowCoupling.mapPair,
    Row.expect_bind,Row.expect_map]

variable [PseudoMetricSpace S] [PseudoMetricSpace X] [PseudoMetricSpace A]

def weightedDistance (a b : ℝ≥0) (y z : S × X) : ℝ :=
  (a:ℝ)*dist y.1 z.1+(b:ℝ)*dist y.2 z.2

def weightedMetric (a b : ℝ≥0) : PseudoMetricSpace (S × X) where
  dist := weightedDistance a b
  dist_self y := by simp [weightedDistance]
  dist_comm y z := by simp [weightedDistance,dist_comm]
  dist_triangle y z w := by
    have hs := mul_le_mul_of_nonneg_left (dist_triangle y.1 z.1 w.1) a.property
    have hx := mul_le_mul_of_nonneg_left (dist_triangle y.2 z.2 w.2) b.property
    unfold weightedDistance
    calc
      _ ≤ (a:ℝ)*(dist y.1 z.1+dist z.1 w.1)+(b:ℝ)*(dist y.2 z.2+dist z.2 w.2) :=
        add_le_add hs hx
      _ = _ := by ring

def metricBudget (a b LPa LUa LUx : ℝ≥0) (δα δP δU : ℝ) : ℝ :=
  (a:ℝ)*δU+((b:ℝ)+(a:ℝ)*(LUx:ℝ))*δP+
    ((a:ℝ)*(LUa:ℝ)+((b:ℝ)+(a:ℝ)*(LUx:ℝ))*(LPa:ℝ))*δα

theorem expect_affine {Y : Type*} [Fintype Y] (p : Row Y) (u v : ℝ) (f : Y → ℝ) :
    p.expect (fun y => u+v*f y)=u+v*p.expect f := by
  simp only [Row.expect_add,Row.expect_mul,Row.expect_const]

/-- The boxed typed metric budget from actual normalized conditional plans. -/
theorem sequential_weighted_cost {α β : Row A} {P Q : A → Row X} {U V : A → X → Row S}
    (gA : RowCoupling α β)
    (gP : ∀ ab : A × A,RowCoupling (P ab.1) (Q ab.2))
    (gU : ∀ (ab : A × A) (xx : X × X),RowCoupling (U ab.1 xx.1) (V ab.2 xx.2))
    (a b LPa LUa LUx : ℝ≥0) (δα δP δU : ℝ)
    (hA : gA.joint.expect (fun ab => dist ab.1 ab.2)≤δα)
    (hP : ∀ ab,(gP ab).joint.expect (fun xx => dist xx.1 xx.2)≤δP+(LPa:ℝ)*dist ab.1 ab.2)
    (hU : ∀ ab xx,(gU ab xx).joint.expect (fun ss => dist ss.1 ss.2)≤
      δU+(LUa:ℝ)*dist ab.1 ab.2+(LUx:ℝ)*dist xx.1 xx.2) :
    (sequentialCoupling gA gP gU).joint.expect
      (fun yy => weightedDistance a b yy.1 yy.2)≤metricBudget a b LPa LUa LUx δα δP δU := by
  let B : ℝ := (b:ℝ)+(a:ℝ)*(LUx:ℝ)
  let C : ℝ := (a:ℝ)*(LUa:ℝ)+B*(LPa:ℝ)
  have hB : 0≤B := add_nonneg b.property (mul_nonneg a.property LUx.property)
  have hC : 0≤C := add_nonneg (mul_nonneg a.property LUa.property) (mul_nonneg hB LPa.property)
  have hs (ab : A × A) (xx : X × X) :
      (gU ab xx).joint.expect (fun ss => weightedDistance a b (ss.1,xx.1) (ss.2,xx.2))≤
        ((a:ℝ)*δU+(a:ℝ)*(LUa:ℝ)*dist ab.1 ab.2)+B*dist xx.1 xx.2 := by
    simp only [weightedDistance,Row.expect_add,Row.expect_mul,Row.expect_const]
    have hh := mul_le_mul_of_nonneg_left (hU ab xx) a.property
    calc
      _ ≤ (a:ℝ)*(δU+(LUa:ℝ)*dist ab.1 ab.2+(LUx:ℝ)*dist xx.1 xx.2)+
          (b:ℝ)*dist xx.1 xx.2 := add_le_add hh le_rfl
      _ = _ := by dsimp [B]; ring
  have hx (ab : A × A) :
      (gP ab).joint.expect (fun xx => (gU ab xx).joint.expect
        (fun ss => weightedDistance a b (ss.1,xx.1) (ss.2,xx.2)))≤
      ((a:ℝ)*δU+B*δP)+C*dist ab.1 ab.2 := by
    calc
      _ ≤ (gP ab).joint.expect (fun xx =>
          ((a:ℝ)*δU+(a:ℝ)*(LUa:ℝ)*dist ab.1 ab.2)+B*dist xx.1 xx.2) :=
        (gP ab).joint.expect_mono (hs ab)
      _ = ((a:ℝ)*δU+(a:ℝ)*(LUa:ℝ)*dist ab.1 ab.2)+
          B*(gP ab).joint.expect (fun xx => dist xx.1 xx.2) := expect_affine _ _ _ _
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left (hP ab) hB
        calc
          _ ≤ ((a:ℝ)*δU+(a:ℝ)*(LUa:ℝ)*dist ab.1 ab.2)+
              B*(δP+(LPa:ℝ)*dist ab.1 ab.2) := add_le_add le_rfl hh
          _ = _ := by dsimp [C]; ring
  rw [sequential_expect]
  calc
    _ ≤ gA.joint.expect (fun ab => ((a:ℝ)*δU+B*δP)+C*dist ab.1 ab.2) :=
      gA.joint.expect_mono hx
    _ = ((a:ℝ)*δU+B*δP)+C*gA.joint.expect (fun ab => dist ab.1 ab.2) := expect_affine _ _ _ _
    _ ≤ metricBudget a b LPa LUa LUx δα δP δU := by
      have hh := mul_le_mul_of_nonneg_left hA hC
      change _ ≤ (a:ℝ)*δU+B*δP+C*δα
      exact add_le_add le_rfl hh

end
end PermanssonResearch.Perturbation.FiniteSequential
