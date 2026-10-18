import PermanssonResearch.Perturbation.PrimitiveTV
import PermanssonResearch.Probability.KantorovichTV

/-! Q-PRIMITIVE: retained mass multiplies through the actual ordered stages.
The frozen additive theorem remains unchanged. The hypotheses retain every
common-kernel measurability instance; independence of errors is not assumed. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace PermanssonResearch.Perturbation

universe uS uX uA

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace.CountableOrCountablyGenerated
  (PermanssonLean.JointState S X) A]
variable [MeasurableSpace.CountableOrCountablyGenerated
  (PermanssonLean.WorldInput S X A) X]
variable [MeasurableSpace.CountableOrCountablyGenerated
  (PermanssonLean.UpdateInput S X A) S]

attribute [local instance]
  PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov
  PermanssonLean.StrategicWorldModel.oneStepHistoryKernel_isMarkov
  PermanssonLean.StrategicWorldModel.reassociatedUpdate_isMarkov
  PermanssonLean.StrategicWorldModel.actionWorldKernel_isMarkov

private theorem orderedSubkernel_mass_ge
    {I B C : Type*} [MeasurableSpace I] [MeasurableSpace B]
    [MeasurableSpace C]
    (k : Kernel I B) (l : Kernel (I × B) C)
    [IsSFiniteKernel k] [IsSFiniteKernel l]
    (q : ℝ≥0∞)
    (hq : ∀ z, q ≤ l z Set.univ)
    (i : I) :
    q * k i Set.univ ≤ (k ⊗ₖ l) i Set.univ := by
  have happly : (k ⊗ₖ l) i Set.univ =
      ∫⁻ b, l (i, b) Set.univ ∂k i := by
    simpa using (Kernel.compProd_apply MeasurableSet.univ k l i)
  rw [happly]
  calc
    q * k i Set.univ = ∫⁻ _ : B, q ∂k i := by
      exact (MeasureTheory.lintegral_const q).symm
    _ ≤ ∫⁻ b, l (i, b) Set.univ ∂k i :=
      lintegral_mono (fun b => hq (i, b))

theorem primitiveCommon_mass_ge_product
    (M N : PermanssonLean.StrategicWorldModel S X A)
    {δα δP δU : ℝ}
    (ha0 : 0 ≤ δα) (ha1 : δα ≤ 1)
    (hp0 : 0 ≤ δP) (hp1 : δP ≤ 1)
    (hu0 : 0 ≤ δU) (hu1 : δU ≤ 1)
    (ha : PermanssonLean.ProbabilitySupport.HasUniformEventTVBound
      M.generator.action N.generator.action δα)
    (hp : PermanssonLean.ProbabilitySupport.HasUniformEventTVBound
      M.world N.world δP)
    (hu : PermanssonLean.ProbabilitySupport.HasUniformEventTVBound
      M.generator.update N.generator.update δU)
    (y : PermanssonLean.JointState S X) :
    ENNReal.ofReal (1 - δU) * ENNReal.ofReal (1 - δP) *
      ENNReal.ofReal (1 - δα) ≤
        commonInducedKernel M N y Set.univ := by
  let qa := ENNReal.ofReal (1 - δα)
  let qp := ENNReal.ofReal (1 - δP)
  let qu := ENNReal.ofReal (1 - δU)
  have hA : ∀ y, qa ≤ commonAction M N y Set.univ := by
    letI : IsMarkovKernel M.generator.action := M.generator.action_isMarkov
    letI : IsMarkovKernel N.generator.action := N.generator.action_isMarkov
    intro z
    have h := PermanssonLean.ProbabilitySupport.one_sub_le_commonPartKernel_real_univ_of_uniformTV
      M.generator.action N.generator.action ha z
    apply (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).2
    simpa only [commonAction, Measure.real] using h
  have hP : ∀ z, qp ≤ commonWorld M N z Set.univ := by
    letI : IsMarkovKernel M.world := M.world_isMarkov
    letI : IsMarkovKernel N.world := N.world_isMarkov
    intro z
    have h := PermanssonLean.ProbabilitySupport.one_sub_le_commonPartKernel_real_univ_of_uniformTV
      M.world N.world hp z
    apply (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).2
    simpa only [commonWorld, Measure.real] using h
  have hU : ∀ z, qu ≤ commonUpdate M N z Set.univ := by
    letI : IsMarkovKernel M.generator.update := M.generator.update_isMarkov
    letI : IsMarkovKernel N.generator.update := N.generator.update_isMarkov
    intro z
    have h := PermanssonLean.ProbabilitySupport.one_sub_le_commonPartKernel_real_univ_of_uniformTV
      M.generator.update N.generator.update hu
      (PermanssonLean.StrategicWorldModel.updateInputReassoc z)
    apply (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).2
    simpa only [commonUpdate, Kernel.comap_apply, Measure.real] using h
  have hAP : qp * commonAction M N y Set.univ ≤
      (commonAction M N ⊗ₖ commonWorld M N) y Set.univ :=
    orderedSubkernel_mass_ge _ _ qp hP y
  have hAPU : qu * (commonAction M N ⊗ₖ commonWorld M N) y Set.univ ≤
      ((commonAction M N ⊗ₖ commonWorld M N) ⊗ₖ commonUpdate M N) y Set.univ :=
    orderedSubkernel_mass_ge _ _ qu hU y
  have hmap : commonInducedKernel M N y Set.univ =
      ((commonAction M N ⊗ₖ commonWorld M N) ⊗ₖ commonUpdate M N)
        y Set.univ := by
    let phi : ((A × X) × S) → PermanssonLean.JointState S X :=
      fun z => (z.2, z.1.2)
    have hphi : Measurable phi := by
      unfold phi
      fun_prop
    change (((commonAction M N ⊗ₖ commonWorld M N) ⊗ₖ
      commonUpdate M N).map phi) y Set.univ =
      ((commonAction M N ⊗ₖ commonWorld M N) ⊗ₖ commonUpdate M N)
        y Set.univ
    rw [Kernel.map_apply' _ hphi y MeasurableSet.univ]
    simp only [Set.preimage_univ]
  rw [hmap]
  calc
    qu * qp * qa = qu * (qp * qa) := by ac_rfl
    _ ≤ qu * (qp * commonAction M N y Set.univ) := by
      gcongr
      exact hA y
    _ ≤ qu * (commonAction M N ⊗ₖ commonWorld M N) y Set.univ :=
      mul_le_mul_of_nonneg_left hAP (by exact bot_le)
    _ ≤ _ := hAPU

/-- Sharp sequential primitive product budget for the actual induced row. -/
theorem inducedKernel_tv_le_primitive_product
    (M N : PermanssonLean.StrategicWorldModel S X A)
    {δα δP δU : ℝ}
    (ha0 : 0 ≤ δα) (ha1 : δα ≤ 1)
    (hp0 : 0 ≤ δP) (hp1 : δP ≤ 1)
    (hu0 : 0 ≤ δU) (hu1 : δU ≤ 1)
    (ha : PermanssonLean.ProbabilitySupport.HasUniformEventTVBound
      M.generator.action N.generator.action δα)
    (hp : PermanssonLean.ProbabilitySupport.HasUniformEventTVBound M.world N.world δP)
    (hu : PermanssonLean.ProbabilitySupport.HasUniformEventTVBound
      M.generator.update N.generator.update δU) :
    PermanssonLean.ProbabilitySupport.HasUniformEventTVBound
      M.inducedKernel N.inducedKernel (1 - (1 - δα) * (1 - δP) * (1 - δU)) := by
  intro y
  have hsub := primitiveCommon_mass_ge_product M N
    ha0 ha1 hp0 hp1 hu0 hu1 ha hp hu y
  have hfinite : commonInducedKernel M N y Set.univ ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp : M.inducedKernel y Set.univ ≠ ⊤)
      (commonInducedKernel_le_left M N y Set.univ)
  have hu' : 0 ≤ 1 - δU := by linarith
  have hp' : 0 ≤ 1 - δP := by linarith
  have hconv : ENNReal.ofReal ((1 - δU) * (1 - δP) * (1 - δα)) =
      ENNReal.ofReal (1 - δU) * ENNReal.ofReal (1 - δP) * ENNReal.ofReal (1 - δα) := by
    rw [ENNReal.ofReal_mul (mul_nonneg hu' hp'), ENNReal.ofReal_mul hu']
  rw [← hconv] at hsub
  have hreal := (ENNReal.ofReal_le_iff_le_toReal hfinite).1 hsub
  have htv := PermanssonLean.ProbabilitySupport.eventTotalVariation_le_one_sub_commonMass
    (commonInducedKernel_le_left M N y) (commonInducedKernel_le_right M N y)
  change _ ≤ 1 - _
  have hreorder : (1 - δU) * (1 - δP) * (1 - δα) =
      (1 - δα) * (1 - δP) * (1 - δU) := by ring
  rw [hreorder] at hreal
  exact htv.trans (sub_le_sub_left hreal 1)

end PermanssonResearch.Perturbation
