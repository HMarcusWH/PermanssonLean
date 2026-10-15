import PermanssonResearch.Perturbation.PrimitiveModelPair
import PermanssonLean.Probability.CommonPartKernel
import PermanssonLean.Probability.FinitePrefixTV
import Mathlib.Tactic

/-!
# A2.1 — primitive model error induces a bounded joint Markov-kernel error

We compare the actual sampled `action → world → strategic update` kernels,
rather than treating an arbitrary joint matrix as a valid typed primitive
replacement. Every comparison is global on the declared kernel input types,
so intervention-reachable states are included, not merely baseline support.

The proof constructs a common dominated history *subkernel*. It does not
postulate independent sampling of the three stages or a probabilistic
coupling. The additive bound follows conservatively from common mass.
This module deliberately does NOT assert that finite-horizon error preserves
exact invariance or a generalized Permansson-regime certificate.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch
namespace Perturbation

universe uS uX uA

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace.CountableOrCountablyGenerated
  (PermanssonLean.JointState S X) A]
variable [MeasurableSpace.CountableOrCountablyGenerated
  (PermanssonLean.WorldInput S X A) X]
variable [MeasurableSpace.CountableOrCountablyGenerated
  (PermanssonLean.UpdateInput S X A) S]

private theorem compProd_mono
    {I B C : Type*} [MeasurableSpace I] [MeasurableSpace B]
    [MeasurableSpace C]
    {k k' : Kernel I B} {l l' : Kernel (I × B) C}
    [IsSFiniteKernel k] [IsSFiniteKernel k']
    [IsSFiniteKernel l] [IsSFiniteKernel l']
    (hk : k ≤ k') (hl : l ≤ l') :
    k ⊗ₖ l ≤ k' ⊗ₖ l' := by
  intro i
  apply Measure.le_iff.mpr
  intro E hE
  rw [Kernel.compProd_apply hE k l i, Kernel.compProd_apply hE k' l' i]
  exact lintegral_mono' (hk i) (fun b => hl (i, b) _)

private theorem compProd_mass_ge
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

/-- Measurable common action subkernel, dominated by both action laws. -/
noncomputable def commonAction
    (M N : PermanssonLean.StrategicWorldModel S X A) :
    Kernel (PermanssonLean.JointState S X) A :=
  PermanssonLean.ProbabilitySupport.commonPartKernel
    M.generator.action N.generator.action

/-- Measurable common world subkernel, dominated by both world laws. -/
noncomputable def commonWorld
    (M N : PermanssonLean.StrategicWorldModel S X A) :
    Kernel (PermanssonLean.WorldInput S X A) X :=
  PermanssonLean.ProbabilitySupport.commonPartKernel
    M.world N.world

/-- Measurable common update law on the actual reassociated history. -/
noncomputable def commonUpdate
    (M N : PermanssonLean.StrategicWorldModel S X A) :
    Kernel (PermanssonLean.JointState S X × (A × X)) S :=
  (PermanssonLean.ProbabilitySupport.commonPartKernel
    M.generator.update N.generator.update).comap
      (PermanssonLean.StrategicWorldModel.updateInputReassoc
        (S := S) (X := X) (A := A))
      (PermanssonLean.StrategicWorldModel.measurable_updateInputReassoc
        (S := S) (X := X) (A := A))

/-- The three common primitive kernels are composed in the original order.
This is a finite sub-Markov kernel on the canonical joint state. -/
noncomputable def commonInducedKernel
    (M N : PermanssonLean.StrategicWorldModel S X A) :
    Kernel (PermanssonLean.JointState S X)
      (PermanssonLean.JointState S X) :=
  ((commonAction M N ⊗ₖ commonWorld M N) ⊗ₖ commonUpdate M N).map
    (fun z : ((A × X) × S) => (z.2, z.1.2))

theorem commonInducedKernel_le_left
    (M N : PermanssonLean.StrategicWorldModel S X A) :
    commonInducedKernel M N ≤ M.inducedKernel := by
  unfold commonInducedKernel
  apply PermanssonLean.ProbabilitySupport.kernelMap_mono
  · apply compProd_mono
    · apply compProd_mono
      · exact PermanssonLean.ProbabilitySupport.commonPartKernel_le_left
          M.generator.action N.generator.action
      · exact PermanssonLean.ProbabilitySupport.commonPartKernel_le_left
          M.world N.world
    · intro z
      exact PermanssonLean.ProbabilitySupport.commonPartKernel_le_left
        M.generator.update N.generator.update
        (PermanssonLean.StrategicWorldModel.updateInputReassoc z)
  · fun_prop

theorem commonInducedKernel_le_right
    (M N : PermanssonLean.StrategicWorldModel S X A) :
    commonInducedKernel M N ≤ N.inducedKernel := by
  unfold commonInducedKernel
  apply PermanssonLean.ProbabilitySupport.kernelMap_mono
  · apply compProd_mono
    · apply compProd_mono
      · exact PermanssonLean.ProbabilitySupport.commonPartKernel_le_right
          M.generator.action N.generator.action
      · exact PermanssonLean.ProbabilitySupport.commonPartKernel_le_right
          M.world N.world
    · intro z
      exact PermanssonLean.ProbabilitySupport.commonPartKernel_le_right
        M.generator.update N.generator.update
        (PermanssonLean.StrategicWorldModel.updateInputReassoc z)
  · fun_prop

private theorem commonInducedKernel_mass_ge
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
    intro z
    have h := PermanssonLean.ProbabilitySupport.one_sub_le_commonPartKernel_real_univ_of_uniformTV
      M.generator.action N.generator.action ha z
    exact (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).2 h
  have hP : ∀ z, qp ≤ commonWorld M N z Set.univ := by
    intro z
    have h := PermanssonLean.ProbabilitySupport.one_sub_le_commonPartKernel_real_univ_of_uniformTV
      M.world N.world hp z
    exact (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).2 h
  have hU : ∀ z, qu ≤ commonUpdate M N z Set.univ := by
    intro z
    have h := PermanssonLean.ProbabilitySupport.one_sub_le_commonPartKernel_real_univ_of_uniformTV
      M.generator.update N.generator.update hu
      (PermanssonLean.StrategicWorldModel.updateInputReassoc z)
    exact (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).2 h
  have hAP : qp * commonAction M N y Set.univ ≤
      (commonAction M N ⊗ₖ commonWorld M N) y Set.univ :=
    compProd_mass_ge _ _ qp hP y
  have hAPU : qu * (commonAction M N ⊗ₖ commonWorld M N) y Set.univ ≤
      ((commonAction M N ⊗ₖ commonWorld M N) ⊗ₖ commonUpdate M N) y Set.univ :=
    compProd_mass_ge _ _ qu hU y
  have hmap : commonInducedKernel M N y Set.univ =
      ((commonAction M N ⊗ₖ commonWorld M N) ⊗ₖ commonUpdate M N)
        y Set.univ := by
    unfold commonInducedKernel
    rw [Kernel.map_apply _ (by fun_prop)]
    simp
  rw [hmap]
  calc
    qu * qp * qa = qu * (qp * qa) := by ac_rfl
    _ ≤ qu * (qp * commonAction M N y Set.univ) := by
      gcongr
      exact hA y
    _ ≤ qu * (commonAction M N ⊗ₖ commonWorld M N) y Set.univ := by
      gcongr
    _ ≤ _ := hAPU

/-- A2 Proposition 5.5: actual primitive α/P/U errors bound the
canonical induced kernel, in the source's event-supremum TV convention.
The elementary *additive* statement is the required A2 release theorem.
No assumption of primitive-stage independence is made. -/
theorem inducedKernel_tv_le_primitive_sum
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
      M.generator.update N.generator.update δU) :
    PermanssonLean.ProbabilitySupport.HasUniformEventTVBound
      M.inducedKernel N.inducedKernel
      (min 1 (δα + δP + δU)) := by
  let δ := min 1 (δα + δP + δU)
  intro y
  have hsub := commonInducedKernel_mass_ge M N
    ha0 ha1 hp0 hp1 hu0 hu1 ha hp hu y
  have hfinite : commonInducedKernel M N y Set.univ ≠ ⊤ := by
    have hle := commonInducedKernel_le_left M N y Set.univ
    exact ne_top_of_le_ne_top (by simp : M.inducedKernel y Set.univ ≠ ⊤) hle
  have hreal :
      (1 - δU) * (1 - δP) * (1 - δα) ≤
        (commonInducedKernel M N y).real Set.univ := by
    have hu' : 0 ≤ 1 - δU := by linarith
    have hp' : 0 ≤ 1 - δP := by linarith
    have ha' : 0 ≤ 1 - δα := by linarith
    have hconv : ENNReal.ofReal ((1 - δU) * (1 - δP) * (1 - δα)) =
        ENNReal.ofReal (1 - δU) * ENNReal.ofReal (1 - δP) *
          ENNReal.ofReal (1 - δα) := by
      rw [ENNReal.ofReal_mul (mul_nonneg hu' hp'),
        ENNReal.ofReal_mul hu']
    rw [← hconv] at hsub
    exact (ENNReal.ofReal_le_iff_le_toReal hfinite).1 hsub
  have hproduct :
      1 - (δα + δP + δU) ≤ (1 - δU) * (1 - δP) * (1 - δα) := by
    have ha' : 0 ≤ 1 - δα := by linarith
    have hbase : 1 - δU - δP ≤ (1 - δU) * (1 - δP) := by
      nlinarith [mul_nonneg hu0 hp0]
    have hfirst :
        (1 - δU - δP) * (1 - δα) ≤
          (1 - δU) * (1 - δP) * (1 - δα) :=
      mul_le_mul_of_nonneg_right hbase ha'
    have hsecond :
        1 - (δα + δP + δU) ≤ (1 - δU - δP) * (1 - δα) := by
      nlinarith [mul_nonneg (add_nonneg hu0 hp0) ha0]
    exact hsecond.trans hfirst
  have htv :=
    PermanssonLean.ProbabilitySupport.eventTotalVariation_le_one_sub_commonMass
      (commonInducedKernel_le_left M N y)
      (commonInducedKernel_le_right M N y)
  have hleSum :
      PermanssonLean.ProbabilitySupport.eventTotalVariation
          (M.inducedKernel y) (N.inducedKernel y) ≤ δα + δP + δU := by
    have hlarge := htv
    linarith
  have hleOne :=
    PermanssonLean.ProbabilitySupport.eventTotalVariation_le_one
      (M.inducedKernel y) (N.inducedKernel y)
  exact le_min hleOne hleSum

/-- Immediate zero-error corollary: exact agreement of every primitive
induced row entails zero event-TV distance for the *actual* joint row. -/
theorem inducedKernel_tv_zero_of_primitive_zero
    (M N : PermanssonLean.StrategicWorldModel S X A)
    (ha : PermanssonLean.ProbabilitySupport.HasUniformEventTVBound
      M.generator.action N.generator.action 0)
    (hp : PermanssonLean.ProbabilitySupport.HasUniformEventTVBound
      M.world N.world 0)
    (hu : PermanssonLean.ProbabilitySupport.HasUniformEventTVBound
      M.generator.update N.generator.update 0)
    (y : PermanssonLean.JointState S X) :
    PermanssonLean.ProbabilitySupport.eventTotalVariation
      (M.inducedKernel y) (N.inducedKernel y) = 0 := by
  have h := inducedKernel_tv_le_primitive_sum M N
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ha hp hu y
  have hnonneg := PermanssonLean.ProbabilitySupport.eventTotalVariation_nonneg
    (M.inducedKernel y) (N.inducedKernel y)
  simp at h
  exact le_antisymm h hnonneg

end Perturbation
end PermanssonResearch
