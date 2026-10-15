import PermanssonResearch.RegimeExit.SwitchRouting
import PermanssonLean.Regime.Persistence
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Tactic

/-!
# C-Exit B — post-entry retention from ACTUAL stationary Markov paths

Only finite-index transition-pair identities of the original canonical
trajectory law are used. No Strong Markov theorem is assumed, and no
destination Exact-GR proof is replaced by an arrival assertion.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit

set_option autoImplicit false

open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA uH uT uK

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {H : Type uH} {T : Type uT}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H] [MeasurableSpace T]
variable [TopologicalSpace S] [TopologicalSpace X]

/-- At a fixed transition, entry into the declared region followed by
leaving it in the next step. This is a genuine two-coordinate path event. -/
def targetBadStep
    (target : RegimeSpecification (JointState S X) T)
    (n : ℕ) : Set (ℕ → JointState S X) :=
  {w | w n ∈ target.region ∧ w (n+1) ∉ target.region}

theorem targetBadStep_measurable
    (target : RegimeSpecification (JointState S X) T)
    (n : ℕ) :
    MeasurableSet (targetBadStep target n) := by
  unfold targetBadStep
  exact (target.region_measurable.preimage (measurable_pi_apply n)).inter
    (target.region_measurable.compl.preimage
      (measurable_pi_apply (n+1)))

/-- Exact invariance eliminates target-leaving transitions at each fixed
time, for every initial law (not merely an initial state in the basin).
Proof uses the original one-step pair law, not an inserted matrix. -/
theorem targetBadStep_probability_zero
    (N : StrategicWorldModel S X A)
    (target : RegimeSpecification (JointState S X) T)
    (hInv : IsExactlyInvariant N target)
    (μ : ProbabilityMeasure (JointState S X))
    (n : ℕ) :
    N.pathLaw μ.toMeasure (targetBadStep target n) = 0 := by
  let P := N.pathLaw μ.toMeasure
  let K := N.inducedKernel
  letI : IsMarkovKernel K := StrategicWorldModel.inducedKernel_isMarkov N
  let prefFn : (ℕ → JointState S X) →
      ((i : Finset.Iic n) → JointState S X) :=
    Preorder.frestrictLe n
  let last : ((i : Finset.Iic n) → JointState S X) →
      JointState S X :=
    fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩
  let A : Set ((i : Finset.Iic n) → JointState S X) :=
    last ⁻¹' target.region
  let pairFn : (ℕ → JointState S X) →
      (((i : Finset.Iic n) → JointState S X) × JointState S X) :=
    fun w => (prefFn w, w (n+1))
  have hlast : Measurable last := by dsimp [last]; fun_prop
  have hA : MeasurableSet A :=
    target.region_measurable.preimage hlast
  have hC : MeasurableSet target.regionᶜ :=
    target.region_measurable.compl
  have hp : Measurable pairFn := by dsimp [pairFn, prefFn]; fun_prop
  have hPair :
      (P.map (Preorder.frestrictLe n)) ⊗ₘ
        StrategicWorldModel.stationaryHistoryKernel K n =
      P.map (fun w => (Preorder.frestrictLe n w, w (n+1))) :=
    StrategicWorldModel.pathLaw_has_transition_pair N μ.toMeasure n
  have hZero (z : JointState S X) (hz : z ∈ target.region) :
      K z target.regionᶜ = 0 := by
    have hfin : K z target.region ≠ ⊤ := measure_ne_top _ _
    rw [measure_compl target.region_measurable hfin]
    simp [hInv z hz]
  have hSet : pairFn ⁻¹' (A ×ˢ target.regionᶜ) =
      targetBadStep target n := by
    ext w
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_compl_iff]
    change (w n ∈ target.region ∧ w (n+1) ∉ target.region) ↔
      (w n ∈ target.region ∧ w (n+1) ∉ target.region)
    rfl
  calc
    P (targetBadStep target n) =
        (P.map pairFn) (A ×ˢ target.regionᶜ) := by
      rw [Measure.map_apply hp (hA.prod hC), hSet]
    _ = ((P.map (Preorder.frestrictLe n)) ⊗ₘ
          StrategicWorldModel.stationaryHistoryKernel K n)
          (A ×ˢ target.regionᶜ) := by
      rw [hPair]
      rfl
    _ = ∫⁻ h in A, K (last h) target.regionᶜ
          ∂(P.map (Preorder.frestrictLe n)) := by
      rw [Measure.compProd_apply_prod hA hC]
      rfl
    _ = 0 := by
      apply setLIntegral_eq_zero hA
      intro h hh
      exact hZero (last h) hh

/-- Countable union of true Markov transition cylinders: almost every
canonical trajectory can never leave a region once it has entered it. -/
theorem target_no_bad_step_ae
    (N : StrategicWorldModel S X A)
    (target : RegimeSpecification (JointState S X) T)
    (hInv : IsExactlyInvariant N target)
    (μ : ProbabilityMeasure (JointState S X)) :
    ∀ᵐ w ∂N.pathLaw μ.toMeasure,
      ∀ n : ℕ, w n ∈ target.region → w (n+1) ∈ target.region := by
  let P := N.pathLaw μ.toMeasure
  have hn : ∀ n : ℕ, ∀ᵐ w ∂P, w ∉ targetBadStep target n := by
    intro n
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using
      targetBadStep_probability_zero N target hInv μ n
  have hall : ∀ᵐ w ∂P, ∀ n : ℕ, w ∉ targetBadStep target n :=
    MeasureTheory.ae_all_iff.mpr hn
  filter_upwards [hall] with w hw n hmem
  by_contra hnot
  exact hw n ⟨hmem, hnot⟩

/-- Successful first-exit arrival is followed by permanent membership
in the INDEPENDENTLY certified destination region, almost surely.
A countable-time one-step proof avoids assuming a strong Markov theorem. -/
theorem switch_routed_path_retained_ae
    (M : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    (mSource mTarget : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M source)
    (J : AdmissibleStrategicIntervention F)
    (cert : CertifiedSwitchData M source target mSource mTarget F B₁ J)
    (μ : ProbabilityMeasure (JointState S X)) :
    ∀ᵐ w ∂J.intervention.apply.pathLaw μ.toMeasure,
      ∀ n : ℕ, w ∈ firstExitAtDestination source n target.basin →
        ∀ t ≥ n+1, w t ∈ target.region := by
  have hInv : IsExactlyInvariant J.intervention.apply target :=
    exactGR_exactlyInvariant J.intervention.apply target mTarget
      cert.targetExact
  have h := target_no_bad_step_ae J.intervention.apply target hInv μ
  filter_upwards [h] with w hw n hentry t ht
  have hstart : w (n+1) ∈ target.region :=
    target.basin_subset_region hentry.2.1
  exact Nat.le_induction hstart (fun k hk ih => hw k ih) t ht

/-- The existential infinite-horizon routing event is eventually
retained in the destination region almost surely. -/
theorem switch_eventual_retention_ae
    (M : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    (mSource mTarget : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M source)
    (J : AdmissibleStrategicIntervention F)
    (cert : CertifiedSwitchData M source target mSource mTarget F B₁ J)
    (μ : ProbabilityMeasure (JointState S X)) :
    ∀ᵐ w ∂J.intervention.apply.pathLaw μ.toMeasure,
      w ∈ firstExitEverDestination source target.basin →
        ∃ n : ℕ, w ∈ firstExitAtDestination source n target.basin ∧
          ∀ t ≥ n+1, w t ∈ target.region := by
  have h := switch_routed_path_retained_ae M source target
    mSource mTarget F B₁ J cert μ
  filter_upwards [h] with w hw hevent
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hevent
  exact ⟨n,hn,hw n hn⟩

end PermanssonResearch.RegimeExit
