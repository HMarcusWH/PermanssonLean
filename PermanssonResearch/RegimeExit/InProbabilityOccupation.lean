import PermanssonResearch.RegimeExit.RandomEntryOccupation
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic

/-!
# C-Exit E (C70.2) — in-probability occupation convergence after random entry

The frozen core exposes `ConvergenceMode.almostSureWeak` and an opaque
`ConvergenceMode.custom`. This module adds ONE precisely typed research mode,

  `inProbabilityWeak`: for every bounded continuous `f : H →ᵇ ℝ` and `ε > 0`,
  `P(|∫ f dν̂_{n+1} − ∫ f dν| > ε) → 0` as `n → ∞`

(convergence in probability of every bounded-continuous test integral of the
empirical occupation law). No claim is made that this coincides with
in-probability convergence for a metric on `ProbabilityMeasure H`; that
requires further hypotheses on `H` and is not used.

## Main theorem (`randomEntry_occupation_inProbability`)

If the target specification is an Exact GR for `N` in the mode
`inProbabilityWeak`, then for `y ∈ B` and every `f`, `ε > 0`,

  `P_y(τ_B < ∞, Y_{τ_B} ∈ B'_0, |∫ f dν̂_{n+1}(Y) − ∫ f dν'| > ε) → 0`.

Proof (no measurability of convergence sets is needed: deviation events at
fixed horizon are measurable):

1. decompose the routed event over FINITE first-exit times `k + 1`;
2. for fixed `k`, the finite-prefix estimate (`OccupationPrefixDeletion`)
   moves a deviation `ε` of the whole path at horizon `(k+1)+(m+1)` to a
   deviation `ε/2` of the shifted path at horizon `m+1` once
   `2(k+1)‖f‖/((k+1)+(m+1)) < ε/2`;
3. by C69.3 the shifted-future probability is `c_k · P_{ν_k}(·)` with `ν_k`
   the normalized positive-mass arrival law, to which the target
   certificate applies; zero-mass arrivals contribute zero;
4. Tannery's dominated convergence (`tendsto_tsum_of_dominated_convergence`)
   over `k`, dominated by the summable `P_y(E_k)`.

Corollary `inProbability_deviation_eventually_le`: under a routing bound
`P_y(routed) ≥ 1 − η`, eventually `P_y(|∫ f dν̂ − ∫ f dν'| > ε) ≤ η + δ` for
every `δ > 0`. An arbitrary `ConvergenceMode.custom` is NOT transported.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal ProbabilityTheory BoundedContinuousFunction

namespace PermanssonResearch.RegimeExit

set_option autoImplicit false
open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA uH uT uY uO
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH} {T : Type uT}
variable [MeasurableSpace S] [MeasurableSpace X]
variable [MeasurableSpace A] [MeasurableSpace H] [MeasurableSpace T]

/-- Research in-probability weak occupation convergence (test-function
form), declared as an ordinary frozen `ConvergenceMode`. -/
noncomputable def inProbabilityWeak
    (Y : Type uY) (O : Type uO) [MeasurableSpace Y] [MeasurableSpace O]
    [TopologicalSpace O] : ConvergenceMode Y O where
  holds μ occ ν :=
    ∀ f : O →ᵇ ℝ, ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => μ {w | ε < |∫ x, f x
          ∂(occ w (n+1) (Nat.succ_pos n) : Measure O) -
          ∫ x, f x ∂(ν : Measure O)|}) atTop (𝓝 0)

/-- Deviation event of the frozen occupation law at horizon `n+1`. -/
def occupationDeviationSet
    [TopologicalSpace T]
    (spec : RegimeSpecification (JointState S X) T)
    (f : T →ᵇ ℝ) (ε : ℝ) (n : ℕ) : Set (ℕ → JointState S X) :=
  {w | ε < |∫ x, f x ∂(empiricalOccupation spec w (n+1)
      (Nat.succ_pos n) : Measure T) - ∫ x, f x ∂(spec.target : Measure T)|}

theorem occupationDeviationSet_eq_average
    [TopologicalSpace T] [OpensMeasurableSpace T]
    (spec : RegimeSpecification (JointState S X) T)
    (f : T →ᵇ ℝ) (ε : ℝ) (n : ℕ) :
    occupationDeviationSet spec f ε n =
      {w | ε < |(((n+1 : ℕ) : ℝ)⁻¹) *
          ∑ t ∈ Finset.range (n+1), f (spec.descriptor (w t)) -
          ∫ x, f x ∂(spec.target : Measure T)|} := by
  ext w
  simp only [occupationDeviationSet, Set.mem_ofPred_eq]
  rw [integral_empiricalOccupation_eq_average spec w (n+1) _
    f.continuous.measurable]

/-- Fixed-horizon deviation events are measurable (finite averages of
measurable observables). -/
theorem occupationDeviationSet_measurable
    [TopologicalSpace T] [OpensMeasurableSpace T]
    (spec : RegimeSpecification (JointState S X) T)
    (f : T →ᵇ ℝ) (ε : ℝ) (n : ℕ) :
    MeasurableSet (occupationDeviationSet spec f ε n) := by
  rw [occupationDeviationSet_eq_average]
  have hsum : Measurable (fun w : ℕ → JointState S X =>
      ∑ t ∈ Finset.range (n+1), f (spec.descriptor (w t))) :=
    Finset.measurable_sum _ fun t _ =>
      f.continuous.measurable.comp
        (spec.descriptor_measurable.comp (measurable_pi_apply t))
  exact measurableSet_lt measurable_const
    (continuous_abs.measurable.comp ((hsum.const_mul _).sub_const _))

/-- **Prefix transfer of deviations.** Once the deletion error
`2(k+1)‖f‖/((k+1)+(m+1))` is below `ε/2`, an `ε`-deviation of the whole path
at horizon `(m+(k+1))+1` forces an `ε/2`-deviation of `θ_{k+1} w` at
horizon `m+1`. -/
theorem occupationDeviation_subset_shift
    [TopologicalSpace T] [OpensMeasurableSpace T]
    (spec : RegimeSpecification (JointState S X) T)
    (f : T →ᵇ ℝ) (ε : ℝ) (k m : ℕ)
    (hδ : 2 * ((k+1 : ℕ) : ℝ) * ‖f‖ / (((k+1 : ℕ) : ℝ) + ((m+1 : ℕ) : ℝ)) <
      ε / 2) :
    occupationDeviationSet spec f ε (m + (k+1)) ⊆
      (pathTailShift (S := S) (X := X) (k+1)) ⁻¹'
        occupationDeviationSet spec f (ε/2) m := by
  intro w hw
  rw [occupationDeviationSet_eq_average] at hw
  simp only [Set.mem_preimage]
  rw [occupationDeviationSet_eq_average]
  simp only [Set.mem_setOf_eq] at hw ⊢
  set L := ∫ x, f x ∂(spec.target : Measure T)
  set g : ℕ → ℝ := fun t => f (spec.descriptor (w t)) with hg
  have hC : ∀ t, |g t| ≤ ‖f‖ := fun t => by
    simpa [Real.norm_eq_abs] using f.norm_coe_le_norm (spec.descriptor (w t))
  have hidx : m + (k+1) + 1 = (k+1) + (m+1) := by omega
  rw [hidx] at hw
  have hest := abs_average_sub_shift_average_le g hC (k+1) (m+1)
    (Nat.succ_pos m)
  set a := (((k+1 + (m+1) : ℕ) : ℝ))⁻¹ *
    ∑ t ∈ Finset.range (k+1 + (m+1)), g t
  set b := (((m+1 : ℕ) : ℝ))⁻¹ * ∑ t ∈ Finset.range (m+1), g (k+1 + t)
  have hb : (((m+1 : ℕ) : ℝ))⁻¹ * ∑ t ∈ Finset.range (m+1),
      f (spec.descriptor (pathTailShift (S := S) (X := X) (k+1) w t)) = b := rfl
  rw [hb]
  have hest' : |a - b| < ε / 2 := by
    push_cast at hest hδ ⊢
    linarith
  have htri : |a - L| ≤ |a - b| + |b - L| := abs_sub_le a b L
  linarith

/-- Shifted-future probabilities at a fixed exit time are the arrival mass
times the normalized-arrival path law (C69.3), or zero for zero mass. -/
theorem firstExit_shift_le_mass_mul
    (N : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (D : Set (JointState S X)) (hD : MeasurableSet D)
    (k : ℕ) {y : JointState S X} (hy : y ∈ source.region)
    (hpos : (firstExitStepMeasure N source k y).restrict D ≠ 0)
    (G : Set (ℕ → JointState S X)) (hG : MeasurableSet G) :
    N.pathLaw (Measure.dirac y)
        (firstExitAtDestination source k D ∩
          (pathTailShift (S := S) (X := X) (k+1)) ⁻¹' G) =
      ((firstExitStepMeasure N source k y).restrict D Set.univ) *
        N.pathLaw (normalizedArrivalLaw N source k hy D hD hpos).toMeasure G := by
  rw [← finiteStoppedFutureMeasure_apply N source k y D G hG,
    finiteStoppedFutureMeasure_eq_smul_pathLaw N source k hy D hD hpos,
    Measure.smul_apply, smul_eq_mul]

/-- The target's Exact-GR certificate in the research in-probability mode,
read for every admissible (basin-supported) initial law. -/
theorem exactGR_inProbability_of_admissible
    [TopologicalSpace S] [TopologicalSpace X]
    [TopologicalSpace T] [OpensMeasurableSpace T]
    (N : StrategicWorldModel S X A)
    (target : RegimeSpecification (JointState S X) T)
    (mT : Measure (JointState S X))
    (hGR : IsExactGeneratedRegime N target mT)
    (hmode : target.convergenceMode = inProbabilityWeak (JointState S X) T)
    (μ : ProbabilityMeasure (JointState S X))
    (hμ : μ.toMeasure target.basin = 1)
    (f : T →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => N.pathLaw μ.toMeasure
      (occupationDeviationSet target f ε n)) atTop (𝓝 0) := by
  have h := hGR.2.2.2 μ hμ
  unfold IsLimitingOccupationLaw at h
  rw [hmode] at h
  exact h f ε hε

/-- **Per-exit-time term.** For each fixed first-exit time `k+1`, the
probability of exiting then into the basin AND deviating at horizon `n+1`
tends to zero. -/
theorem firstExit_deviation_tendsto_zero
    [TopologicalSpace S] [TopologicalSpace X]
    [TopologicalSpace T] [OpensMeasurableSpace T]
    (N : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    (mT : Measure (JointState S X))
    (hGR : IsExactGeneratedRegime N target mT)
    (hmode : target.convergenceMode = inProbabilityWeak (JointState S X) T)
    {y : JointState S X} (hy : y ∈ source.region)
    (f : T →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    Tendsto (fun n : ℕ => N.pathLaw (Measure.dirac y)
      (firstExitAtDestination source k target.basin ∩
        occupationDeviationSet target f ε n)) atTop (𝓝 0) := by
  set P := N.pathLaw (Measure.dirac y)
  set E := firstExitAtDestination source k target.basin
  by_cases hρ : (firstExitStepMeasure N source k y).restrict target.basin = 0
  · -- zero arrival mass: the whole first-exit event is null; no normalization
    have hE : P E = 0 := by
      rw [← firstExitStepMeasure_restrict_univ N source k hy target.basin
        target.basin_measurable, hρ]
      rfl
    have hzero : ∀ n, P (E ∩ occupationDeviationSet target f ε n) = 0 :=
      fun n => measure_mono_null Set.inter_subset_left hE
    simp only [hzero]
    exact tendsto_const_nhds
  · set c := (firstExitStepMeasure N source k y).restrict target.basin Set.univ
    have hc : c ≠ ∞ := firstExitStepMeasure_restrict_univ_ne_top N source k hy
      target.basin target.basin_measurable
    set ν := normalizedArrivalLaw N source k hy target.basin
      target.basin_measurable hρ
    have hcert := exactGR_inProbability_of_admissible N target mT hGR hmode ν
      (normalizedArrivalLaw_apply_dest N source k hy target.basin
        target.basin_measurable hρ) f (half_pos hε)
    have hupper : Tendsto (fun m : ℕ =>
        c * N.pathLaw ν.toMeasure (occupationDeviationSet target f (ε/2) m))
          atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul hcert (Or.inr hc)
      simpa using this
    -- eventually the deletion error is below ε/2
    have hδ : ∀ᶠ m : ℕ in atTop,
        2 * ((k+1 : ℕ) : ℝ) * ‖f‖ /
          (((k+1 : ℕ) : ℝ) + ((m+1 : ℕ) : ℝ)) < ε / 2 := by
      have hden : Tendsto (fun m : ℕ =>
          ((k+1 : ℕ) : ℝ) + ((m+1 : ℕ) : ℝ)) atTop atTop := by
        apply tendsto_atTop_add_const_left
        exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
      have hlim := (tendsto_const_nhds
        (x := 2 * ((k+1 : ℕ) : ℝ) * ‖f‖)).div_atTop hden
      exact hlim.eventually (gt_mem_nhds (half_pos hε))
    have hshift : Tendsto (fun m : ℕ =>
        P (E ∩ occupationDeviationSet target f ε (m + (k+1)))) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        hupper (Eventually.of_forall fun _ => bot_le) ?_
      filter_upwards [hδ] with m hm
      calc
        P (E ∩ occupationDeviationSet target f ε (m + (k+1))) ≤
            P (E ∩ (pathTailShift (S := S) (X := X) (k+1)) ⁻¹'
              occupationDeviationSet target f (ε/2) m) :=
          measure_mono (Set.inter_subset_inter_right _
            (occupationDeviation_subset_shift target f ε k m hm))
        _ = c * N.pathLaw ν.toMeasure
              (occupationDeviationSet target f (ε/2) m) :=
          firstExit_shift_le_mass_mul N source target.basin
            target.basin_measurable k hy hρ _
            (occupationDeviationSet_measurable target f (ε/2) m)
    exact (tendsto_add_atTop_iff_nat (k+1)).mp hshift

/-- **C70.2.** In-probability occupation convergence on the routed event,
after a random finite entry time. -/
theorem randomEntry_occupation_inProbability
    [TopologicalSpace S] [TopologicalSpace X]
    [TopologicalSpace T] [OpensMeasurableSpace T]
    (N : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    (mT : Measure (JointState S X))
    (hGR : IsExactGeneratedRegime N target mT)
    (hmode : target.convergenceMode = inProbabilityWeak (JointState S X) T)
    {y : JointState S X} (hy : y ∈ source.region)
    (f : T →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => N.pathLaw (Measure.dirac y)
      (firstExitEverDestination source target.basin ∩
        occupationDeviationSet target f ε n)) atTop (𝓝 0) := by
  set P := N.pathLaw (Measure.dirac y)
  set E : ℕ → Set (ℕ → JointState S X) := fun k =>
    firstExitAtDestination source k target.basin
  set Dev : ℕ → Set (ℕ → JointState S X) := fun n =>
    occupationDeviationSet target f ε n
  have hEmeas : ∀ k, MeasurableSet (E k) := fun k =>
    firstExitAtDestination_measurable source k target.basin
      target.basin_measurable
  have hsplit : ∀ n, P (firstExitEverDestination source target.basin ∩ Dev n) =
      ∑' k, P (E k ∩ Dev n) := by
    intro n
    rw [firstExitEverDestination, Set.iUnion_inter]
    exact measure_iUnion
      (fun i j hij => (firstExitAtDestination_disjoint source target.basin
        hij).mono Set.inter_subset_left Set.inter_subset_left)
      (fun k => (hEmeas k).inter
        (occupationDeviationSet_measurable target f ε n))
  have hsumE : ∑' k, P (E k) ≠ ∞ := by
    rw [← measure_iUnion
      (fun i j hij => firstExitAtDestination_disjoint source target.basin hij)
      hEmeas]
    exact measure_ne_top _ _
  have hterm : ∀ k, Tendsto (fun n => P (E k ∩ Dev n)) atTop (𝓝 0) :=
    fun k => firstExit_deviation_tendsto_zero N source target mT hGR hmode hy
      f hε k
  have hreal : Tendsto (fun n => ∑' k, (P (E k ∩ Dev n)).toReal) atTop
      (𝓝 (∑' _k : ℕ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun k => (P (E k)).toReal) (ENNReal.summable_toReal hsumE)
      (fun k => ?_) (Eventually.of_forall fun n k => ?_)
    · exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hterm k)
    · rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_mono (measure_ne_top _ _)
        (measure_mono Set.inter_subset_left)
  rw [tsum_zero] at hreal
  have hne : ∀ n, ∑' k, P (E k ∩ Dev n) ≠ ∞ := fun n =>
    ne_top_of_le_ne_top hsumE
      (ENNReal.tsum_le_tsum fun k => measure_mono Set.inter_subset_left)
  have hsum : Tendsto (fun n => ∑' k, P (E k ∩ Dev n)) atTop (𝓝 0) := by
    rw [← ENNReal.tendsto_toReal_iff hne ENNReal.zero_ne_top]
    refine hreal.congr fun n => ?_
    exact (ENNReal.tsum_toReal_eq fun k => measure_ne_top _ _).symm
  exact hsum.congr fun n => (hsplit n).symm

/-- **C70.2 corollary.** If the routed event has probability at least
`1 - η`, then eventually the WHOLE-path deviation probability is at most
`η + δ`, for every `δ > 0`. Never-routed mass is charged in full. -/
theorem inProbability_deviation_eventually_le
    [TopologicalSpace S] [TopologicalSpace X]
    [TopologicalSpace T] [OpensMeasurableSpace T]
    (N : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    (mT : Measure (JointState S X))
    (hGR : IsExactGeneratedRegime N target mT)
    (hmode : target.convergenceMode = inProbabilityWeak (JointState S X) T)
    {y : JointState S X} (hy : y ∈ source.region)
    (f : T →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε)
    {η : ℝ≥0∞}
    (hroute : 1 - η ≤ N.pathLaw (Measure.dirac y)
      (firstExitEverDestination source target.basin))
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, N.pathLaw (Measure.dirac y)
      (occupationDeviationSet target f ε n) ≤ η + δ := by
  set P := N.pathLaw (Measure.dirac y)
  set R := firstExitEverDestination source target.basin
  have hR : MeasurableSet R :=
    firstExitEverDestination_measurable source target.basin
      target.basin_measurable
  have hcompl : P Rᶜ ≤ η := by
    rw [prob_compl_eq_one_sub hR]
    exact tsub_le_iff_left.mpr (tsub_le_iff_right.mp hroute)
  have hlim := randomEntry_occupation_inProbability N source target mT hGR
    hmode hy f hε
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with n hn
  calc
    P (occupationDeviationSet target f ε n) ≤
        P (R ∩ occupationDeviationSet target f ε n) + P Rᶜ := by
      calc
        P (occupationDeviationSet target f ε n) ≤
            P ((R ∩ occupationDeviationSet target f ε n) ∪ Rᶜ) :=
          measure_mono fun w hw => by
            by_cases hwR : w ∈ R
            · exact Or.inl ⟨hwR, hw⟩
            · exact Or.inr hwR
        _ ≤ _ := measure_union_le _ _
    _ ≤ δ + η := add_le_add hn.le hcompl
    _ = η + δ := add_comm _ _

end PermanssonResearch.RegimeExit
