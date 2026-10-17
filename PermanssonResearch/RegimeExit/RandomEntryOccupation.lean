import PermanssonResearch.RegimeExit.StoppedFutureRestart
import PermanssonResearch.RegimeExit.OccupationPrefixDeletion
import PermanssonLean.Regime.GeneratedRegime
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

/-!
# C-Exit E (C70.1) — almost-sure target occupation after a RANDOM entry time

Setting: a canonical model `N` (typically the post-intervention model
`J.intervention.apply`), a source specification with region `B`, and a target
specification whose basin is `B'_0`. Start at `y ∈ B`. The entry time into the
target basin is the RANDOM first-exit time `τ_B = n + 1`, finite on the routed
event and never evaluated at `∞`.

## Generic transport (`stoppedFuture_ae_of_basinLaws`)

If a path property `p` holds `P_μ`-a.s. for EVERY initial probability law `μ`
with `μ(D) = 1`, then `P_y`-a.s., on each first-exit event `E_{n,D}` the
re-indexed future `θ_{n+1} w` satisfies `p`; and simultaneously over all
`n` (`stoppedFuture_ae_all_of_basinLaws`).

The proof uses C69.3 (`finiteStoppedFutureMeasure_eq_bind`): the stopped
future is `P_• ∘ₘ ExitStep_n(y,·)|_D`. When that arrival measure has positive
mass `c`, it is divided by `c` to obtain a GENUINE probability law supported
on `D` (legitimate: positive mass, unit total), the certificate is applied to
that law, and the a.e. statement transfers back through `c • ·`
(`ae_ennreal_smul_measure_iff`), the pushforward (`ae_of_ae_map`) and the
restriction (`ae_restrict_iff'`). None of these steps requires measurability
of `{w | p w}` — important because the set of paths on which an occupation
law converges weakly need not be measurable for a general descriptor space.
When the arrival mass is zero the stopped-future measure is zero and nothing
is normalized.

## Occupation (`randomEntry_occupation_ae`)

Specializing `p` to target occupation convergence under the target's Exact-GR
certificate in the frozen almost-sure weak mode, and deleting the random but
finite pre-entry prefix with `tendsto_empiricalOccupation_of_tailShift`, the
WHOLE-PATH occupation law of `w` converges to the declared target `ν'`
almost surely on the routed event.

Kept separate on purpose: target-REGION retention is not used or claimed
here (it is PR #67's `switch_eventual_retention_ae`), and only the frozen
`ConvergenceMode.almostSureWeak` is transported — an arbitrary
`ConvergenceMode.custom` predicate is not.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit

set_option autoImplicit false
open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA uH uT
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH} {T : Type uT}
variable [MeasurableSpace S] [MeasurableSpace X]
variable [MeasurableSpace A] [MeasurableSpace H] [MeasurableSpace T]

/-- The canonical path law from ANY initial probability law is the restart
kernel composed with that law (linearity of the Ionescu--Tulcea law in its
initial condition). -/
theorem pathLaw_eq_bind
    (N : StrategicWorldModel S X A)
    (μ : Measure (JointState S X)) [IsProbabilityMeasure μ] :
    N.pathLaw μ = canonicalFutureKernel N ∘ₘ μ := by
  letI : IsMarkovKernel N.inducedKernel :=
    StrategicWorldModel.inducedKernel_isMarkov N
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  unfold StrategicWorldModel.pathLaw Kernel.trajMeasure
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hs) (MeasurableEquiv.measurable _)]
  rfl

/-- The arrival measure restricted to `D` has total mass equal to the
genuine path probability of first exit at `n+1` into `D \ B`; in particular
it is finite (at most one). -/
theorem firstExitStepMeasure_restrict_univ
    (N : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (n : ℕ) {y : JointState S X} (hy : y ∈ source.region)
    (D : Set (JointState S X)) (hD : MeasurableSet D) :
    (firstExitStepMeasure N source n y).restrict D Set.univ =
      N.pathLaw (Measure.dirac y) (firstExitAtDestination source n D) := by
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact (firstExitStep_eq_pathEvent N source n hy D hD).symm

theorem firstExitStepMeasure_restrict_univ_ne_top
    (N : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (n : ℕ) {y : JointState S X} (hy : y ∈ source.region)
    (D : Set (JointState S X)) (hD : MeasurableSet D) :
    (firstExitStepMeasure N source n y).restrict D Set.univ ≠ ∞ := by
  rw [firstExitStepMeasure_restrict_univ N source n hy D hD]
  exact measure_ne_top _ _

/-- **Normalized arrival law.** For a positive-mass first-exit arrival into
`D`, dividing by its (finite, positive) mass gives a probability law with
`ν(D) = 1`. This is the only place normalization occurs, and only for
positive mass. -/
noncomputable def normalizedArrivalLaw
    (N : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (n : ℕ) {y : JointState S X} (hy : y ∈ source.region)
    (D : Set (JointState S X)) (hD : MeasurableSet D)
    (hpos : (firstExitStepMeasure N source n y).restrict D ≠ 0) :
    ProbabilityMeasure (JointState S X) :=
  ⟨((firstExitStepMeasure N source n y).restrict D Set.univ)⁻¹ •
      (firstExitStepMeasure N source n y).restrict D,
    ⟨by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.inv_mul_cancel
        (by rwa [Ne, Measure.measure_univ_eq_zero])
        (firstExitStepMeasure_restrict_univ_ne_top N source n hy D hD)⟩⟩

theorem normalizedArrivalLaw_toMeasure
    (N : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (n : ℕ) {y : JointState S X} (hy : y ∈ source.region)
    (D : Set (JointState S X)) (hD : MeasurableSet D)
    (hpos : (firstExitStepMeasure N source n y).restrict D ≠ 0) :
    (normalizedArrivalLaw N source n hy D hD hpos).toMeasure =
      ((firstExitStepMeasure N source n y).restrict D Set.univ)⁻¹ •
        (firstExitStepMeasure N source n y).restrict D := rfl

/-- The normalized arrival law is supported on `D`. -/
theorem normalizedArrivalLaw_apply_dest
    (N : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (n : ℕ) {y : JointState S X} (hy : y ∈ source.region)
    (D : Set (JointState S X)) (hD : MeasurableSet D)
    (hpos : (firstExitStepMeasure N source n y).restrict D ≠ 0) :
    (normalizedArrivalLaw N source n hy D hD hpos).toMeasure D = 1 := by
  rw [normalizedArrivalLaw_toMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hD, Set.inter_self]
  have huniv := (Measure.restrict_apply (μ := firstExitStepMeasure N source n y)
    (s := D) MeasurableSet.univ)
  rw [Set.univ_inter] at huniv
  rw [← huniv]
  exact ENNReal.inv_mul_cancel (by rwa [Ne, Measure.measure_univ_eq_zero])
    (firstExitStepMeasure_restrict_univ_ne_top N source n hy D hD)

/-- The stopped future is the positive mass times the path law of the
normalized arrival law. -/
theorem finiteStoppedFutureMeasure_eq_smul_pathLaw
    (N : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (n : ℕ) {y : JointState S X} (hy : y ∈ source.region)
    (D : Set (JointState S X)) (hD : MeasurableSet D)
    (hpos : (firstExitStepMeasure N source n y).restrict D ≠ 0) :
    finiteStoppedFutureMeasure N source n y D =
      ((firstExitStepMeasure N source n y).restrict D Set.univ) •
        N.pathLaw (normalizedArrivalLaw N source n hy D hD hpos).toMeasure := by
  rw [pathLaw_eq_bind, normalizedArrivalLaw_toMeasure, Measure.comp_smul,
    smul_smul, ENNReal.mul_inv_cancel
      (by rwa [Ne, Measure.measure_univ_eq_zero])
      (firstExitStepMeasure_restrict_univ_ne_top N source n hy D hD),
    one_smul]
  exact finiteStoppedFutureMeasure_eq_bind N source n hy D hD

/-- **Generic a.e. transport through one random-entry time.** -/
theorem stoppedFuture_ae_of_basinLaws
    (N : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (D : Set (JointState S X)) (hD : MeasurableSet D)
    {p : (ℕ → JointState S X) → Prop}
    (hcert : ∀ μ : ProbabilityMeasure (JointState S X), μ.toMeasure D = 1 →
      ∀ᵐ v ∂N.pathLaw μ.toMeasure, p v)
    (n : ℕ) {y : JointState S X} (hy : y ∈ source.region) :
    ∀ᵐ w ∂N.pathLaw (Measure.dirac y),
      w ∈ firstExitAtDestination source n D →
        p (pathTailShift (S := S) (X := X) (n+1) w) := by
  have hstop : ∀ᵐ v ∂finiteStoppedFutureMeasure N source n y D, p v := by
    by_cases hρ : (firstExitStepMeasure N source n y).restrict D = 0
    · rw [finiteStoppedFutureMeasure_eq_bind N source n hy D hD, hρ]
      simp
    · rw [finiteStoppedFutureMeasure_eq_smul_pathLaw N source n hy D hD hρ,
        Measure.ae_ennreal_smul_measure_iff (by rwa [Ne, Measure.measure_univ_eq_zero])]
      exact hcert _ (normalizedArrivalLaw_apply_dest N source n hy D hD hρ)
  have hmap := ae_of_ae_map
    (measurable_pathTailShift (S := S) (X := X) (n+1)).aemeasurable hstop
  exact (ae_restrict_iff' (firstExitAtDestination_measurable source n D hD)).mp hmap

/-- Simultaneously over ALL finite first-exit times (countable union). -/
theorem stoppedFuture_ae_all_of_basinLaws
    (N : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (D : Set (JointState S X)) (hD : MeasurableSet D)
    {p : (ℕ → JointState S X) → Prop}
    (hcert : ∀ μ : ProbabilityMeasure (JointState S X), μ.toMeasure D = 1 →
      ∀ᵐ v ∂N.pathLaw μ.toMeasure, p v)
    {y : JointState S X} (hy : y ∈ source.region) :
    ∀ᵐ w ∂N.pathLaw (Measure.dirac y), ∀ n : ℕ,
      w ∈ firstExitAtDestination source n D →
        p (pathTailShift (S := S) (X := X) (n+1) w) :=
  ae_all_iff.mpr fun n =>
    stoppedFuture_ae_of_basinLaws N source D hD hcert n hy

/-- The target's Exact-GR certificate in the frozen almost-sure weak mode,
read as an a.e. statement for every admissible (basin-supported) law. -/
theorem exactGR_occupation_ae_of_admissible
    [TopologicalSpace S] [TopologicalSpace X]
    [TopologicalSpace T] [OpensMeasurableSpace T]
    (N : StrategicWorldModel S X A)
    (target : RegimeSpecification (JointState S X) T)
    (mT : Measure (JointState S X))
    (hGR : IsExactGeneratedRegime N target mT)
    (hmode : target.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) T)
    (μ : ProbabilityMeasure (JointState S X))
    (hμ : μ.toMeasure target.basin = 1) :
    ∀ᵐ v ∂N.pathLaw μ.toMeasure,
      Tendsto (fun n : ℕ =>
        empiricalOccupation target v (n+1) (Nat.succ_pos n))
        atTop (𝓝 target.target) := by
  have h := hGR.2.2.2 μ hμ
  unfold IsLimitingOccupationLaw at h
  rw [hmode] at h
  exact h

/-- **C70.1 (post-entry form).** Almost surely, at every finite first-exit
time `n+1` into the target basin, the occupation laws of the re-indexed
post-entry path converge weakly to the declared target `ν'`. -/
theorem postEntry_occupation_ae
    [TopologicalSpace S] [TopologicalSpace X]
    [TopologicalSpace T] [OpensMeasurableSpace T]
    (N : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    (mT : Measure (JointState S X))
    (hGR : IsExactGeneratedRegime N target mT)
    (hmode : target.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) T)
    {y : JointState S X} (hy : y ∈ source.region) :
    ∀ᵐ w ∂N.pathLaw (Measure.dirac y), ∀ n : ℕ,
      w ∈ firstExitAtDestination source n target.basin →
        Tendsto (fun m : ℕ =>
          empiricalOccupation target
            (pathTailShift (S := S) (X := X) (n+1) w) (m+1) (Nat.succ_pos m))
          atTop (𝓝 target.target) :=
  stoppedFuture_ae_all_of_basinLaws N source target.basin
    target.basin_measurable
    (fun μ hμ => exactGR_occupation_ae_of_admissible N target mT hGR hmode μ hμ)
    hy

/-- **C70.1 (whole-path form).** Almost surely on the routed event
`{τ_B < ∞, Y_{τ_B} ∈ B'_0}`, the occupation laws of the ENTIRE path
(including the random finite pre-entry prefix) converge weakly to `ν'`. -/
theorem randomEntry_occupation_ae
    [TopologicalSpace S] [TopologicalSpace X]
    [TopologicalSpace T] [OpensMeasurableSpace T]
    (N : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    (mT : Measure (JointState S X))
    (hGR : IsExactGeneratedRegime N target mT)
    (hmode : target.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) T)
    {y : JointState S X} (hy : y ∈ source.region) :
    ∀ᵐ w ∂N.pathLaw (Measure.dirac y),
      w ∈ firstExitEverDestination source target.basin →
        Tendsto (fun m : ℕ =>
          empiricalOccupation target w (m+1) (Nat.succ_pos m))
          atTop (𝓝 target.target) := by
  filter_upwards [postEntry_occupation_ae N source target mT hGR hmode hy]
    with w hw hroute
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hroute
  exact tendsto_empiricalOccupation_of_tailShift target w (n+1) (hw n hn)

end PermanssonResearch.RegimeExit
