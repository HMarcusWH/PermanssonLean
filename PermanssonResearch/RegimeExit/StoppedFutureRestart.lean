import PermanssonResearch.RegimeExit.ShiftedPrefixStationarity
import PermanssonResearch.RegimeExit.ConditionalRestartBridge
import PermanssonResearch.RegimeExit.ExitConservation
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic

/-!
# C-Exit D (C69.3–C69.4) — unconditional first-exit future routing

With the last-state restart property PROVED (`hasCanonicalLastStateRestart`,
C69.2), the PR #68 conditional bridge `stoppedFuture_measure_restart_of_lastState`
becomes unconditional. For `y ∈ B`, a measurable destination `D`, a finite
`n`, and ANY measurable infinite-future event `F`:

  `P_y(E_{n,D} ∩ θ_{n+1}⁻¹ F) = ∫ P_z(F) ExitStep_{n,D}(y, dz)`   (C69.3)

where the first exit occurs at time `n + 1` (never at time zero from `B`)
and the arrival law is PR #66's UNNORMALIZED exit-step submeasure
restricted to `D` (equivalently to `D \ B`, see
`firstExitStepMeasure_restrict_diff_region`). Summing over all finite exit
times by monotone measure-sum interchange:

  `μ_D^∞(F) = Σ_n μ_{n,D}(F) = ∫ P_z(F) R_B^{(∞)}(y, dz)|_D`        (C69.4)

Firewalls kept explicit below:
* no normalization: the arrival measures are never turned into probability
  laws, and a zero-mass destination gives the zero future measure;
* never-exiting mass is not reassigned: the full stopped-future mass plus
  `P_y(τ_B = ∞)` is exactly one;
* `Y_{τ_B}` is never evaluated at `τ_B = ∞`: the pathwise event is the
  disjoint union over FINITE first-exit times.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit

set_option autoImplicit false
open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA uH
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X]
variable [MeasurableSpace A] [MeasurableSpace H]

/-! ### C69.3 — finite first-exit time -/

/-- **C69.3** — unconditional first-exit full-future restart, for EVERY
measurable infinite-future event `F`. The hypothesis of PR #68's bridge is
discharged by C69.2; nothing is assumed. -/
theorem finiteStoppedFutureMeasure_restart
    (N : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) {y : JointState S X} (hy : y ∈ spec.region)
    (D : Set (JointState S X)) (hD : MeasurableSet D)
    (F : Set (ℕ → JointState S X)) (hF : MeasurableSet F) :
    finiteStoppedFutureMeasure N spec n y D F =
      ∫⁻ z, canonicalFutureKernel N z F
        ∂((firstExitStepMeasure N spec n y).restrict D) :=
  stoppedFuture_measure_restart_of_lastState N
    (hasCanonicalLastStateRestart N) spec n hy D hD F hF

/-- C69.3, original path-event form:
`P_y(E_{n,D} ∩ θ_{n+1}⁻¹ F) = ∫_{z ∈ D} P_z(F) ExitStep_n(y, dz)`. -/
theorem firstExit_shift_event_restart
    (N : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) {y : JointState S X} (hy : y ∈ spec.region)
    (D : Set (JointState S X)) (hD : MeasurableSet D)
    (F : Set (ℕ → JointState S X)) (hF : MeasurableSet F) :
    N.pathLaw (Measure.dirac y)
      (firstExitAtDestination spec n D ∩
        (pathTailShift (S := S) (X := X) (n+1)) ⁻¹' F) =
      ∫⁻ z in D, N.pathLaw (Measure.dirac z) F
        ∂(firstExitStepMeasure N spec n y) := by
  rw [← finiteStoppedFutureMeasure_apply N spec n y D F hF,
    finiteStoppedFutureMeasure_restart N spec n hy D hD F hF]
  simp_rw [canonicalFutureKernel_apply]

/-- C69.3, measure form: the finite stopped-future SUBmeasure is the
canonical restart kernel composed with the unnormalized arrival measure. -/
theorem finiteStoppedFutureMeasure_eq_bind
    (N : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) {y : JointState S X} (hy : y ∈ spec.region)
    (D : Set (JointState S X)) (hD : MeasurableSet D) :
    finiteStoppedFutureMeasure N spec n y D =
      canonicalFutureKernel N ∘ₘ
        ((firstExitStepMeasure N spec n y).restrict D) := by
  ext F hF
  rw [Measure.bind_apply hF (Kernel.aemeasurable _)]
  exact finiteStoppedFutureMeasure_restart N spec n hy D hD F hF

/-- The exit-step measure charges no state of `B`. -/
theorem firstExitStepMeasure_region_zero
    (N : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) (y : JointState S X) :
    firstExitStepMeasure N spec n y spec.region = 0 := by
  unfold firstExitStepMeasure
  rw [Measure.bind_apply spec.region_measurable (Kernel.aemeasurable _)]
  simp [exitSubkernel_region_zero]

/-- Destination restriction is genuinely to `D \ B`: restricting the
arrival measure to `D` or to `D \ B` gives the same measure. -/
theorem firstExitStepMeasure_restrict_diff_region
    (N : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) (y : JointState S X)
    (D : Set (JointState S X)) :
    (firstExitStepMeasure N spec n y).restrict D =
      (firstExitStepMeasure N spec n y).restrict (D \ spec.region) := by
  ext C hC
  rw [Measure.restrict_apply hC, Measure.restrict_apply hC,
    ← Set.inter_diff_assoc,
    measure_diff_null (firstExitStepMeasure_region_zero N spec n y)]

/-! ### C69.4 — all finite first-exit times -/

/-- The infinite stopped-future measure is the countable sum of the
finite-time stopped-future measures (no normalization, no ∞ index). -/
theorem infiniteStoppedFutureMeasure_apply_tsum
    (N : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X) (D : Set (JointState S X))
    (F : Set (ℕ → JointState S X)) (hF : MeasurableSet F) :
    infiniteStoppedFutureMeasure N spec y D F =
      ∑' n : ℕ, finiteStoppedFutureMeasure N spec n y D F :=
  Measure.sum_apply _ hF

/-- **C69.4** — countable infinite-future exit routing:
`μ_D^∞(F) = Σ_n μ_{n,D}(F) = ∫ P_z(F) R_B^{(∞)}(y, dz)|_D`, for every
measurable future event `F`. The interchange is `lintegral_sum_measure`
for the nonnegative integrand over `Measure.sum`. -/
theorem infiniteStoppedFutureMeasure_restart
    (N : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {y : JointState S X} (hy : y ∈ spec.region)
    (D : Set (JointState S X)) (hD : MeasurableSet D)
    (F : Set (ℕ → JointState S X)) (hF : MeasurableSet F) :
    infiniteStoppedFutureMeasure N spec y D F =
      ∫⁻ z, canonicalFutureKernel N z F
        ∂((exitRoutingInfiniteMeasure N spec y).restrict D) := by
  rw [infiniteStoppedFutureMeasure_apply_tsum N spec y D F hF,
    exitRoutingInfiniteMeasure, Measure.restrict_sum _ hD,
    lintegral_sum_measure]
  exact tsum_congr fun n =>
    finiteStoppedFutureMeasure_restart N spec n hy D hD F hF

/-- C69.4, measure form. -/
theorem infiniteStoppedFutureMeasure_eq_bind
    (N : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {y : JointState S X} (hy : y ∈ spec.region)
    (D : Set (JointState S X)) (hD : MeasurableSet D) :
    infiniteStoppedFutureMeasure N spec y D =
      canonicalFutureKernel N ∘ₘ
        ((exitRoutingInfiniteMeasure N spec y).restrict D) := by
  ext F hF
  rw [Measure.bind_apply hF (Kernel.aemeasurable _)]
  exact infiniteStoppedFutureMeasure_restart N spec hy D hD F hF

/-- The PATHWISE stopped-future event: first exit at some FINITE time
`n + 1` into `D \ B`, and the future re-indexed at that exit time lies in
`F`. Never evaluates a path at an infinite stopping index. -/
def firstExitFutureEvent
    (spec : RegimeSpecification (JointState S X) H)
    (D : Set (JointState S X)) (F : Set (ℕ → JointState S X)) :
    Set (ℕ → JointState S X) :=
  ⋃ n : ℕ, firstExitAtDestination spec n D ∩
    (pathTailShift (S := S) (X := X) (n+1)) ⁻¹' F

theorem firstExitFutureEvent_measurable
    (spec : RegimeSpecification (JointState S X) H)
    (D : Set (JointState S X)) (hD : MeasurableSet D)
    (F : Set (ℕ → JointState S X)) (hF : MeasurableSet F) :
    MeasurableSet (firstExitFutureEvent spec D F) :=
  MeasurableSet.iUnion fun n =>
    (firstExitAtDestination_measurable spec n D hD).inter
      (hF.preimage (measurable_pathTailShift (n+1)))

/-- Stopping-time semantics of the pathwise event: `τ_B(w)` is a FINITE
time `n + 1`, `Y_{τ_B} ∈ D`, and `θ_{τ_B} w ∈ F`. -/
theorem mem_firstExitFutureEvent_iff
    (spec : RegimeSpecification (JointState S X) H)
    (D : Set (JointState S X)) (F : Set (ℕ → JointState S X))
    (w : ℕ → JointState S X) :
    w ∈ firstExitFutureEvent spec D F ↔
      ∃ n : ℕ, exitTime spec w = ((n+1 : ℕ) : ℕ∞) ∧ w (n+1) ∈ D ∧
        pathTailShift (S := S) (X := X) (n+1) w ∈ F := by
  simp only [firstExitFutureEvent, Set.mem_iUnion, Set.mem_inter_iff,
    Set.mem_preimage, firstExitAt_eq_exitTime_succ, and_assoc,
    Nat.cast_add, Nat.cast_one]

/-- The finite-time pieces are pairwise disjoint (first exit is unique). -/
theorem firstExitFutureEvent_pieces_disjoint
    (spec : RegimeSpecification (JointState S X) H)
    (D : Set (JointState S X)) (F : Set (ℕ → JointState S X)) :
    Pairwise (Function.onFun Disjoint fun n : ℕ =>
      firstExitAtDestination spec n D ∩
        (pathTailShift (S := S) (X := X) (n+1)) ⁻¹' F) := by
  intro n m hnm
  exact (firstExitAtDestination_disjoint spec D hnm).mono
    Set.inter_subset_left Set.inter_subset_left

/-- The ORIGINAL canonical path law of the pathwise stopped-future event
is the infinite stopped-future submeasure of `F`. -/
theorem pathLaw_firstExitFutureEvent
    (N : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X)
    (D : Set (JointState S X)) (hD : MeasurableSet D)
    (F : Set (ℕ → JointState S X)) (hF : MeasurableSet F) :
    N.pathLaw (Measure.dirac y) (firstExitFutureEvent spec D F) =
      infiniteStoppedFutureMeasure N spec y D F := by
  rw [firstExitFutureEvent,
    measure_iUnion (firstExitFutureEvent_pieces_disjoint spec D F)
      (fun n => (firstExitAtDestination_measurable spec n D hD).inter
        (hF.preimage (measurable_pathTailShift (n+1)))),
    infiniteStoppedFutureMeasure_apply_tsum N spec y D F hF]
  exact tsum_congr fun n =>
    (finiteStoppedFutureMeasure_apply N spec n y D F hF).symm

/-- **C69.4, stopping-time form** (strong Markov at the first exit from
`B`, for the canonical stationary model, unconditionally):
`P_y(τ_B < ∞, Y_{τ_B} ∈ D, θ_{τ_B} ∈ F) = ∫_D P_z(F) R_B^{(∞)}(y, dz)`. -/
theorem pathLaw_firstExitFutureEvent_restart
    (N : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {y : JointState S X} (hy : y ∈ spec.region)
    (D : Set (JointState S X)) (hD : MeasurableSet D)
    (F : Set (ℕ → JointState S X)) (hF : MeasurableSet F) :
    N.pathLaw (Measure.dirac y) (firstExitFutureEvent spec D F) =
      ∫⁻ z in D, N.pathLaw (Measure.dirac z) F
        ∂(exitRoutingInfiniteMeasure N spec y) := by
  rw [pathLaw_firstExitFutureEvent N spec y D hD F hF,
    infiniteStoppedFutureMeasure_restart N spec hy D hD F hF]
  simp_rw [canonicalFutureKernel_apply]

/-! ### Mass bookkeeping firewalls -/

/-- Never-exiting mass is NOT lost or reassigned: the total stopped-future
mass over all exits plus `P_y(τ_B = ∞)` is exactly one. -/
theorem infiniteStoppedFutureMeasure_add_survivalForever_eq_one
    (N : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {y : JointState S X} (hy : y ∈ spec.region) :
    infiniteStoppedFutureMeasure N spec y (Set.univ \ spec.region) Set.univ +
      survivalForeverProbability N spec y = 1 := by
  rw [infiniteStoppedFutureMeasure_univ N spec hy (Set.univ \ spec.region)
    (MeasurableSet.univ.diff spec.region_measurable)]
  exact exitRoutingInfinite_add_survivalForever_eq_one N spec hy

/-- No normalization of zero-mass arrivals: if no path ever exits into
`D`, then every stopped-future event has probability ZERO (it is not
replaced by a restarted probability law). -/
theorem infiniteStoppedFutureMeasure_eq_zero_of_routing_zero
    (N : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {y : JointState S X} (hy : y ∈ spec.region)
    (D : Set (JointState S X)) (hD : MeasurableSet D)
    (hzero : exitRoutingInfinite N spec y D = 0)
    (F : Set (ℕ → JointState S X)) :
    infiniteStoppedFutureMeasure N spec y D F = 0 := by
  apply nonpos_iff_eq_zero.mp
  calc
    infiniteStoppedFutureMeasure N spec y D F ≤
        infiniteStoppedFutureMeasure N spec y D Set.univ :=
      measure_mono (Set.subset_univ F)
    _ = exitRoutingInfinite N spec y D :=
      infiniteStoppedFutureMeasure_univ N spec hy D hD
    _ = 0 := hzero

/-- The stopped-future measure of `F` never exceeds the arrival mass:
the restart integrand is a probability, so no mass is created. -/
theorem infiniteStoppedFutureMeasure_le_routing
    (N : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {y : JointState S X} (hy : y ∈ spec.region)
    (D : Set (JointState S X)) (hD : MeasurableSet D)
    (F : Set (ℕ → JointState S X)) :
    infiniteStoppedFutureMeasure N spec y D F ≤
      exitRoutingInfinite N spec y D := by
  calc
    infiniteStoppedFutureMeasure N spec y D F ≤
        infiniteStoppedFutureMeasure N spec y D Set.univ :=
      measure_mono (Set.subset_univ F)
    _ = exitRoutingInfinite N spec y D :=
      infiniteStoppedFutureMeasure_univ N spec hy D hD

end PermanssonResearch.RegimeExit
