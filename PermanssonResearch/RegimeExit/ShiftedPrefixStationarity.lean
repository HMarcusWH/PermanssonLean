import PermanssonResearch.RegimeExit.StationaryLastStateReduction
import PermanssonResearch.RegimeExit.ShiftedHistoryMarginals
import PermanssonLean.StrategicWorld.WellPosedness
import PermanssonResearch.Probability.CompProdPushforward
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic

/-!
# C-Exit D (C69.1–C69.2) — unconditional canonical last-state restart

For the ORIGINAL canonical stationary strategic-world process, conditioning
on any complete absolute-time history `h` through `m` and re-indexing the
future at zero gives exactly the canonical path law restarted from the
last observed state `h m`:

  `L(Y_{m+·} | h) = P_{h_m}`.

The proof uses only certified ingredients:

1. the shifted continuation starts at `h m` (`shiftedHistory_zero_marginal`);
2. mathlib's absolute-time Ionescu--Tulcea transition-pair identity
   `Kernel.partialTraj_compProd_eq_map_traj` at time `m + n`;
3. STATIONARITY of the induced kernel, used exactly once:
   `stationaryHistoryKernel K (m+n)` reads only the last coordinate, so it
   equals `stationaryHistoryKernel K n` precomposed with the map that drops
   the first `m` coordinates;
4. the frozen v0.1.8 uniqueness theorems
   `StrategicWorldModel.prefix_maps_eq_of_initial_and_transition` and
   `StrategicWorldModel.measure_eq_of_prefix_maps_eq`.

No `StrongMarkov` premise, finite-state, countable or standard-Borel
restriction, and no second path-law construction is introduced. The
predicate `HasCanonicalShiftedPrefixLaws` from PR #68 is PROVED below, not
assumed. A time-inhomogeneous kernel family would break step 3; the
statement is therefore specific to the stationary canonical model.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit

set_option autoImplicit false
open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA
variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

/-- Forget the first `m` coordinates of an absolute-time history through
`m + n`, re-indexing the remaining `n + 1` states at zero. -/
def dropHistoryPrefix (m n : ℕ)
    (q : (i : Finset.Iic (m + n)) → JointState S X) :
    (i : Finset.Iic n) → JointState S X :=
  fun i => q ⟨m + i.1, Finset.mem_Iic.mpr
    (Nat.add_le_add_left (Finset.mem_Iic.mp i.2) m)⟩

theorem measurable_dropHistoryPrefix (m n : ℕ) :
    Measurable (dropHistoryPrefix (S := S) (X := X) m n) := by
  exact Measurable.of_eval fun _ => measurable_pi_apply _

/-- The first `n + 1` coordinates of the time-`m` tail are the dropped
absolute prefix through `m + n`. Purely an indexing identity. -/
theorem frestrictLe_pathTailShift (m n : ℕ)
    (w : ℕ → JointState S X) :
    Preorder.frestrictLe n (pathTailShift (S := S) (X := X) m w) =
      dropHistoryPrefix m n (Preorder.frestrictLe (m + n) w) := by
  funext i
  rfl

/-- STATIONARITY, the only place it is used: the absolute-time history
kernel at `m + n` is the time-`n` history kernel read through the
prefix-dropping map. Both read only the most recent state. -/
theorem stationaryHistoryKernel_add_eq_comap_drop
    (K : Kernel (JointState S X) (JointState S X)) (m n : ℕ) :
    StrategicWorldModel.stationaryHistoryKernel K (m + n) =
      (StrategicWorldModel.stationaryHistoryKernel K n).comap
        (dropHistoryPrefix (S := S) (X := X) m n)
        (measurable_dropHistoryPrefix m n) := by
  ext q : 1
  rfl

/-- The shifted continuation is the pushforward of the absolute-time
Ionescu--Tulcea continuation measure along the tail shift. -/
theorem canonicalShiftedHistoryKernel_apply
    (N : StrategicWorldModel S X A) (m : ℕ)
    (h : (i : Finset.Iic m) → JointState S X) :
    canonicalShiftedHistoryKernel N m h =
      (canonicalHistoryContinuation N m h).map
        (pathTailShift (S := S) (X := X) m) := by
  unfold canonicalShiftedHistoryKernel
  exact Kernel.map_apply _ (measurable_pathTailShift (S := S) (X := X) m) h

/-- The shifted continuation from ANY finite history satisfies the frozen
v0.1.8 stationary transition-pair identity for the model's own induced
kernel, at EVERY future time `n`. This is a whole-prefix identity, not a
one-coordinate marginal check. -/
theorem shiftedHistory_hasTransitionPair
    (N : StrategicWorldModel S X A) (m : ℕ)
    (h : (i : Finset.Iic m) → JointState S X) :
    StrategicWorldModel.HasTransitionPair
      (canonicalShiftedHistoryKernel N m h) N.inducedKernel := by
  letI : IsMarkovKernel N.inducedKernel :=
    StrategicWorldModel.inducedKernel_isMarkov N
  intro n
  let κ : (k : ℕ) →
      Kernel ((i : Finset.Iic k) → JointState S X) (JointState S X) :=
    fun k => StrategicWorldModel.stationaryHistoryKernel N.inducedKernel k
  let μ : Measure (ℕ → JointState S X) := canonicalHistoryContinuation N m h
  let shift := pathTailShift (S := S) (X := X) m
  let drop := dropHistoryPrefix (S := S) (X := X) m n
  have hShift : Measurable shift := measurable_pathTailShift m
  have hDrop : Measurable drop := measurable_dropHistoryPrefix m n
  have hμ : μ = Kernel.traj (X := fun _ : ℕ => JointState S X) κ m h := rfl
  -- absolute-time transition pair at time m + n (mathlib, Ionescu--Tulcea)
  have habs :
      (μ.map (Preorder.frestrictLe (m + n))) ⊗ₘ κ (m + n) =
        μ.map (fun w : ℕ → JointState S X =>
          (Preorder.frestrictLe (m + n) w, w (m + n + 1))) := by
    rw [hμ, Kernel.traj_map_frestrictLe_apply]
    exact Kernel.partialTraj_compProd_eq_map_traj
      (X := fun _ : ℕ => JointState S X) (κ := κ) (Nat.le_add_right m n)
  have hprefix :
      (canonicalShiftedHistoryKernel N m h).map (Preorder.frestrictLe n) =
        (μ.map (Preorder.frestrictLe (m + n))).map drop := by
    rw [canonicalShiftedHistoryKernel_apply,
      Measure.map_map (Preorder.measurable_frestrictLe n) hShift,
      Measure.map_map hDrop (Preorder.measurable_frestrictLe (m + n))]
    congr 1
  have hpairFn :
      (fun w : ℕ → JointState S X =>
          (Preorder.frestrictLe n w, w (n + 1))) ∘ shift =
        Prod.map drop id ∘
          (fun w : ℕ → JointState S X =>
            (Preorder.frestrictLe (m + n) w, w (m + n + 1))) := by
    funext w
    exact Prod.ext (frestrictLe_pathTailShift m n w) rfl
  have hpair :
      (canonicalShiftedHistoryKernel N m h).map
          (fun w : ℕ → JointState S X =>
            (Preorder.frestrictLe n w, w (n + 1))) =
        (μ.map (fun w : ℕ → JointState S X =>
          (Preorder.frestrictLe (m + n) w, w (m + n + 1)))).map
            (Prod.map drop id) := by
    rw [canonicalShiftedHistoryKernel_apply,
      Measure.map_map (by fun_prop) hShift,
      Measure.map_map (hDrop.prodMap measurable_id) (by fun_prop)]
    exact congrArg (fun g => μ.map g) hpairFn
  have hκ : κ (m + n) = (κ n).comap drop hDrop :=
    stationaryHistoryKernel_add_eq_comap_drop N.inducedKernel m n
  rw [hprefix, hpair, ← habs, hκ]
  exact PermanssonResearch.Probability.compProd_map_left_eq_map_compProd_comap
    _ hDrop (κ n)

/-- The singleton-prefix embedding used to compare time-zero laws without
appealing to a particular `Unique` instance of `Finset.Iic 0`. -/
def singletonPrefix (z : JointState S X) :
    (i : Finset.Iic (0 : ℕ)) → JointState S X :=
  fun _ => z

theorem measurable_singletonPrefix :
    Measurable (singletonPrefix (S := S) (X := X)) :=
  Measurable.of_eval fun _ => measurable_id

theorem frestrictLe_zero_eq_singletonPrefix :
    (Preorder.frestrictLe 0 : (ℕ → JointState S X) →
        (i : Finset.Iic (0 : ℕ)) → JointState S X) =
      singletonPrefix ∘ (fun w : ℕ → JointState S X => w 0) := by
  funext w i
  have hi : i.1 = 0 := Nat.le_zero.mp (Finset.mem_Iic.mp i.2)
  change w i.1 = w 0
  rw [hi]

/-- Any infinite-path law whose time-zero coordinate is `δ_z` has the
zeroth-prefix law of the canonical point-started process at `z`. -/
theorem map_frestrictLe_zero_of_eval_zero
    (ν : Measure (ℕ → JointState S X)) (z : JointState S X)
    (hν : ν.map (fun w : ℕ → JointState S X => w 0) = Measure.dirac z) :
    ν.map (Preorder.frestrictLe 0) =
      (Measure.dirac z).map (singletonPrefix (S := S) (X := X)) := by
  rw [frestrictLe_zero_eq_singletonPrefix,
    ← Measure.map_map measurable_singletonPrefix (measurable_pi_apply 0), hν]

/-- **C69.1** — Every shifted finite-prefix law. For EVERY absolute time
`m`, EVERY complete history `h` through `m` and EVERY future horizon `T`,
the first `T + 1` coordinates of the shifted continuation have exactly the
prefix law of the canonical process restarted from `h m`. Proved, not
assumed; the universal horizon quantifier is discharged by the frozen
initial-plus-transition uniqueness theorem. -/
theorem hasCanonicalShiftedPrefixLaws
    (N : StrategicWorldModel S X A) :
    HasCanonicalShiftedPrefixLaws N := by
  letI : IsMarkovKernel N.inducedKernel :=
    StrategicWorldModel.inducedKernel_isMarkov N
  intro m h T
  let z := h ⟨m, Finset.mem_Iic.mpr le_rfl⟩
  have h0 :
      (canonicalShiftedHistoryKernel N m h).map (Preorder.frestrictLe 0) =
        (canonicalFutureKernel N z).map (Preorder.frestrictLe 0) := by
    rw [map_frestrictLe_zero_of_eval_zero _ z
        (shiftedHistory_zero_marginal N m h),
      map_frestrictLe_zero_of_eval_zero _ z
        (canonicalFutureKernel_zero_marginal N z)]
  have hFuture :
      StrategicWorldModel.HasTransitionPair
        (canonicalFutureKernel N z) N.inducedKernel := by
    rw [canonicalFutureKernel_apply]
    exact StrategicWorldModel.pathLaw_has_transition_pair N (Measure.dirac z)
  exact StrategicWorldModel.prefix_maps_eq_of_initial_and_transition
    N.inducedKernel h0 (shiftedHistory_hasTransitionPair N m h) hFuture T

/-- **C69.2** — Unconditional full-future last-state restart:
`L(Y_{m+·} | h) = P_{h_m}` as probability measures on infinite paths, for
every canonical stationary strategic-world model. Obtained from C69.1 and
the frozen projective-limit uniqueness theorem; no extra hypothesis. -/
theorem hasCanonicalLastStateRestart
    (N : StrategicWorldModel S X A) :
    HasCanonicalLastStateRestart N :=
  hasCanonicalLastStateRestart_of_allPrefixLaws N
    (hasCanonicalShiftedPrefixLaws N)

/-- Pointwise form of C69.2. -/
theorem canonicalShiftedHistoryKernel_eq_restart
    (N : StrategicWorldModel S X A) (m : ℕ)
    (h : (i : Finset.Iic m) → JointState S X) :
    canonicalShiftedHistoryKernel N m h =
      canonicalFutureKernel N (h ⟨m, Finset.mem_Iic.mpr le_rfl⟩) :=
  hasCanonicalLastStateRestart N m h

/-- Pasts are irrelevant: two histories, possibly of DIFFERENT lengths,
with the same final state have identical shifted infinite-future laws. -/
theorem canonicalShiftedHistoryKernel_eq_of_last_eq
    (N : StrategicWorldModel S X A) {m m' : ℕ}
    (h : (i : Finset.Iic m) → JointState S X)
    (h' : (i : Finset.Iic m') → JointState S X)
    (hlast : h ⟨m, Finset.mem_Iic.mpr le_rfl⟩ =
      h' ⟨m', Finset.mem_Iic.mpr le_rfl⟩) :
    canonicalShiftedHistoryKernel N m h =
      canonicalShiftedHistoryKernel N m' h' := by
  rw [canonicalShiftedHistoryKernel_eq_restart,
    canonicalShiftedHistoryKernel_eq_restart, hlast]

/-- Deterministic-time Markov property of the point-started canonical law:
the prefix through `m` and the shifted future are jointly distributed as
the prefix law composed with the restart kernel at the LAST state. -/
theorem pointPathLaw_shifted_lastState_joint
    (N : StrategicWorldModel S X A)
    (y : JointState S X) (m : ℕ) :
    (N.pathLaw (Measure.dirac y)).map
      (fun w : ℕ → JointState S X =>
        (Preorder.frestrictLe m w,
          pathTailShift (S := S) (X := X) m w)) =
    ((N.pathLaw (Measure.dirac y)).map
        (Preorder.frestrictLe m)) ⊗ₘ
      (canonicalFutureKernel N).comap
        (fun h : (i : Finset.Iic m) → JointState S X =>
          h ⟨m, Finset.mem_Iic.mpr le_rfl⟩) (by fun_prop) := by
  rw [pointPathLaw_shifted_history_joint N y m]
  congr 1
  ext h : 1
  exact canonicalShiftedHistoryKernel_eq_restart N m h

/-- Deterministic-time Markov property, event form: for every measurable
prefix event `G` and every measurable future-path event `F`,
`P_y(Y_{0:m} ∈ G, Y_{m+·} ∈ F) = ∫_{G} P_{h_m}(F) dP_y^{0:m}(h)`. -/
theorem pointPathLaw_prefix_shift_event
    (N : StrategicWorldModel S X A)
    (y : JointState S X) (m : ℕ)
    (G : Set ((i : Finset.Iic m) → JointState S X)) (hG : MeasurableSet G)
    (F : Set (ℕ → JointState S X)) (hF : MeasurableSet F) :
    N.pathLaw (Measure.dirac y)
      ((Preorder.frestrictLe m) ⁻¹' G ∩
        (pathTailShift (S := S) (X := X) m) ⁻¹' F) =
    ∫⁻ h in G,
      canonicalFutureKernel N (h ⟨m, Finset.mem_Iic.mpr le_rfl⟩) F
      ∂((N.pathLaw (Measure.dirac y)).map (Preorder.frestrictLe m)) := by
  have hPair : Measurable (fun w : ℕ → JointState S X =>
      (Preorder.frestrictLe m w, pathTailShift (S := S) (X := X) m w)) :=
    (Preorder.measurable_frestrictLe m).prodMk (measurable_pathTailShift m)
  have hEvent :
      (Preorder.frestrictLe m) ⁻¹' G ∩
          (pathTailShift (S := S) (X := X) m) ⁻¹' F =
        (fun w : ℕ → JointState S X =>
          (Preorder.frestrictLe m w,
            pathTailShift (S := S) (X := X) m w)) ⁻¹' (G ×ˢ F) := rfl
  rw [hEvent, ← Measure.map_apply hPair (hG.prod hF),
    pointPathLaw_shifted_lastState_joint N y m,
    Measure.compProd_apply_prod hG hF]
  rfl

end PermanssonResearch.RegimeExit
