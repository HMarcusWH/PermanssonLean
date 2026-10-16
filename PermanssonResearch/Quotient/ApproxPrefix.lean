import PermanssonResearch.Probability.EventTVCalculus
import PermanssonResearch.Probability.CompProdPushforward
import PermanssonResearch.ConstitutiveQuasi.PathOutput
import PermanssonLean.Probability.FinitePrefixTV
import PermanssonLean.Quotient.KernelIntertwining
import Mathlib.Tactic

/-!
# E1.1–E1.2 — approximate type-respecting quotients: linear finite-prefix bound

For a measurable map `q : Y → Q`, a fine kernel `K` on `Y` and a coarse kernel
`K̄` on `Q`, the ONE-STEP QUOTIENT DEFECT (spec V20.30) is

  `η = sup_y ‖q_# K(y,·) − K̄(q y,·)‖_TV`,

encoded as the hypothesis `HasQuotientDefect q K K̄ η` (a bound for EVERY fine
state, not only baseline-visited ones). The projected fine process `q(Y_t)` need
not be Markov. Nevertheless, from the SAME fine initial state `y`,

  `TV((q^{0:T})_# P_y^{K,0:T}, P_{q y}^{K̄,0:T}) ≤ min(1, T η)`        (V20.31)

(`approxQuotient_prefix_tv_le_min`).

## Proof (last-step hybrid; no fibre disintegration, no countability)

Write `μ_T` for the fine prefix law and `ν_T` for the coarse one. By the
Ionescu--Tulcea recursion (`finitePrefixLaw_succ`),
`μ_{T+1} = (μ_T ⊗ K_T).map append`, and projection commutes with appending.
With `A = (μ_T ⊗ q_#K_T)` read through `q^{0:T}`, the hybrid
`H = (q^{0:T}_# μ_T) ⊗ K̄_T` and `C = ν_T ⊗ K̄_T`:

* `TV(A, H) ≤ η` — same first law, kernels within `η` at every fine history
  (`eventTotalVariation_compProd_right_le`);
* `TV(H, C) ≤ TV(q^{0:T}_# μ_T, ν_T)` — same kernel
  (`eventTotalVariation_compProd_left_le`, Hahn decomposition);

so `δ_{T+1} ≤ δ_T + η` and `δ_0 = 0`. The sharper geometric bound
`1 − (1 − η)^T` (V20.32) is NOT claimed here: it needs a separate
common-mass / coupling construction (anchor E1.5, OPEN).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.Quotient

set_option autoImplicit false

open PermanssonLean PermanssonLean.ProbabilitySupport
open PermanssonResearch.Probability

universe uY uQ uZ
variable {Y : Type uY} {Q : Type uQ}
variable [MeasurableSpace Y] [MeasurableSpace Q]

/-- Coordinatewise projection of a finite history. -/
def prefixMap (q : Y → Q) (T : ℕ) :
    ((i : Finset.Iic T) → Y) → ((i : Finset.Iic T) → Q) :=
  fun h i => q (h i)

theorem measurable_prefixMap {q : Y → Q} (hq : Measurable q) (T : ℕ) :
    Measurable (prefixMap q T) :=
  Measurable.of_eval fun i => hq.comp (measurable_pi_apply i)

/-- **E1.1** One-step quotient defect bound, for EVERY fine state. -/
def HasQuotientDefect (q : Y → Q) (K : Kernel Y Y) (Kbar : Kernel Q Q)
    (η : ℝ) : Prop :=
  ∀ y, eventTotalVariation ((K y).map q) (Kbar (q y)) ≤ η

/-- Append the next state to a history (the map used by mathlib's
`partialTraj_succ_of_le`). -/
noncomputable def appendLast {Z : Type uZ} [MeasurableSpace Z] (T : ℕ) :
    ((i : Finset.Iic T) → Z) × Z → ((i : Finset.Iic (T+1)) → Z) :=
  IicProdIoc (X := fun _ : ℕ => Z) T (T+1) ∘
    Prod.map id (MeasurableEquiv.piSingleton (X := fun _ : ℕ => Z) T)

theorem measurable_appendLast {Z : Type uZ} [MeasurableSpace Z] (T : ℕ) :
    Measurable (appendLast (Z := Z) T) :=
  measurable_IicProdIoc.comp
    (measurable_id.prodMap
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ => Z) T).measurable)

/-- Ionescu--Tulcea recursion of the frozen finite-prefix law. -/
theorem finitePrefixLaw_succ {Z : Type uZ} [MeasurableSpace Z]
    (K : Kernel Z Z) [IsMarkovKernel K] (z : Z) (T : ℕ) :
    finitePrefixLaw K z (T+1) =
      (finitePrefixLaw K z T ⊗ₘ stationaryPrefixKernel K T).map
        (appendLast T) := by
  have hπ := (MeasurableEquiv.piSingleton (X := fun _ : ℕ => Z) T).measurable
  unfold finitePrefixLaw
  have hI : Measurable (IicProdIoc (X := fun _ : ℕ => Z) T (T+1)) :=
    measurable_IicProdIoc
  rw [Kernel.partialTraj_succ_of_le (Nat.zero_le T),
    Kernel.map_apply _ hI, Kernel.comp_apply,
    ← Measure.compProd_eq_comp_prod, Measure.compProd_map hπ,
    Measure.map_map hI (measurable_id.prodMap hπ)]
  rfl

/-- Projection commutes with appending. -/
theorem prefixMap_appendLast (q : Y → Q) (T : ℕ)
    (p : ((i : Finset.Iic T) → Y) × Y) :
    prefixMap q (T+1) (appendLast T p) =
      appendLast T (prefixMap q T p.1, q p.2) := by
  funext i
  simp only [prefixMap, appendLast, Function.comp, Prod.map, id, IicProdIoc]
  split_ifs
  · rfl
  · simp [MeasurableEquiv.piSingleton, eq_rec_constant]

/-- The zero-transition prefix laws agree after projection. -/
theorem finitePrefixLaw_zero_map (q : Y → Q) (hq : Measurable q)
    (K : Kernel Y Y) (Kbar : Kernel Q Q) (y : Y) :
    (finitePrefixLaw K y 0).map (prefixMap q 0) = finitePrefixLaw Kbar (q y) 0 := by
  simp only [finitePrefixLaw, Kernel.partialTraj_zero, Kernel.deterministic_apply]
  rw [Measure.map_dirac' (measurable_prefixMap hq 0)]
  congr 1

/-- **E1.2 (linear form).** `TV(q-projected fine prefix, coarse prefix) ≤ T η`. -/
theorem approxQuotient_prefix_tv_le_linear
    {q : Y → Q} (hq : Measurable q)
    (K : Kernel Y Y) (Kbar : Kernel Q Q)
    [IsMarkovKernel K] [IsMarkovKernel Kbar]
    {η : ℝ} (hη : 0 ≤ η) (hdef : HasQuotientDefect q K Kbar η)
    (y : Y) (T : ℕ) :
    eventTotalVariation ((finitePrefixLaw K y T).map (prefixMap q T))
      (finitePrefixLaw Kbar (q y) T) ≤ T * η := by
  induction T with
  | zero =>
      rw [finitePrefixLaw_zero_map q hq K Kbar y, eventTotalVariation_self]
      simp
  | succ T ih =>
      haveI : IsMarkovKernel ((stationaryPrefixKernel K T).map q) :=
        Kernel.IsMarkovKernel.map _ hq
      set μ := finitePrefixLaw K y T
      set ν := finitePrefixLaw Kbar (q y) T
      set qP := prefixMap q T
      have hqP : Measurable qP := measurable_prefixMap hq T
      -- fine projected law at T+1 through the append map
      have hfine : (finitePrefixLaw K y (T+1)).map (prefixMap q (T+1)) =
          ((μ ⊗ₘ (stationaryPrefixKernel K T).map q).map (Prod.map qP id)).map
            (appendLast T) := by
        rw [finitePrefixLaw_succ,
          Measure.map_map (measurable_prefixMap hq (T+1)) (measurable_appendLast T),
          Measure.compProd_map hq,
          Measure.map_map (hqP.prodMap measurable_id) (measurable_id.prodMap hq),
          Measure.map_map (measurable_appendLast T)
            ((hqP.prodMap measurable_id).comp (measurable_id.prodMap hq))]
        congr 1
        funext p
        exact prefixMap_appendLast q T p
      have hcoarse : finitePrefixLaw Kbar (q y) (T+1) =
          (ν ⊗ₘ stationaryPrefixKernel Kbar T).map (appendLast T) :=
        finitePrefixLaw_succ Kbar (q y) T
      have hhyb : (μ.map qP) ⊗ₘ stationaryPrefixKernel Kbar T =
          (μ ⊗ₘ (stationaryPrefixKernel Kbar T).comap qP hqP).map
            (Prod.map qP id) :=
        compProd_map_left_eq_map_compProd_comap μ hqP _
      -- one-step defect at every fine history
      have hstep : eventTotalVariation
          (μ ⊗ₘ (stationaryPrefixKernel K T).map q)
          (μ ⊗ₘ (stationaryPrefixKernel Kbar T).comap qP hqP) ≤ η := by
        refine eventTotalVariation_compProd_right_le μ _ _ hη fun h => ?_
        rw [Kernel.map_apply _ hq, Kernel.comap_apply]
        exact hdef (h ⟨T, Finset.mem_Iic.mpr le_rfl⟩)
      have hA : eventTotalVariation
          ((μ ⊗ₘ (stationaryPrefixKernel K T).map q).map (Prod.map qP id))
          ((μ.map qP) ⊗ₘ stationaryPrefixKernel Kbar T) ≤ η := by
        rw [hhyb]
        exact (eventTotalVariation_map_le _ _ (hqP.prodMap measurable_id)).trans hstep
      have hB : eventTotalVariation
          ((μ.map qP) ⊗ₘ stationaryPrefixKernel Kbar T)
          (ν ⊗ₘ stationaryPrefixKernel Kbar T) ≤ T * η :=
        (eventTotalVariation_compProd_left_le _ _ _).trans ih
      rw [hfine, hcoarse]
      calc
        eventTotalVariation
            (((μ ⊗ₘ (stationaryPrefixKernel K T).map q).map (Prod.map qP id)).map
              (appendLast T))
            ((ν ⊗ₘ stationaryPrefixKernel Kbar T).map (appendLast T)) ≤
            eventTotalVariation
              ((μ ⊗ₘ (stationaryPrefixKernel K T).map q).map (Prod.map qP id))
              (ν ⊗ₘ stationaryPrefixKernel Kbar T) :=
          eventTotalVariation_map_le _ _ (measurable_appendLast T)
        _ ≤ η + T * η :=
          (eventTotalVariation_triangle _ _ _).trans (add_le_add hA hB)
        _ = ((T+1 : ℕ) : ℝ) * η := by push_cast; ring

/-- **E1.2 (V20.31).** `TV ≤ min(1, T η)`. -/
theorem approxQuotient_prefix_tv_le_min
    {q : Y → Q} (hq : Measurable q)
    (K : Kernel Y Y) (Kbar : Kernel Q Q)
    [IsMarkovKernel K] [IsMarkovKernel Kbar]
    {η : ℝ} (hη : 0 ≤ η) (hdef : HasQuotientDefect q K Kbar η)
    (y : Y) (T : ℕ) :
    eventTotalVariation ((finitePrefixLaw K y T).map (prefixMap q T))
      (finitePrefixLaw Kbar (q y) T) ≤ min 1 (T * η) := by
  exact le_min (eventTotalVariation_le_one _ _)
    (approxQuotient_prefix_tv_le_linear hq K Kbar hη hdef y T)

/-- Exact intertwining is the `η = 0` case (AQ1). -/
theorem hasQuotientDefect_zero_of_intertwines
    (q : Y → Q) (K : Kernel Y Y) (Kbar : Kernel Q Q)
    [IsMarkovKernel K] [IsMarkovKernel Kbar]
    (h : ∀ y, (K y).map q = Kbar (q y)) :
    HasQuotientDefect q K Kbar 0 := by
  intro y
  rw [h y, eventTotalVariation_self]

/-! ### Typed strategic-world specialization -/

universe uS uX uA uSb uXb uAb
variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {Sb : Type uSb} {Xb : Type uXb} {Ab : Type uAb}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace Sb] [MeasurableSpace Xb] [MeasurableSpace Ab]

/-- Approximate kernel intertwining through a TYPE-RESPECTING compression
`q = q_S × q_X` (surjective, measurable, coordinate-preserving). -/
def ApproxKernelIntertwines
    (Qc : TypeRespectingStateCompression S X Sb Xb)
    (M : StrategicWorldModel S X A) (Mbar : StrategicWorldModel Sb Xb Ab)
    (η : ℝ) : Prop :=
  HasQuotientDefect Qc.stateMap M.inducedKernel Mbar.inducedKernel η

/-- Exact `KernelIntertwines` (frozen Theorem 7.4b hypothesis) gives defect 0. -/
theorem approxKernelIntertwines_zero_of_exact
    (Qc : TypeRespectingStateCompression S X Sb Xb)
    (M : StrategicWorldModel S X A) (Mbar : StrategicWorldModel Sb Xb Ab)
    (h : KernelIntertwines Qc M.inducedKernel Mbar.inducedKernel) :
    ApproxKernelIntertwines Qc M Mbar 0 := by
  letI := StrategicWorldModel.inducedKernel_isMarkov M
  letI := StrategicWorldModel.inducedKernel_isMarkov Mbar
  exact hasQuotientDefect_zero_of_intertwines _ _ _
    (kernelIntertwines_apply Qc _ _ h)

/-- **E1.2, canonical path laws.** The `T`-prefix of the compressed fine
canonical path law is within `min(1, T η)` of the coarse canonical prefix from
the compressed initial state. -/
theorem approxQuotient_pathLaw_prefix_tv_le
    (Qc : TypeRespectingStateCompression S X Sb Xb)
    (M : StrategicWorldModel S X A) (Mbar : StrategicWorldModel Sb Xb Ab)
    {η : ℝ} (hη : 0 ≤ η) (hdef : ApproxKernelIntertwines Qc M Mbar η)
    (y : JointState S X) (T : ℕ) :
    eventTotalVariation
      (((M.pathLaw (Measure.dirac y)).map (Preorder.frestrictLe T)).map
        (prefixMap Qc.stateMap T))
      ((Mbar.pathLaw (Measure.dirac (Qc.stateMap y))).map
        (Preorder.frestrictLe T)) ≤ min 1 (T * η) := by
  letI := StrategicWorldModel.inducedKernel_isMarkov M
  letI := StrategicWorldModel.inducedKernel_isMarkov Mbar
  rw [ConstitutiveQuasi.pathLaw_finitePrefix_eq,
    ConstitutiveQuasi.pathLaw_finitePrefix_eq]
  exact approxQuotient_prefix_tv_le_min Qc.stateMap_measurable _ _ hη hdef y T

end PermanssonResearch.Quotient
