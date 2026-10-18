import PermanssonResearch.Quotient.ApproxPrefix

/-!
# Q-GEOMETRIC: propagation of a projected common subkernel

The fine projection is not assumed Markov. The recursive object is retained
fine-prefix mass; its projection is dominated by the coarse prefix law.
Construction of the subkernel (finite or jointly measurable RN) is separate.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.Quotient

open PermanssonLean.ProbabilitySupport PermanssonResearch.Probability

variable {Y Q : Type*} [MeasurableSpace Y] [MeasurableSpace Q]

private theorem subPrefixLaw_succ (R : Kernel Y Y) [IsFiniteKernel R]
    (y : Y) (T : ℕ) :
    finitePrefixLaw R y (T + 1) =
      (finitePrefixLaw R y T ⊗ₘ stationaryPrefixKernel R T).map (appendLast T) := by
  have hπ := (MeasurableEquiv.piSingleton (X := fun _ : ℕ => Y) T).measurable
  have hI : Measurable (IicProdIoc (X := fun _ : ℕ => Y) T (T+1)) :=
    measurable_IicProdIoc
  unfold finitePrefixLaw
  rw [Kernel.partialTraj_succ_of_le (Nat.zero_le T),
    Kernel.map_apply _ hI, Kernel.comp_apply,
    ← Measure.compProd_eq_comp_prod, Measure.compProd_map hπ,
    Measure.map_map hI (measurable_id.prodMap hπ)]
  rfl

private theorem compProd_mono_sub
    {H Z : Type*} [MeasurableSpace H] [MeasurableSpace Z]
    {μ ν : Measure H} [SFinite μ] [SFinite ν]
    {R K : Kernel H Z} [IsSFiniteKernel R] [IsSFiniteKernel K]
    (hμ : μ ≤ ν) (hR : R ≤ K) : μ ⊗ₘ R ≤ ν ⊗ₘ K := by
  apply Measure.le_iff.mpr
  intro E hE
  rw [Measure.compProd_apply hE, Measure.compProd_apply hE]
  exact lintegral_mono' hμ (fun h => hR h _)

/-- Projected fine-prefix subprobabilities are dominated by the actual coarse
prefix law, even when the fine projection has memory. -/
theorem projected_subPrefix_le
    {q : Y → Q} (hq : Measurable q)
    (R : Kernel Y Y) [IsFiniteKernel R]
    (Kbar : Kernel Q Q) [IsMarkovKernel Kbar]
    (hproj : ∀ y, (R y).map q ≤ Kbar (q y)) (y : Y) (T : ℕ) :
    (finitePrefixLaw R y T).map (prefixMap q T) ≤ finitePrefixLaw Kbar (q y) T := by
  induction T with
  | zero => exact (finitePrefixLaw_zero_map q hq R Kbar y).le
  | succ T ih =>
    let μ := finitePrefixLaw R y T
    let ν := finitePrefixLaw Kbar (q y) T
    let qP := prefixMap q T
    have hqP : Measurable qP := measurable_prefixMap hq T
    haveI : IsFiniteMeasure μ := by
      dsimp [μ, finitePrefixLaw]
      infer_instance
    haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
    have hfine : (finitePrefixLaw R y (T+1)).map (prefixMap q (T+1)) =
        ((μ ⊗ₘ (stationaryPrefixKernel R T).map q).map (Prod.map qP id)).map
          (appendLast T) := by
      rw [subPrefixLaw_succ,
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
    have hrows : (stationaryPrefixKernel R T).map q ≤
        (stationaryPrefixKernel Kbar T).comap qP hqP := by
      intro h
      rw [Kernel.map_apply _ hq, Kernel.comap_apply]
      exact hproj (h ⟨T, Finset.mem_Iic.mpr le_rfl⟩)
    rw [hfine, hcoarse]
    apply measureMap_mono (hf := measurable_appendLast T)
    calc
      (μ ⊗ₘ (stationaryPrefixKernel R T).map q).map (Prod.map qP id)
          ≤ (μ ⊗ₘ (stationaryPrefixKernel Kbar T).comap qP hqP).map
            (Prod.map qP id) :=
        measureMap_mono (compProd_mono_sub le_rfl hrows) (hqP.prodMap measurable_id)
      _ = (μ.map qP) ⊗ₘ stationaryPrefixKernel Kbar T := hhyb.symm
      _ ≤ ν ⊗ₘ stationaryPrefixKernel Kbar T := compProd_mono_sub ih le_rfl

/-- The measurable common-subkernel geometric bound. Every-row domination and
mass retention remain explicit; no arbitrary-measurable RN theorem is assumed. -/
theorem approxQuotient_prefix_tv_le_geometric_of_subkernel
    {q : Y → Q} (hq : Measurable q)
    (K : Kernel Y Y) [IsMarkovKernel K]
    (Kbar : Kernel Q Q) [IsMarkovKernel Kbar]
    (R : Kernel Y Y) [IsFiniteKernel R]
    (hRK : R ≤ K) (hproj : ∀ y, (R y).map q ≤ Kbar (q y))
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hmass : ∀ y, ENNReal.ofReal (1 - η) ≤ R y Set.univ)
    (y : Y) (T : ℕ) :
    eventTotalVariation ((finitePrefixLaw K y T).map (prefixMap q T))
      (finitePrefixLaw Kbar (q y) T) ≤ 1 - (1 - η) ^ T := by
  haveI : IsFiniteMeasure (finitePrefixLaw R y T) := by
    unfold finitePrefixLaw
    infer_instance
  have hleft := measureMap_mono (finitePrefixLaw_mono hRK y T)
    (measurable_prefixMap hq T)
  have hright := projected_subPrefix_le hq R Kbar hproj y T
  have htv := eventTotalVariation_le_one_sub_commonMass hleft hright
  have hpow := finitePrefixLaw_univ_ge_pow R hmass y T
  have hbase : 0 ≤ 1 - η := sub_nonneg.mpr hη1
  have hfinite : finitePrefixLaw R y T Set.univ ≠ ∞ := by finiteness
  rw [← ENNReal.ofReal_pow hbase] at hpow
  have hreal := (ENNReal.ofReal_le_iff_le_toReal hfinite).mp hpow
  have hmap : ((finitePrefixLaw R y T).map (prefixMap q T)).real Set.univ =
      (finitePrefixLaw R y T).real Set.univ := by
    simp [Measure.real, Measure.map_apply (measurable_prefixMap hq T)]
  rw [hmap] at htv
  exact htv.trans (sub_le_sub_left hreal 1)

end PermanssonResearch.Quotient
