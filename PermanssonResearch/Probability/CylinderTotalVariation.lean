import PermanssonResearch.Probability.EventTVCalculus
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent

/-! Bounds on the actual finite-coordinate laws extend to the entire product
sigma-algebra. Approximation uses the sum of the two original finite measures. -/

open MeasureTheory ProbabilityTheory Set
open scoped symmDiff ENNReal

namespace PermanssonResearch.Probability

open PermanssonLean.ProbabilitySupport

theorem eventTotalVariation_le_of_generating_ring
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {C : Set (Set Ω)} (hC : IsSetRing C) (huniv : univ ∈ C)
    (hgen : mΩ = MeasurableSpace.generateFrom C) {e : ℝ}
    (hbound : ∀ s ∈ C, |μ.real s - ν.real s| ≤ e) :
    eventTotalVariation μ ν ≤ e := by
  unfold eventTotalVariation
  apply csSup_le (eventTVCandidates_nonempty μ ν)
  rintro _ ⟨s, hs, rfl⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨t, ht, happrox⟩ :=
    exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := μ + ν) hC
      ⟨{univ}, Set.countable_singleton _, by simpa using huniv, by simp⟩
      hgen hs (ENNReal.ofReal_pos.mpr hε)
  have htm : MeasurableSet t := by
    rw [hgen]
    exact MeasurableSpace.measurableSet_generateFrom ht
  have hreal : μ.real (t ∆ s) + ν.real (t ∆ s) < ε := by
    have hh := (ENNReal.toReal_lt_toReal (measure_ne_top (μ + ν) _) 
      ENNReal.ofReal_ne_top).mpr happrox
    simpa [Measure.add_apply, ENNReal.toReal_add (measure_ne_top μ _)
      (measure_ne_top ν _), ENNReal.toReal_ofReal hε.le, Measure.real] using hh
  have hμ := abs_measureReal_sub_le_measureReal_symmDiff
    htm.nullMeasurableSet hs.nullMeasurableSet (μ := μ)
  have hν := abs_measureReal_sub_le_measureReal_symmDiff
    htm.nullMeasurableSet hs.nullMeasurableSet (μ := ν)
  calc
    |μ.real s - ν.real s| =
        |(μ.real s - μ.real t) + (μ.real t - ν.real t) +
          (ν.real t - ν.real s)| := by congr 1; ring
    _ ≤ (|μ.real s - μ.real t| + |μ.real t - ν.real t|) +
        |ν.real t - ν.real s| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |μ.real t - ν.real t| + |μ.real t - μ.real s| +
        |ν.real t - ν.real s| := by rw [abs_sub_comm (μ.real s)]; ring
    _ ≤ e + (μ.real (t ∆ s) + ν.real (t ∆ s)) := by
      linarith [hbound t ht]
    _ ≤ e + ε := by linarith

/-- No topology, atomicity or Markov property is required for this extension. -/
theorem path_eventTotalVariation_le_of_prefixes
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ ν : Measure (∀ n, X n)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {e : ℝ}
    (hprefix : ∀ n, eventTotalVariation
      (μ.map (Finset.Iic n).restrict) (ν.map (Finset.Iic n).restrict) ≤ e) :
    eventTotalVariation μ ν ≤ e := by
  apply eventTotalVariation_le_of_generating_ring μ ν
    isSetRing_measurableCylinders (univ_mem_measurableCylinders X)
    generateFrom_measurableCylinders.symm
  intro s hs
  rw [measurableCylinders_nat] at hs
  simp only [mem_iUnion, mem_singleton_iff] at hs
  obtain ⟨n, t, ht, rfl⟩ := hs
  have hm : Measurable ((Finset.Iic n).restrict : (∀ n, X n) → _) :=
    Measurable.of_eval (fun _ => measurable_pi_apply _)
  haveI : IsProbabilityMeasure (μ.map (Finset.Iic n).restrict) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  haveI : IsProbabilityMeasure (ν.map (Finset.Iic n).restrict) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  have hh := (abs_measureReal_sub_le_eventTotalVariation
    (μ.map (Finset.Iic n).restrict) (ν.map (Finset.Iic n).restrict) ht).trans (hprefix n)
  simpa [Measure.real, Measure.map_apply hm ht, cylinder] using hh

end PermanssonResearch.Probability
