import PermanssonResearch.Quotient.GeometricPrefix
import PermanssonResearch.Probability.ProjectedCommonSubkernel

/-! The actual common-part/RN construction for Q-GEOMETRIC. The sufficient
kernel RN instance is explicit and is not erased by the quotient wrapper. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.Quotient

open PermanssonLean.ProbabilitySupport PermanssonResearch.Probability

variable {Y Q : Type*} [MeasurableSpace Y] [MeasurableSpace Q]
variable [MeasurableSpace.CountableOrCountablyGenerated Y Q]

noncomputable def projectedCommonKernel (q : Y → Q) (hq : Measurable q)
    (K : Kernel Y Y) [IsMarkovKernel K]
    (Kbar : Kernel Q Q) [IsMarkovKernel Kbar] : Kernel Y Y :=
  let P := K.map q
  let B := Kbar.comap q hq
  letI : IsMarkovKernel P := Kernel.IsMarkovKernel.map K hq
  liftProjectedDensity q K (clippedProjectedDensity (commonPartKernel P B) P)

theorem projectedCommonKernel_le (q : Y → Q) (hq : Measurable q)
    (K : Kernel Y Y) [IsMarkovKernel K]
    (Kbar : Kernel Q Q) [IsMarkovKernel Kbar] :
    projectedCommonKernel q hq K Kbar ≤ K := by
  let P := K.map q
  let B := Kbar.comap q hq
  letI : IsMarkovKernel P := Kernel.IsMarkovKernel.map K hq
  exact liftProjectedDensity_le hq K
    (measurable_clippedProjectedDensity (commonPartKernel P B) P)
    (clippedProjectedDensity_le_one (commonPartKernel P B) P)

instance projectedCommonKernel_isFinite (q : Y → Q) (hq : Measurable q)
    (K : Kernel Y Y) [IsMarkovKernel K]
    (Kbar : Kernel Q Q) [IsMarkovKernel Kbar] :
    IsFiniteKernel (projectedCommonKernel q hq K Kbar) :=
  isFiniteKernel_of_le (projectedCommonKernel_le q hq K Kbar)

theorem map_projectedCommonKernel (q : Y → Q) (hq : Measurable q)
    (K : Kernel Y Y) [IsMarkovKernel K]
    (Kbar : Kernel Q Q) [IsMarkovKernel Kbar] (y : Y) :
    (projectedCommonKernel q hq K Kbar y).map q =
      commonPartKernel (K.map q) (Kbar.comap q hq) y := by
  letI : IsMarkovKernel (K.map q) := Kernel.IsMarkovKernel.map K hq
  change (liftProjectedDensity q K
    (clippedProjectedDensity (commonPartKernel (K.map q) (Kbar.comap q hq)) (K.map q)) y).map q = _
  rw [map_liftProjectedDensity hq K
    (measurable_clippedProjectedDensity _ _) y]
  rw [← Kernel.map_apply K hq y]
  exact withDensity_clippedProjectedDensity _ _ (commonPartKernel_le_left _ _) y

theorem projectedCommonKernel_map_le (q : Y → Q) (hq : Measurable q)
    (K : Kernel Y Y) [IsMarkovKernel K]
    (Kbar : Kernel Q Q) [IsMarkovKernel Kbar] (y : Y) :
    (projectedCommonKernel q hq K Kbar y).map q ≤ Kbar (q y) := by
  letI : IsMarkovKernel (K.map q) := Kernel.IsMarkovKernel.map K hq
  rw [map_projectedCommonKernel q hq K Kbar y]
  exact commonPartKernel_le_right _ _ y

theorem projectedCommonKernel_mass (q : Y → Q) (hq : Measurable q)
    (K : Kernel Y Y) [IsMarkovKernel K]
    (Kbar : Kernel Q Q) [IsMarkovKernel Kbar]
    {η : ℝ} (hdef : HasQuotientDefect q K Kbar η) (y : Y) :
    ENNReal.ofReal (1 - η) ≤ projectedCommonKernel q hq K Kbar y Set.univ := by
  let P := K.map q
  let B := Kbar.comap q hq
  letI : IsMarkovKernel P := Kernel.IsMarkovKernel.map K hq
  have hTV : HasUniformEventTVBound P B η := by
    intro z
    simpa [P, B, Kernel.map_apply _ hq, Kernel.comap_apply] using hdef z
  have hm := one_sub_le_commonPartKernel_real_univ_of_uniformTV P B hTV y
  have hENN : ENNReal.ofReal (1 - η) ≤ commonPartKernel P B y Set.univ :=
    (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).mpr hm
  have hmass : projectedCommonKernel q hq K Kbar y Set.univ =
      commonPartKernel P B y Set.univ := by
    rw [← map_projectedCommonKernel q hq K Kbar y]
    simp [Measure.map_apply hq]
  rwa [hmass]

/-- Geometric projected-prefix TV from every actual fine start. No Markov
property of the projected fine process is required. -/
theorem approxQuotient_prefix_tv_le_geometric
    {q : Y → Q} (hq : Measurable q)
    (K : Kernel Y Y) [IsMarkovKernel K]
    (Kbar : Kernel Q Q) [IsMarkovKernel Kbar]
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hdef : HasQuotientDefect q K Kbar η) (y : Y) (T : ℕ) :
    eventTotalVariation ((finitePrefixLaw K y T).map (prefixMap q T))
      (finitePrefixLaw Kbar (q y) T) ≤ 1 - (1 - η) ^ T := by
  exact approxQuotient_prefix_tv_le_geometric_of_subkernel hq K Kbar
    (projectedCommonKernel q hq K Kbar)
    (projectedCommonKernel_le q hq K Kbar)
    (projectedCommonKernel_map_le q hq K Kbar) hη0 hη1
    (projectedCommonKernel_mass q hq K Kbar hdef) y T

end PermanssonResearch.Quotient
