import PermanssonLean.Regime.Relevance
import Mathlib.Topology.MetricSpace.Basic

open MeasureTheory ProbabilityTheory

namespace PermanssonLean

/-!
# Nuisance padding exclusion

Path-law semantic core of Proposition 7.5 in Permansson v0.1.7.

A padded representation `Y × R` is observed through a frozen relevance map that
ignores the auxiliary coordinate.  If the baseline and intervention projected
relevance-path laws agree with the corresponding unpadded laws, every grounded
property value and every grounded metric gap is preserved.  In particular, a
change to the auxiliary coordinate alone cannot manufacture grounded
constitutive status.
-/

namespace RegimeSpecification

universe uY uR uH uG uZ

variable {Y : Type uY} {R : Type uR} {H : Type uH}
variable {G : Type uG} {Z : Type uZ}
variable [MeasurableSpace Y] [MeasurableSpace R]
variable [MeasurableSpace H] [MeasurableSpace G]

/-- A padding certificate records that the padded relevance map discards the
auxiliary coordinate exactly: g_tilde(y,r) = g(y). -/
structure NuisancePaddingRelevance
    (spec : RegimeSpecification Y H)
    (paddedSpec : RegimeSpecification (Y × R) H)
    (g : GroundedRelevanceMap spec G)
    (gPadded : GroundedRelevanceMap paddedSpec G) : Prop where
  observe_ignores_padding :
    ∀ y r, gPadded.observe (y, r) = g.observe y

namespace NuisancePaddingRelevance

/-- Coordinatewise relevance observations of a padded path depend only on its
unpadded first-coordinate path. -/
theorem pathMap_eq
    (spec : RegimeSpecification Y H)
    (paddedSpec : RegimeSpecification (Y × R) H)
    (g : GroundedRelevanceMap spec G)
    (gPadded : GroundedRelevanceMap paddedSpec G)
    (h : NuisancePaddingRelevance spec paddedSpec g gPadded)
    (w : ℕ → Y × R) :
    gPadded.pathMap w =
      g.pathMap (fun n => (w n).1) := by
  funext n
  exact h.observe_ignores_padding (w n).1 (w n).2

end NuisancePaddingRelevance

/-- Frozen baseline/intervention equality of projected relevance-path laws
before and after nuisance padding.  This is the exact hypothesis used in
Proposition 7.5. -/
structure NuisancePaddingPathLawMatch
    (spec : RegimeSpecification Y H)
    (paddedSpec : RegimeSpecification (Y × R) H)
    (g : GroundedRelevanceMap spec G)
    (gPadded : GroundedRelevanceMap paddedSpec G)
    (baseline intervention : ProbabilityMeasure (ℕ → Y))
    (paddedBaseline paddedIntervention :
      ProbabilityMeasure (ℕ → (Y × R))) : Prop where
  baseline_match :
    g.pushPath baseline = gPadded.pushPath paddedBaseline
  intervention_match :
    g.pushPath intervention = gPadded.pushPath paddedIntervention

/-- Every grounded property has the same baseline value before and after
padding when the frozen projected path laws match. -/
theorem nuisancePadding_grounded_baseline_value_eq
    (spec : RegimeSpecification Y H)
    (paddedSpec : RegimeSpecification (Y × R) H)
    (g : GroundedRelevanceMap spec G)
    (gPadded : GroundedRelevanceMap paddedSpec G)
    (baseline intervention : ProbabilityMeasure (ℕ → Y))
    (paddedBaseline paddedIntervention :
      ProbabilityMeasure (ℕ → (Y × R)))
    (h : NuisancePaddingPathLawMatch
      spec paddedSpec g gPadded
      baseline intervention paddedBaseline paddedIntervention)
    (ψG : RegimePropertyMap G Z) :
    ψG (g.pushPath baseline) =
      ψG (gPadded.pushPath paddedBaseline) := by
  exact congrArg ψG h.baseline_match

/-- Every grounded property has the same intervention value before and after
padding when the frozen projected path laws match. -/
theorem nuisancePadding_grounded_intervention_value_eq
    (spec : RegimeSpecification Y H)
    (paddedSpec : RegimeSpecification (Y × R) H)
    (g : GroundedRelevanceMap spec G)
    (gPadded : GroundedRelevanceMap paddedSpec G)
    (baseline intervention : ProbabilityMeasure (ℕ → Y))
    (paddedBaseline paddedIntervention :
      ProbabilityMeasure (ℕ → (Y × R)))
    (h : NuisancePaddingPathLawMatch
      spec paddedSpec g gPadded
      baseline intervention paddedBaseline paddedIntervention)
    (ψG : RegimePropertyMap G Z) :
    ψG (g.pushPath intervention) =
      ψG (gPadded.pushPath paddedIntervention) := by
  exact congrArg ψG h.intervention_match

/-- Proposition 7.5, metric-gap form: nuisance padding preserves every
grounded constitutive gap exactly. -/
theorem nuisancePadding_grounded_gap_eq
    [MetricSpace Z]
    (spec : RegimeSpecification Y H)
    (paddedSpec : RegimeSpecification (Y × R) H)
    (g : GroundedRelevanceMap spec G)
    (gPadded : GroundedRelevanceMap paddedSpec G)
    (baseline intervention : ProbabilityMeasure (ℕ → Y))
    (paddedBaseline paddedIntervention :
      ProbabilityMeasure (ℕ → (Y × R)))
    (h : NuisancePaddingPathLawMatch
      spec paddedSpec g gPadded
      baseline intervention paddedBaseline paddedIntervention)
    (ψG : RegimePropertyMap G Z) :
    dist
        (ψG (g.pushPath baseline))
        (ψG (g.pushPath intervention))
      =
    dist
        (ψG (gPadded.pushPath paddedBaseline))
        (ψG (gPadded.pushPath paddedIntervention)) := by
  rw [h.baseline_match, h.intervention_match]

/-- No-new-constitution form of Proposition 7.5: if a grounded property is
unchanged by the unpadded intervention, nuisance padding alone cannot make the
same grounded property change. -/
theorem nuisancePadding_cannot_create_grounded_change
    (spec : RegimeSpecification Y H)
    (paddedSpec : RegimeSpecification (Y × R) H)
    (g : GroundedRelevanceMap spec G)
    (gPadded : GroundedRelevanceMap paddedSpec G)
    (baseline intervention : ProbabilityMeasure (ℕ → Y))
    (paddedBaseline paddedIntervention :
      ProbabilityMeasure (ℕ → (Y × R)))
    (h : NuisancePaddingPathLawMatch
      spec paddedSpec g gPadded
      baseline intervention paddedBaseline paddedIntervention)
    (ψG : RegimePropertyMap G Z)
    (hNoChange :
      ψG (g.pushPath baseline) = ψG (g.pushPath intervention)) :
    ψG (gPadded.pushPath paddedBaseline) =
      ψG (gPadded.pushPath paddedIntervention) := by
  rw [← h.baseline_match, ← h.intervention_match]
  exact hNoChange

end RegimeSpecification

end PermanssonLean
