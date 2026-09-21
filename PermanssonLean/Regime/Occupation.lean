import PermanssonLean.Regime.Assumption41
import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Measure.DiracProba

open Filter MeasureTheory ProbabilityTheory Set

namespace PermanssonLean

universe uS uX uA uH

variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]

namespace RegimeSpecification

/-- Uniform probability measure on a positive finite horizon. -/
noncomputable def uniformFinProbability
    (T : ℕ) (hT : 0 < T) :
    ProbabilityMeasure (Fin T) := by
  letI : MeasurableSpace (Fin T) := ⊤
  letI : Nonempty (Fin T) := ⟨⟨0, hT⟩⟩
  exact ⟨uniformOn Set.univ, inferInstance⟩

/-- Pathwise empirical descriptor occupation law

\[
\widehat\nu_T^h = \frac1T\sum_{t=0}^{T-1}\delta_{h(Y_t)}
\]

for a strictly positive horizon T.  It is implemented as the push-forward
of the uniform probability law on `Fin T`, so unit mass is enforced by
the return type rather than proved downstream each time.
-/
noncomputable def empiricalOccupation
    (Σ : RegimeSpecification (JointState S X) H)
    (w : ℕ → JointState S X)
    (T : ℕ) (hT : 0 < T) :
    ProbabilityMeasure H := by
  letI : MeasurableSpace (Fin T) := ⊤
  letI : Nonempty (Fin T) := ⟨⟨0, hT⟩⟩
  let u : ProbabilityMeasure (Fin T) :=
    ⟨uniformOn Set.univ, inferInstance⟩
  exact u.map (fun i => Σ.descriptor (w (i : ℕ)))

/-- Bundle the canonical infinite path law as a probability measure. -/
noncomputable def pathProbability
    (M : StrategicWorldModel S X A)
    (λ : ProbabilityMeasure (JointState S X)) :
    ProbabilityMeasure (ℕ → JointState S X) :=
  ⟨M.pathLaw λ.toMeasure, inferInstance⟩

/-- Descriptor law at a fixed time under a declared initial probability law. -/
noncomputable def descriptorLaw
    (M : StrategicWorldModel S X A)
    (Σ : RegimeSpecification (JointState S X) H)
    (λ : ProbabilityMeasure (JointState S X))
    (t : ℕ) :
    ProbabilityMeasure H :=
  (pathProbability M λ).map (fun w => Σ.descriptor (w t))

/-- The target law is a limiting occupation law for a particular initial
probability law under the frozen convergence semantics. -/
def IsLimitingOccupationLaw
    (M : StrategicWorldModel S X A)
    (Σ : RegimeSpecification (JointState S X) H)
    (λ : ProbabilityMeasure (JointState S X)) : Prop :=
  Σ.convergenceMode.holds
    (M.pathLaw λ.toMeasure)
    (empiricalOccupation Σ)
    Σ.target

/-- Basin-reachable descriptor nondegeneracy:
the family of descriptor laws reachable from point initializations in B₀
at finite times contains at least two distinct probability measures. -/
def IsDescriptorNondegenerate
    (M : StrategicWorldModel S X A)
    (Σ : RegimeSpecification (JointState S X) H) : Prop :=
  ∃ y₁ ∈ Σ.basin, ∃ t₁ : ℕ,
    ∃ y₂ ∈ Σ.basin, ∃ t₂ : ℕ,
      descriptorLaw M Σ (diracProba y₁) t₁ ≠
        descriptorLaw M Σ (diracProba y₂) t₂

end RegimeSpecification

end PermanssonLean
