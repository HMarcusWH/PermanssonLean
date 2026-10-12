import PermanssonResearch.MultipleLimit.FiniteMarkovMartingaleStep
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Tactic

/-!
# C53-02 — real canonical next-event conditional probability

This bridge uses mathlib's conditional distribution for the ACTUAL
Ionescu–Tulcea infinite trajectory measure. The law of the next state,
given the entire measurable finite past, is the original transition
kernel at the last observed state. This is the stochastic input to the
centered Markov martingale proof, and does not assume independence.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory


namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteMarkovConditionalEvent

open FiniteCanonicalPath
open FiniteMarkovMartingaleStep
open FiniteKernelRealBridge

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [StandardBorelSpace Y]
variable [Nonempty Y] [DecidableEq Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- A real conditional expectation identity for all finite-past measurable
sets, derived from the exact canonical trajectory conditional kernel,
not a row-wise heuristic or an IID substitution. -/
theorem canonical_next_singleton_conditional_probability
    (μ : ProbabilityMeasure Y) (t : ℕ) (z : Y) :
    (canonicalPathLaw K μ.toMeasure)
      ⟦{w : ℕ → Y | w (t+1) = z} | pastFiltration (Y := Y) t⟧
      =ᵐ[canonicalPathLaw K μ.toMeasure]
      (fun w : ℕ → Y => realTransition K (w t) z) := by
  let P : Measure (ℕ → Y) := canonicalPathLaw K μ.toMeasure
  let X : (ℕ → Y) → ((i : Finset.Iic t) → Y) :=
    Preorder.frestrictLe t
  let Ynext : (ℕ → Y) → Y := fun w => w (t+1)
  have hX : Measurable X := by
    fun_prop
  have hY : Measurable Ynext := by
    fun_prop
  have hkernel :
      (condDistrib Ynext X P) =ᵐ[P.map X]
        PermanssonLean.ProbabilitySupport.stationaryPrefixKernel K t := by
    have hpair := CanonicalKernelMarginals.canonical_transition_pair
      K μ.toMeasure t
    apply ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      hX hY
    simpa only [P, X, Ynext] using hpair.symm
  have hkernelPath :
      ∀ᵐ w ∂P,
        condDistrib Ynext X P (X w) =
          PermanssonLean.ProbabilitySupport.stationaryPrefixKernel K t (X w) :=
    ae_of_ae_map hX.aemeasurable hkernel
  have hReal :
      (fun w : ℕ → Y =>
        (condDistrib Ynext X P (X w)).real ({z} : Set Y)) =ᵐ[P]
      (fun w : ℕ → Y => realTransition K (w t) z) := by
    filter_upwards [hkernelPath] with w hw
    have hm := congrArg (fun ν : Measure Y => ν.real ({z} : Set Y)) hw
    simpa [realTransition, X,
      PermanssonLean.ProbabilitySupport.stationaryPrefixKernel,
      Measure.real_def] using hm
  have hExp :
      (fun w : ℕ → Y =>
        (condDistrib Ynext X P (X w)).real ({z} : Set Y)) =ᵐ[P]
      P⟦Ynext ⁻¹' ({z} : Set Y) | (inferInstance :
        MeasurableSpace ((i : Finset.Iic t) → Y)).comap X⟧ := by
    exact ProbabilityTheory.condDistrib_ae_eq_condExp
      (μ := P) (X := X) (Y := Ynext)
      hX hY (measurableSet_singleton z)
  change P⟦Ynext ⁻¹' ({z} : Set Y) |
      Filtration.piLE (X := fun _ : ℕ => Y) t⟧ =ᵐ[P] _
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact hExp.symm.trans hReal

end FiniteMarkovConditionalEvent
end MultipleLimit
end PermanssonResearch
