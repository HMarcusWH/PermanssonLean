import PermanssonResearch.ReverseSolver.NonlinearPeriodThreeRealization
import PermanssonResearch.MultipleLimit.FiniteOccupationRandomLaw
import PermanssonResearch.MultipleLimit.FiniteCanonicalPath
import Mathlib.Tactic

/-!
# NEXT-06.2 — original native canonical occupation: kernel and limit bridge

This is the actual S = Fin 3, X = Bool, A = Bool alpha -> P -> U
induced kernel, not a Unit × Fin 6 physical-world reencoding.

The native one-step kernel is proved deterministic using its certified
36-atom theorem and finite measure extensionality. The full ORIGINAL typed
pathLaw is then linked directly to the existing genuine finite-state
canonical empirical occupation convergence theorem. This is a first
substage only: recurrent-class identification, explicit weights,
Boolean score and policy-class optimization remain separate obligations.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology ProbabilityTheory

namespace PermanssonResearch.ReverseSolver.NonlinearPeriodThree

open PermanssonLean
open PermanssonResearch.MultipleLimit.FiniteCanonicalPath
open PermanssonResearch.MultipleLimit.FiniteOccupationRandomLaw
open PermanssonResearch.MultipleLimit.FiniteStateOccupation

set_option autoImplicit false
attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- A useful *derived* deterministic joint-state kernel, not a replacement
for the genuine physical P or strategic update U. -/
noncomputable def nextStateKernel (policy : State → Bool) :
    Kernel State State :=
  Kernel.deterministic (nextState policy) Measurable.of_discrete

/-- Genuine alpha-P-U induced rows coincide with the next-state Dirac.
Singleton measure extensionality is valid *here* because native State is
a finite six-atom type; it must not be used for P-05 measurable spaces. -/
theorem native_inducedKernel_eq_deterministic (policy : State → Bool) :
    (typedModel policy).inducedKernel = nextStateKernel policy := by
  apply Kernel.ext
  intro y
  apply Measure.ext_of_singleton
  intro z
  rw [induced_kernel_singleton]
  simp [nextStateKernel, Kernel.deterministic_apply,
    Measure.dirac_apply', Pi.single_apply]

/-- Same native induced stochastic process for every physical controller,
with actual infinite original pathLaw and genuine empirical weak limit.
This does NOT yet calculate selected bottom classes, their weights,
the nonlinear Boolean score, or the deterministic policy-class maximum. -/
theorem native_actual_occupation_ae_limit
    (policy : State → Bool) (μ : ProbabilityMeasure State) :
    ∀ᵐ w ∂(typedModel policy).pathLaw μ.toMeasure,
      Tendsto
        (fun n : ℕ =>
          empiricalOccupation w (n+1) (Nat.succ_pos n))
        atTop (𝓝 (physicalOccupationLimit
          (typedModel policy).inducedKernel w)) := by
  rw [typed_pathLaw_eq_canonical (typedModel policy) μ.toMeasure]
  exact physicalOccupationLimit_ae_correct
    (typedModel policy).inducedKernel μ

end PermanssonResearch.ReverseSolver.NonlinearPeriodThree
