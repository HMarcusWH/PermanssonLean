import PermanssonResearch.X1.Comparison
import PermanssonResearch.MultipleLimit.CanonicalKernelMarginals
import PermanssonLean.Regime.ConstitutiveMargin

/-!+# X1: genuine canonical horizon output and original margin transport

This reuses the existing canonical marginal-power theorem. The finite recurrence
below is proved equal to the ACTUAL alpha/P/U path-law property, and its infimum
is proved equal to the original frozen constitutive margin. Reflection of the
separate rational calculation's numerical fractions remains an additional gate.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.X1

set_option autoImplicit false
open PermanssonLean PermanssonLean.RegimeSpecification
open PermanssonResearch.MultipleLimit

attribute [local instance] StrategicWorldModel.inducedKernel_isMarkov

/-- Backward finite matrix evaluation of terminal repletion. This is NOT killed
persistence: intermediate exits are allowed, exactly as the declared property. -/
noncomputable def kernelTerminal (K : Kernel Y Y) : ℕ → Y → ℝ≥0∞
  | 0, y => if y ∈ region then 1 else 0
  | n+1, y => ∑ z : Y, kernelTerminal K n z * K y {z}

theorem kernelTerminal_eq_power (K : Kernel Y Y) [IsMarkovKernel K] (n : ℕ) (y : Y) :
    kernelTerminal K n y = (K ^ n) y region := by
  induction n generalizing y with
  | zero => simp [kernelTerminal, Kernel.id_apply, Measure.dirac_apply]
  | succ n ih =>
      calc
        kernelTerminal K (n+1) y = ∫⁻ z, (K ^ n) z region ∂K y := by
          rw [lintegral_fintype]
          simp only [kernelTerminal, ih]
        _ = (K ^ (n+1)) y region := by
          simpa only [Nat.add_comm 1 n, pow_one] using
            (Kernel.pow_add_apply_eq_lintegral K 1 n y
              (show MeasurableSet region from MeasurableSet.of_discrete)).symm

/-- Baseline evaluation using the explicit primitive-derived transition entries. -/
noncomputable def primitiveTerminal (m : Mode) : ℕ → Y → ℝ≥0∞
  | 0, y => if y ∈ region then 1 else 0
  | n+1, y => ∑ z : Y, primitiveTerminal m n z * transitionEntry m y z

theorem primitiveTerminal_eq_kernelTerminal (m : Mode) (n : ℕ) (y : Y) :
    primitiveTerminal m n y = kernelTerminal (model m).inducedKernel n y := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
      simp only [primitiveTerminal, kernelTerminal, ih, inducedKernel_atom_entry]

/-- Equality with the ORIGINAL full-path property, for any typed model on this
state space, including every actual typed intervention. No surrogate path law. -/
theorem baselineProperty_eq_kernelTerminal (M : StrategicWorldModel Memory Bool Action)
    (y : Y) :
    baselinePropertyValue property M y =
      (kernelTerminal M.inducedKernel propertyHorizon y).toReal := by
  have hm := CanonicalKernelMarginals.canonical_eval_eq_kernel_pow M.inducedKernel y propertyHorizon
  rw [← FiniteCanonicalPath.typed_pathLaw_eq_canonical M (Measure.dirac y)] at hm
  have hevent := congrArg (fun μ : Measure Y => μ region) hm
  rw [Measure.map_apply (measurable_pi_apply propertyHorizon)
    (show MeasurableSet region from MeasurableSet.of_discrete)] at hevent
  rw [kernelTerminal_eq_power]
  exact congrArg ENNReal.toReal hevent

noncomputable def finiteEffect (m : Mode) (J : AdmissibleStrategicIntervention (family m))
    (y : Y) : ℝ :=
  dist (kernelTerminal (model m).inducedKernel propertyHorizon y).toReal
    (kernelTerminal J.intervention.apply.inducedKernel propertyHorizon y).toReal

/-- Exact original pointwise-effect transport for the same typed interventions. -/
theorem constitutiveEffect_eq_finiteEffect (m : Mode)
    (J : AdmissibleStrategicIntervention (family m)) (y : Y) :
    constitutiveEffect (model m) property J y = finiteEffect m J y := by
  unfold constitutiveEffect finiteEffect
  change dist (baselinePropertyValue property (model m) y)
    (baselinePropertyValue property J.intervention.apply y) = _
  rw [baselineProperty_eq_kernelTerminal, baselineProperty_eq_kernelTerminal]

/-- Genuine original kappa, on the corrected WHOLE-region comparison object,
equals the infimum of actual finite-kernel evaluations. Numerical proof of the
external rational receipt's particular fractions is NOT assumed or asserted. -/
theorem constitutiveMargin_eq_finiteInf (m : Mode)
    (J : AdmissibleStrategicIntervention (family m)) :
    constitutiveMargin (model m) (specification m) (family m) property (comparisonSet m) J =
      sInf (finiteEffect m J '' comparisonStarts) := by
  unfold constitutiveMargin
  rw [show constitutiveEffect (model m) property J = finiteEffect m J from
    funext (constitutiveEffect_eq_finiteEffect m J)]
  rfl

end PermanssonResearch.X1
