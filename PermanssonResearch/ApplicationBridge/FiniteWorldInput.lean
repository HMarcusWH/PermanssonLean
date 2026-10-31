import PermanssonResearch.ReverseSolver.RationalKernel
import Mathlib.MeasureTheory.Measure.Sum
import Mathlib.Probability.Kernel.Basic
import Mathlib.Tactic

/-!
# ApplicationBridge — exact finite α/P/U input

This is the *rational arithmetic* input-to-joint-row bridge. All three
probabilistic primitives must carry separate stochastic-row proofs; a JSON
status flag or a Python receipt does not supply these proofs. The convention is
α(a | s,x), P(x' | s,x,a), U(s' | s,x,a,x'). Their multiplication is NOT a
claim of empirical identification or of correspondence to an externally
supplied `StrategicWorldModel` until the separate measure-kernel bridge exists.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch.ApplicationBridge

set_option autoImplicit false

/-- A finite rational source, with each primitive normalized separately.
    The declared feasible-action relation is preserved. Infeasible action
    probabilities must be zero; P and U rows on infeasible action indices are
    explicitly normalized *extensions*, not supplied or identified source
    primitives. Only feasible controlled actions are source-meaningful. -/
structure FiniteWorldInput (ns nx na : ℕ) where
  feasible : Fin ns → Fin nx → Fin na → Prop
  alpha : Fin ns → Fin nx → Fin na → ℚ
  world : Fin ns → Fin nx → Fin na → Fin nx → ℚ
  update : Fin ns → Fin nx → Fin na → Fin nx → Fin ns → ℚ
  alpha_nonneg : ∀ s x a, 0 ≤ alpha s x a
  alpha_zero_of_infeasible : ∀ s x a, ¬ feasible s x a → alpha s x a = 0
  world_nonneg : ∀ s x a xp, 0 ≤ world s x a xp
  update_nonneg : ∀ s x a xp sp, 0 ≤ update s x a xp sp
  alpha_sum_one : ∀ s x, (∑ a : Fin na, alpha s x a) = 1
  world_sum_one : ∀ s x a, (∑ xp : Fin nx, world s x a xp) = 1
  update_sum_one : ∀ s x a xp, (∑ sp : Fin ns, update s x a xp sp) = 1

namespace FiniteWorldInput
variable {ns nx na : ℕ} (w : FiniteWorldInput ns nx na)

/-- Fixed-action joint transition atom. No selection by the hidden state is
    permitted here: the caller chooses the same `a` for the declared row.
    The consumer must separately prove `w.feasible y.1 y.2 a` for every
    positive-mass source state before treating this as an admissible policy. -/
def controlledAtom (a : Fin na) (y z : Fin ns × Fin nx) : ℚ :=
  w.world y.1 y.2 a z.2 * w.update y.1 y.2 a z.2 z.1

/-- The α/P/U-induced next-joint-state atom, in the source's declared order. -/
def inducedAtom (y z : Fin ns × Fin nx) : ℚ :=
  ∑ a : Fin na, w.alpha y.1 y.2 a * w.controlledAtom a y z

theorem controlledAtom_nonneg (a : Fin na) (y z : Fin ns × Fin nx) :
    0 ≤ w.controlledAtom a y z :=
  mul_nonneg (w.world_nonneg y.1 y.2 a z.2)
    (w.update_nonneg y.1 y.2 a z.2 z.1)

theorem inducedAtom_nonneg (y z : Fin ns × Fin nx) :
    0 ≤ w.inducedAtom y z := by
  exact Finset.sum_nonneg (fun a _ =>
    mul_nonneg (w.alpha_nonneg y.1 y.2 a) (w.controlledAtom_nonneg a y z))

/-- Every fixed-action row has mass one over the ENTIRE joint destination. -/
theorem controlledAtom_sum_one (a : Fin na) (y : Fin ns × Fin nx) :
    (∑ z : Fin ns × Fin nx, w.controlledAtom a y z) = 1 := by
  calc
    (∑ z : Fin ns × Fin nx, w.controlledAtom a y z) =
        ∑ xp : Fin nx, ∑ sp : Fin ns,
          w.world y.1 y.2 a xp * w.update y.1 y.2 a xp sp := by
          simp only [controlledAtom, Fintype.sum_prod_type]
          exact Finset.sum_comm
    _ = ∑ xp : Fin nx, w.world y.1 y.2 a xp *
          (∑ sp : Fin ns, w.update y.1 y.2 a xp sp) := by
          simp only [Finset.mul_sum]
    _ = ∑ xp : Fin nx, w.world y.1 y.2 a xp := by
          simp only [w.update_sum_one, mul_one]
    _ = 1 := w.world_sum_one y.1 y.2 a

/-- The induced α/P/U matrix is stochastic. The proof genuinely uses all
    three primitive row-normalization certificates rather than trusting a
    precomputed matrix or a report's verification flag. -/
theorem inducedAtom_sum_one (y : Fin ns × Fin nx) :
    (∑ z : Fin ns × Fin nx, w.inducedAtom y z) = 1 := by
  calc
    (∑ z : Fin ns × Fin nx, w.inducedAtom y z) =
        ∑ a : Fin na, w.alpha y.1 y.2 a *
          (∑ z : Fin ns × Fin nx, w.controlledAtom a y z) := by
          simp only [inducedAtom, Finset.mul_sum]
          exact Finset.sum_comm
    _ = ∑ a : Fin na, w.alpha y.1 y.2 a := by
          simp only [w.controlledAtom_sum_one, mul_one]
    _ = 1 := w.alpha_sum_one y.1 y.2

/-- Atomwise representation: the primitive factorization, not an arbitrary
    independently supplied numerical matrix, determines the next-step row. -/
theorem inducedAtom_eq_primitives (y z : Fin ns × Fin nx) :
    w.inducedAtom y z =
      ∑ a : Fin na, w.alpha y.1 y.2 a *
        w.world y.1 y.2 a z.2 * w.update y.1 y.2 a z.2 z.1 := by
  simp only [inducedAtom, controlledAtom, mul_assoc]


/-- The certified rational row is also an actual discrete probability kernel
    on the finite joint strategic/world state space. -/
noncomputable def inducedRationalKernel :
    Kernel (Fin ns × Fin nx) (Fin ns × Fin nx) where
  toFun := fun y =>
    ∑ z : Fin ns × Fin nx,
      (ENNReal.ofReal (w.inducedAtom y z : ℝ)) • Measure.dirac z
  measurable' := Measurable.of_discrete

/-- Exact atomwise correspondence between the rational α/P/U factorization
    and its canonical finite discrete Markov kernel. -/
theorem inducedRationalKernel_singleton (y z : Fin ns × Fin nx) :
    w.inducedRationalKernel y {z} =
      ENNReal.ofReal (w.inducedAtom y z : ℝ) := by
  classical
  simp [inducedRationalKernel, Measure.finsetSum_apply,
    Measure.smul_apply, Pi.single_apply]

/-- Genuine Markov normalization: no mass has been dropped or added when
    lifting the rational α/P/U rows to a measure-theoretic kernel. -/
instance inducedRationalKernel_isMarkov :
    IsMarkovKernel (w.inducedRationalKernel) := by
  refine ⟨fun y => ⟨?_⟩⟩
  have hreal : (∑ z : Fin ns × Fin nx, (w.inducedAtom y z : ℝ)) = 1 := by
    exact_mod_cast w.inducedAtom_sum_one y
  have hnonneg : ∀ z ∈ (Finset.univ : Finset (Fin ns × Fin nx)),
      0 ≤ (w.inducedAtom y z : ℝ) := by
    intro z _
    exact_mod_cast w.inducedAtom_nonneg y z
  change (∑ z : Fin ns × Fin nx,
    (ENNReal.ofReal (w.inducedAtom y z : ℝ)) •
      Measure.dirac z) Set.univ = 1
  simp only [Measure.finsetSum_apply, Measure.smul_apply]
  simp only [Measure.dirac_apply' _ MeasurableSet.univ,
    Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => hnonneg z (Finset.mem_univ z))]
  rw [hreal]
  simp

end FiniteWorldInput
end PermanssonResearch.ApplicationBridge
