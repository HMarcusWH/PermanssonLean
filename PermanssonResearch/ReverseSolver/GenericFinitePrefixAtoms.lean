import PermanssonResearch.ReverseSolver.FiniteStrategicRealization
import PermanssonResearch.ReverseSolver.CanonicalAtomMass
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Tactic

/-!
# D0-E: generic canonical finite-prefix atomic transition recurrence

Unlike the D0-C matrix-specific atom formula, this holds for any measurable
Markov kernel. We use the actual mathlib finitePrefixLaw, not an invented
finite-word process, to transfer PR #42's one-step kernel equality to paths.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace FiniteStrategicPathBridge

open PermanssonLean.ProbabilitySupport

/-- The actual canonical finite-prefix law factors into its prefix and the
conditional transition. This is not a synthetic trajectory surrogate. -/
theorem prefix_transition_pair {Y : Type*} [MeasurableSpace Y]
    (K : Kernel Y Y) [IsMarkovKernel K] (y : Y) (T : ℕ) :
    finitePrefixLaw K y T ⊗ₘ stationaryPrefixKernel K T =
      (finitePrefixLaw K y (T+1)).map
        (fun (w : (i : Finset.Iic (T+1)) → Y) =>
          (Preorder.frestrictLe₂ (π := fun _ : ℕ => Y) T.le_succ w,
           w ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩)) := by
  let κ : (k : ℕ) → Kernel ((i : Finset.Iic k) → Y) Y :=
    fun k => stationaryPrefixKernel K k
  let x₀ := singletonPrefix y
  have hpair := Kernel.partialTraj_compProd_eq_map_traj
    (X := fun _ : ℕ => Y) (κ := κ)
    (a := 0) (b := T) (Nat.zero_le T) (x₀ := x₀)
  have hprefix := congrArg
    (fun Q : Kernel ((i : Finset.Iic 0) → Y)
      ((i : Finset.Iic (T+1)) → Y) => Q x₀)
    (Kernel.traj_map_frestrictLe (X := fun _ : ℕ => Y)
      (κ := κ) 0 (T+1))
  rw [Kernel.map_apply _ (by fun_prop)] at hprefix
  calc
    finitePrefixLaw K y T ⊗ₘ stationaryPrefixKernel K T =
        (Kernel.traj κ 0 x₀).map
          (fun w : ℕ → Y => (Preorder.frestrictLe T w, w (T+1))) := by
            simpa [finitePrefixLaw, κ, x₀] using hpair
    _ = (finitePrefixLaw K y (T+1)).map
        (fun (w : (i : Finset.Iic (T+1)) → Y) =>
          (Preorder.frestrictLe₂ (π := fun _ : ℕ => Y) T.le_succ w,
           w ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩)) := by
            change (Kernel.traj κ 0 x₀).map
                (fun w : ℕ → Y => (Preorder.frestrictLe T w, w (T+1))) =
              (Kernel.partialTraj (X := fun _ : ℕ => Y) κ 0 (T+1) x₀).map
                (fun w : ((i : Finset.Iic (T+1)) → Y) =>
                  (Preorder.frestrictLe₂ (π := fun _ : ℕ => Y)
                    T.le_succ w,
                   w ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩))
            rw [← hprefix]
            have hleft : Measurable
                (Preorder.frestrictLe₂
                  (π := fun _ : ℕ => Y) T.le_succ) :=
              Preorder.measurable_frestrictLe₂ T.le_succ
            have hright : Measurable
                (fun w : ((i : Finset.Iic (T+1)) → Y) =>
                  w ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩) :=
              measurable_pi_apply _
            have hmPair :
                Measurable (fun w : ((i : Finset.Iic (T+1)) → Y) =>
                  (Preorder.frestrictLe₂ (π := fun _ : ℕ => Y)
                    T.le_succ w,
                    w ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩)) :=
              hleft.prodMk hright
            rw [Measure.map_map hmPair (Preorder.measurable_frestrictLe (T+1))]
            rfl

private def prefixPair {Y : Type*} (T : ℕ) :
    ((i : Finset.Iic (T+1)) → Y) →
      (((i : Finset.Iic T) → Y) × Y) :=
  fun w =>
    (Preorder.frestrictLe₂ (π := fun _ : ℕ => Y) T.le_succ w,
      w ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩)

private theorem prefixPair_injective {Y : Type*} (T : ℕ) :
    Function.Injective (prefixPair (Y := Y) T) := by
  intro w v h
  have hp := congrArg Prod.fst h
  have hl := congrArg Prod.snd h
  funext i
  by_cases hi : (i : ℕ) ≤ T
  · have hpoint := congrFun hp ⟨(i : ℕ), Finset.mem_Iic.mpr hi⟩
    simpa [prefixPair, Preorder.frestrictLe₂] using hpoint
  · have hibound : (i : ℕ) ≤ T+1 := Finset.mem_Iic.mp i.property
    have hieq : (i : ℕ) = T+1 := by omega
    have heq : i = ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩ := Subtype.ext hieq
    simpa [prefixPair, heq] using hl

/-- The canonical atom mass at T+1 factors into the previous prefix atom
and the genuine one-step transition, for every Markov kernel. -/
theorem finitePrefixLaw_singleton_succ {Y : Type*} [MeasurableSpace Y]
    (K : Kernel Y Y) [IsMarkovKernel K]
    (y : Y) (T : ℕ) (w : (i : Finset.Iic (T+1)) → Y)
    (hpoint : MeasurableSet
      ({Preorder.frestrictLe₂ (π := fun _ : ℕ => Y) T.le_succ w} :
        Set ((i : Finset.Iic T) → Y)))
    (hlast : MeasurableSet ({w ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩} : Set Y))
    (hwhole : MeasurableSet ({w} : Set ((i : Finset.Iic (T+1)) → Y))) :
    finitePrefixLaw K y (T+1) {w} =
      finitePrefixLaw K y T
        {Preorder.frestrictLe₂ (π := fun _ : ℕ => Y) T.le_succ w} *
      K (w ⟨T, Finset.mem_Iic.mpr T.le_succ⟩)
        {w ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩} := by
  let pre := Preorder.frestrictLe₂ (π := fun _ : ℕ => Y) T.le_succ w
  let z := w ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩
  let μ := finitePrefixLaw K y T
  let ν := finitePrefixLaw K y (T+1)
  let κ := stationaryPrefixKernel K T
  have hpair := congrArg
    (fun ρ : Measure (((i : Finset.Iic T) → Y) × Y) =>
      ρ {(pre, z)}) (prefix_transition_pair K y T)
  change (μ ⊗ₘ κ) {(pre,z)} =
    (ν.map (prefixPair T)) {(pre,z)} at hpair
  have hpre : prefixPair (Y := Y) T ⁻¹' {(pre,z)} = {w} := by
    ext u
    change prefixPair T u = prefixPair T w ↔ u = w
    exact (prefixPair_injective T).eq_iff
  have hprod : ({pre} ×ˢ {z} : Set (((i : Finset.Iic T) → Y) × Y)) =
      {(pre,z)} := by
    ext p
    rcases p with ⟨a,b⟩
    simp
  have hpairsingleton : MeasurableSet
      ({(pre,z)} : Set (((i : Finset.Iic T) → Y) × Y)) := by
    rw [← hprod]
    exact hpoint.prod hlast
  have hleft : Measurable
      (Preorder.frestrictLe₂
        (π := fun _ : ℕ => Y) T.le_succ) :=
    Preorder.measurable_frestrictLe₂ T.le_succ
  have hright : Measurable
      (fun u : ((i : Finset.Iic (T+1)) → Y) =>
        u ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩) :=
    measurable_pi_apply _
  have hmPair : Measurable (prefixPair (Y := Y) T) := by
    unfold prefixPair
    exact hleft.prodMk hright
  rw [Measure.map_apply hmPair hpairsingleton, hpre] at hpair
  rw [← hprod, Measure.compProd_apply_prod hpoint hlast] at hpair
  rw [lintegral_singleton' (Kernel.measurable_coe κ hlast) pre] at hpair
  change ν {w} = μ {pre} * _
  have hstep : κ pre {z} =
      K (w ⟨T, Finset.mem_Iic.mpr T.le_succ⟩) {z} := rfl
  rw [← hstep, mul_comm]
  exact hpair.symm

end FiniteStrategicPathBridge
end ReverseSolver
end PermanssonResearch
