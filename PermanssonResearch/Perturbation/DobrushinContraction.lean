import PermanssonResearch.Perturbation.DirectDualContraction
import PermanssonResearch.Probability.CouplingDualBound
import PermanssonResearch.Probability.KantorovichTV
import PermanssonLean.Probability.FinitePrefixTV

/-! Derived certificates for the original all-probability-law contraction.
The TV route retains its diameter/minimum-distance factor. A genuine coupling
route directly integrates the given metric, including the zero-factor case. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace PermanssonResearch.Perturbation
open PermanssonResearch.Probability PermanssonLean.ProbabilitySupport
variable {Y : Type*} [PseudoMetricSpace Y] [MeasurableSpace Y]

theorem isW1Contraction_of_row_couplings (K : Kernel Y Y) [IsMarkovKernel K]
    {ρ : ℝ} (hρ : 0≤ρ)
    (hrows : ∀ x y,∃ γ : IntegrableCoupling (K x) (K y),γ.cost≤ρ*dist x y) :
    IsW1Contraction K ρ := by
  apply isW1Contraction_of_test_images K hρ
  intro f hf x y
  obtain ⟨γ,hγ⟩ := hrows x y
  exact (γ.dual_bound f hf).trans hγ

theorem isW1Contraction_of_tv_rows (K : Kernel Y Y) [IsMarkovKernel K]
    {D ell β : ℝ} (hD : 0≤D) (hell : 0<ell) (hβ : 0≤β)
    (hdiam : ∀ x y : Y,dist x y≤D)
    (hsep : ∀ x y : Y,x≠y→ell≤dist x y)
    (hrows : ∀ x y,eventTotalVariation (K x) (K y)≤β) :
    IsW1Contraction K (D*β/ell) := by
  have hρ : 0≤D*β/ell := div_nonneg (mul_nonneg hD hβ) hell.le
  apply isW1Contraction_of_test_images K hρ
  intro f hf x y
  by_cases hxy : x=y
  · subst y
    simp
  · have hw := (W1DualLE.of_eventTV (K x) (K y) hD hdiam).mono
      (mul_le_mul_of_nonneg_left (hrows x y) hD)
    calc
      _ ≤ D*β := hw f hf
      _ = (D*β/ell)*ell := (div_mul_cancel₀ _ hell.ne').symm
      _ ≤ (D*β/ell)*dist x y := mul_le_mul_of_nonneg_left (hsep x y hxy) hρ

noncomputable def dobrushinCoefficient [Fintype Y] [Nonempty Y] (K : Kernel Y Y) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun p : Y × Y => eventTotalVariation (K p.1) (K p.2))

theorem row_tv_le_dobrushin [Fintype Y] [Nonempty Y] (K : Kernel Y Y) (x y : Y) :
    eventTotalVariation (K x) (K y)≤dobrushinCoefficient K :=
  Finset.le_sup' (fun p : Y × Y => eventTotalVariation (K p.1) (K p.2))
    (Finset.mem_univ (x,y))

theorem dobrushin_bounds [Fintype Y] [Nonempty Y] (K : Kernel Y Y) [IsMarkovKernel K] :
    0≤dobrushinCoefficient K ∧ dobrushinCoefficient K≤1 := by
  constructor
  · let x : Y := Classical.choice inferInstance
    exact (eventTotalVariation_nonneg (K x) (K x)).trans (row_tv_le_dobrushin K x x)
  · exact Finset.sup'_le _ _ (fun p _ => eventTotalVariation_le_one (K p.1) (K p.2))

/-- On the discrete unit metric the actual maximum row TV is a contraction
coefficient for all probability laws, with no first-moment restriction. -/
theorem isW1Contraction_dobrushin [Fintype Y] [Nonempty Y] [DecidableEq Y]
    (K : Kernel Y Y) [IsMarkovKernel K]
    (hmetric : ∀ x y : Y,dist x y=if x=y then 0 else 1) :
    IsW1Contraction K (dobrushinCoefficient K) := by
  have hd (x y : Y) : dist x y≤1 := by rw [hmetric]; split_ifs <;> norm_num
  have hs (x y : Y) (hxy : x≠y) : (1:ℝ)≤dist x y := by simp [hmetric,hxy]
  simpa using isW1Contraction_of_tv_rows K (by norm_num : (0:ℝ)≤1)
    (by norm_num : (0:ℝ)<1) (dobrushin_bounds K).1 hd hs (row_tv_le_dobrushin K)

/-- An actual common minorizing measure yields the TV row bound directly;
no measurable common-part selection or duality oracle is assumed. -/
theorem doeblin_tv_rows [Nonempty Y] (K : Kernel Y Y) [IsMarkovKernel K]
    (reference : Measure Y) [IsProbabilityMeasure reference] {ε : ℝ} (hε : 0≤ε)
    (hminor : ∀ x,ENNReal.ofReal ε • reference≤K x) (x y : Y) :
    eventTotalVariation (K x) (K y)≤1-ε := by
  let ξ := ENNReal.ofReal ε • reference
  letI : IsFiniteMeasure ξ := ⟨lt_of_le_of_lt (hminor x Set.univ) (by simp)⟩
  have hh := eventTotalVariation_le_one_sub_commonMass (hminor x) (hminor y)
  simpa [ξ,Measure.real,ENNReal.toReal_ofReal hε] using hh

theorem isW1Contraction_doeblin [Nonempty Y] (K : Kernel Y Y) [IsMarkovKernel K]
    (reference : Measure Y) [IsProbabilityMeasure reference] {ε D ell : ℝ}
    (hε0 : 0≤ε) (hε1 : ε≤1) (hD : 0≤D) (hell : 0<ell)
    (hdiam : ∀ x y : Y,dist x y≤D)
    (hsep : ∀ x y : Y,x≠y→ell≤dist x y)
    (hminor : ∀ x,ENNReal.ofReal ε • reference≤K x) :
    IsW1Contraction K (D*(1-ε)/ell) :=
  isW1Contraction_of_tv_rows K hD hell (sub_nonneg.mpr hε1) hdiam hsep
    (doeblin_tv_rows K reference hε0 hminor)

end PermanssonResearch.Perturbation
