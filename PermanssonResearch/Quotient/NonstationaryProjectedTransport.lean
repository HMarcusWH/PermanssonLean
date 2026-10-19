import PermanssonResearch.Probability.DependentHistoryCommonMass
import PermanssonResearch.Probability.CompProdPushforward
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Tactic

/-!
# NEXT-04 — actual nonstationary projected-history common mass

`H n` and `G n` can be fine/coarse histories containing 0..n observations.
The kernels are chronological: the n-th kernel takes history n to history n+1.
No Markov assumption on the projected fine process is made. A finite common
fine-history subkernel R is supplied with rowwise measurable projection and
coarse domination, including fine histories outside baseline support.

This is a conditional *constructive transport* from source kernels and initial
subprobability to the actual `DependentHistory.evolution` laws, not an assumed
prefix-TV inequality. The requested original-margin/discounted application
requires a separate property and canonical full-path identification adapter.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.Quotient.NonstationaryProjected

open PermanssonLean.ProbabilitySupport
open PermanssonResearch.Probability
open PermanssonResearch.Probability.DependentHistory

set_option autoImplicit false

universe u v
variable {H : ℕ → Type u} {G : ℕ → Type v}
variable [∀ n, MeasurableSpace (H n)] [∀ n, MeasurableSpace (G n)]

/-- Composing and projecting a finite fine-history row is dominated by a
coarse-history transition if the *actual* projected common row is dominated.
The first-factor pushforward is proved using the shared compProd provider. -/
private theorem projected_compProd_step {n : ℕ}
    (ρ : Measure (H n)) [IsFiniteMeasure ρ]
    (R : Kernel (H n) (H (n+1))) [IsFiniteKernel R]
    (L : Kernel (G n) (G (n+1))) [IsMarkovKernel L]
    (q0 : H n → G n) (hq0 : Measurable q0)
    (q1 : H (n+1) → G (n+1)) (hq1 : Measurable q1)
    (hrows : R.map q1 ≤ L.comap q0 hq0) :
    ((ρ ⊗ₘ R).map Prod.snd).map q1 ≤
      ((ρ.map q0) ⊗ₘ L).map Prod.snd := by
  have hcomp : (ρ ⊗ₘ R.map q1) ≤ ρ ⊗ₘ (L.comap q0 hq0) :=
    compProd_mono le_rfl hrows
  have hnatural :
      ((ρ ⊗ₘ R).map Prod.snd).map q1 =
        (ρ ⊗ₘ R.map q1).map Prod.snd := by
    rw [Measure.map_map hq1 measurable_snd,
      Measure.compProd_map hq1,
      Measure.map_map measurable_snd (measurable_id.prodMap hq1)]
    rfl
  have hcoarse :
      (ρ ⊗ₘ (L.comap q0 hq0)).map Prod.snd =
        ((ρ.map q0) ⊗ₘ L).map Prod.snd := by
    rw [compProd_map_left_eq_map_compProd_comap ρ hq0 L]
    rw [Measure.map_map measurable_snd (hq0.prodMap measurable_id)]
    rfl
  rw [hnatural, ← hcoarse]
  exact Measure.map_mono hcomp measurable_snd

/-- Actual projected common *history measures* stay below the coarse history
law for every horizon, including different initial laws and dependent rows. -/
theorem projected_evolution_le
    (ξ : Measure (H 0)) [IsFiniteMeasure ξ]
    (ν : Measure (G 0)) [IsProbabilityMeasure ν]
    (R : ∀ n, Kernel (H n) (H (n+1)))
    (L : ∀ n, Kernel (G n) (G (n+1)))
    [∀ n, IsFiniteKernel (R n)] [∀ n, IsMarkovKernel (L n)]
    (q : ∀ n, H n → G n) (hq : ∀ n, Measurable (q n))
    (hstart : ξ.map (q 0) ≤ ν)
    (hrows : ∀ n, (R n).map (q (n+1)) ≤ (L n).comap (q n) (hq n))
    (n : ℕ) :
    (evolution ξ R n).map (q n) ≤ evolution ν L n := by
  induction n with
  | zero => exact hstart
  | succ n ih =>
    haveI : IsFiniteMeasure (evolution ξ R n) := evolution_finite ξ R n
    haveI : IsProbabilityMeasure (evolution ν L n) := evolution_probability ν L n
    calc
      (evolution ξ R (n+1)).map (q (n+1)) =
          (((evolution ξ R n) ⊗ₘ R n).map Prod.snd).map (q (n+1)) := rfl
      _ ≤ (((evolution ξ R n).map (q n)) ⊗ₘ L n).map Prod.snd :=
        projected_compProd_step (evolution ξ R n) (R n) (L n)
          (q n) (hq n) (q (n+1)) (hq (n+1)) (hrows n)
      _ ≤ ((evolution ν L n) ⊗ₘ L n).map Prod.snd :=
        Measure.map_mono (compProd_mono ih le_rfl) measurable_snd
      _ = evolution ν L (n+1) := rfl

/-- Actual finite-horizon TV bound from fine/coarse kernels, a common fine
subprobability, and retained row mass. The initial discrepancy ε is charged
at n=0; per-step η may vary and dependent errors need not be independent.

The result does NOT assert the projected process is Markov, does NOT change a
constitutive comparison domain, and does NOT transfer exact all-time GR/PR. -/
theorem projected_evolution_tv_le_product
    (μ ξ : Measure (H 0)) [IsProbabilityMeasure μ]
    (ν : Measure (G 0)) [IsProbabilityMeasure ν]
    (K R : ∀ n, Kernel (H n) (H (n+1)))
    (L : ∀ n, Kernel (G n) (G (n+1)))
    [∀ n, IsMarkovKernel (K n)] [∀ n, IsFiniteKernel (R n)]
    [∀ n, IsMarkovKernel (L n)]
    (q : ∀ n, H n → G n) (hq : ∀ n, Measurable (q n))
    (hξμ : ξ ≤ μ) (hξν : ξ.map (q 0) ≤ ν)
    (hRK : ∀ n, R n ≤ K n)
    (hproj : ∀ n, (R n).map (q (n+1)) ≤ (L n).comap (q n) (hq n))
    (η : ℕ → ℝ) (hη1 : ∀ n, η n ≤ 1)
    (hmass : ∀ n h, ENNReal.ofReal (1-η n) ≤ R n h univ)
    {ε : ℝ} (hε1 : ε ≤ 1)
    (hξmass : ENNReal.ofReal (1-ε) ≤ ξ univ)
    (n : ℕ) :
    eventTotalVariation ((evolution μ K n).map (q n)) (evolution ν L n) ≤
      1-(1-ε)*retained η n := by
  letI : IsFiniteMeasure ξ := isFiniteMeasure_of_le μ hξμ
  haveI : IsFiniteMeasure (evolution ξ R n) := evolution_finite ξ R n
  haveI : IsProbabilityMeasure (evolution μ K n) := evolution_probability μ K n
  haveI : IsProbabilityMeasure (evolution ν L n) := evolution_probability ν L n
  haveI : IsProbabilityMeasure ((evolution μ K n).map (q n)) :=
    (Measure.isProbabilityMeasure_map_iff (hq n).aemeasurable).mpr inferInstance
  have hleft := Measure.map_mono (evolution_mono R K hξμ hRK n) (hq n)
  have hright := projected_evolution_le ξ ν R L q hq hξν hproj n
  have htv := eventTotalVariation_le_one_sub_commonMass hleft hright
  have hbound := common_mass_ge ξ R η hη1 hmass hε1 hξmass n
  have hreal := (ENNReal.ofReal_le_iff_le_toReal
    (measure_ne_top (evolution ξ R n) univ)).mp hbound
  have hmap : ((evolution ξ R n).map (q n)).real univ =
      (evolution ξ R n).real univ := by
    simp [Measure.real, Measure.map_apply (hq n)]
  rw [hmap] at htv
  exact htv.trans (sub_le_sub_left hreal 1)

end PermanssonResearch.Quotient.NonstationaryProjected
