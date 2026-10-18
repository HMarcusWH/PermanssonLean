import PermanssonResearch.Probability.CouplingDualBound
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Tactic

/-! A countable gluing of actual adjacent couplings. Conditional kernels are
constructed by standard-Borel disintegration and the path measure by the
Ionescu--Tulcea theorem; all adjacent pair laws are then proved exactly. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace PermanssonResearch.Probability.GluedCouplingSequence
set_option autoImplicit false

theorem map_compProd_comap {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (θ : Measure A) [IsFiniteMeasure θ]
    (K : Kernel B C) [IsMarkovKernel K] (f : A → B) (hf : Measurable f) :
    (θ ⊗ₘ K.comap f hf).map (Prod.map f id) = (θ.map f) ⊗ₘ K := by
  ext s hs
  rw [Measure.map_apply (hf.prodMap measurable_id) hs,
    Measure.compProd_apply ((hf.prodMap measurable_id) hs),Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  rfl

variable {Y : Type*} [PseudoMetricSpace Y] [MeasurableSpace Y]
variable [StandardBorelSpace Y] [Nonempty Y]
variable (μ : ℕ → Measure Y) [∀ n, IsProbabilityMeasure (μ n)]
variable (γ : (n : ℕ) → IntegrableCoupling (μ n) (μ (n+1)))

noncomputable def chainKernel (n : ℕ) : Kernel Y Y := (γ n).law.condKernel

instance chainKernel_markov (n : ℕ) : IsMarkovKernel (chainKernel μ γ n) := by
  unfold chainKernel
  infer_instance

def lastCoordinate (n : ℕ) (h : Finset.Iic n → Y) : Y :=
  h ⟨n,Finset.mem_Iic.mpr le_rfl⟩

theorem lastCoordinate_measurable (n : ℕ) : Measurable (lastCoordinate (Y := Y) n) :=
  measurable_pi_apply _

noncomputable def prefixKernel (n : ℕ) : Kernel (Finset.Iic n → Y) Y :=
  (chainKernel μ γ n).comap (lastCoordinate n) (lastCoordinate_measurable n)

instance prefixKernel_markov (n : ℕ) : IsMarkovKernel (prefixKernel μ γ n) := by
  unfold prefixKernel
  infer_instance

noncomputable def law : Measure (ℕ → Y) := Kernel.trajMeasure (μ 0) (prefixKernel μ γ)

instance law_probability : IsProbabilityMeasure (law μ γ) := by
  unfold law
  infer_instance

theorem prefix_zero : (law μ γ).map (Preorder.frestrictLe 0) =
    (μ 0).map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Y)).symm := by
  unfold law Kernel.trajMeasure
  rw [Measure.map_comp _ _ (by fun_prop),Kernel.traj_map_frestrictLe]
  simp

theorem marginal_zero : (law μ γ).map (fun w => w 0) = μ 0 := by
  have h := congrArg (fun θ : Measure (Finset.Iic 0 → Y) =>
    θ.map (fun x => x ⟨0,by simp⟩)) (prefix_zero μ γ)
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  change (law μ γ).map (fun w => w 0) = (μ 0).map id at h
  simpa using h

theorem pair_of_marginal (n : ℕ) (hn : (law μ γ).map (fun w => w n) = μ n) :
    (law μ γ).map (fun w => (w n,w (n+1))) = (γ n).law := by
  have h := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => Y) (μ₀ := μ 0) (κ := prefixKernel μ γ) (a := n)
  have hp := congrArg (fun θ : Measure ((Finset.Iic n → Y) × Y) =>
    θ.map (Prod.map (lastCoordinate n) id)) h
  simp only [prefixKernel] at hp
  rw [map_compProd_comap,
    Measure.map_map (lastCoordinate_measurable n) (by fun_prop),
    Measure.map_map ((lastCoordinate_measurable n).prodMap measurable_id) (by fun_prop)] at hp
  change ((law μ γ).map (fun w => w n)) ⊗ₘ chainKernel μ γ n =
    (law μ γ).map (fun w => (w n,w (n+1))) at hp
  rw [hn] at hp
  have hd : (μ n) ⊗ₘ chainKernel μ γ n = (γ n).law := by
    have hf : (γ n).law.fst = μ n := (γ n).first
    have hh := congrArg (fun θ : Measure Y => θ ⊗ₘ (γ n).law.condKernel) hf.symm
    exact hh.trans ((γ n).law.disintegrate (γ n).law.condKernel)
  exact hp.symm.trans hd

theorem marginal (n : ℕ) : (law μ γ).map (fun w => w n) = μ n := by
  induction n with
  | zero => exact marginal_zero μ γ
  | succ n ih =>
    have hp := pair_of_marginal μ γ n ih
    have h := congrArg (fun θ : Measure (Y × Y) => θ.map Prod.snd) hp
    rw [Measure.map_map measurable_snd (by fun_prop)] at h
    exact h.trans (γ n).second

theorem pair (n : ℕ) : (law μ γ).map (fun w => (w n,w (n+1))) = (γ n).law :=
  pair_of_marginal μ γ n (marginal μ γ n)

variable [BorelSpace Y] [SecondCountableTopology Y]

theorem step_integrable (n : ℕ) :
    Integrable (fun w => dist (w n) (w (n+1))) (law μ γ) := by
  have h : Integrable (fun z : Y × Y => dist z.1 z.2)
      ((law μ γ).map (fun w => (w n,w (n+1)))) := by
    rw [pair μ γ n]
    exact (γ n).cost_integrable
  exact h.comp_measurable (by fun_prop)

theorem integral_step (n : ℕ) :
    (∫ w, dist (w n) (w (n+1)) ∂law μ γ) = (γ n).cost := by
  unfold IntegrableCoupling.cost
  rw [← pair μ γ n,
    integral_map (by fun_prop) (measurable_fst.dist measurable_snd).aestronglyMeasurable]

end PermanssonResearch.Probability.GluedCouplingSequence
