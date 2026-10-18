import PermanssonResearch.Probability.FullPathProductTV
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-! Literal dependent-history prefix identifications and boundary checks
for the whole-path product estimate. Initial mismatch is retained even
with identical transition kernels. A unit defect is allowed, while a
fixed positive recurring defect is outside the summable class. -/

open MeasureTheory ProbabilityTheory Filter Finset Set
open scoped Topology ENNReal ProbabilityTheory
namespace PermanssonResearch.Probability.FullPathProductRegression
open PermanssonLean.ProbabilitySupport DependentHistory FullPathProduct
set_option autoImplicit false

abbrev H (n : ℕ) := History (fun _ => Bool) n
def point (b : Bool) (n : ℕ) : H n := fun _ => b

noncomputable def keep (n : ℕ) : Kernel (H n) (H (n+1)) :=
  Kernel.deterministic (fun h => fun _ => h ⟨0,mem_Iic.mpr (Nat.zero_le _)⟩)
    (Measurable.of_eval fun _ => measurable_pi_apply _)

instance keep_markov (n : ℕ) : IsMarkovKernel (keep n) := by unfold keep; infer_instance

noncomputable def initial (b : Bool) : Measure (H 0) := Measure.dirac (point b 0)
noncomputable def pointLaw (b : Bool) : Measure (ℕ → Bool) := Measure.dirac (fun _ => b)

instance initial_probability (b : Bool) : IsProbabilityMeasure (initial b) := by
  unfold initial; infer_instance
instance pointLaw_probability (b : Bool) : IsProbabilityMeasure (pointLaw b) := by
  unfold pointLaw; infer_instance

theorem evolution_point (b : Bool) (n : ℕ) :
    evolution (initial b) keep n = Measure.dirac (point b n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [evolution,ih,keep,Measure.compProd_deterministic,
      Measure.map_dirac' (by fun_prop),Measure.map_dirac' measurable_snd]
    rfl

theorem actual_prefix (b : Bool) (n : ℕ) :
    (pointLaw b).map (Finset.Iic n).restrict = evolution (initial b) keep n := by
  rw [evolution_point]
  exact Measure.map_dirac' (by fun_prop) _

theorem zero_defect_budget (ε : ℝ) :
    1-(1-ε)*(∏' _n : ℕ, (1-(0 : ℝ))) = ε := by rw [zero_defect_product]; ring

theorem identical_actual_laws_bound_zero :
    eventTotalVariation (pointLaw false) (pointLaw false) ≤ 0 := by
  have h := path_tv_le_product (pointLaw false) (pointLaw false)
    (initial false) (initial false) (initial false) keep keep keep
    (actual_prefix false) (actual_prefix false) le_rfl le_rfl
    (fun _ => le_rfl) (fun _ => le_rfl)
    (fun _ => (0 : ℝ)) (fun _ => by norm_num) (fun _ => by norm_num)
    summable_zero (fun _ _ => by simp)
    (ε := 0) (by norm_num) (by norm_num) (by simp [initial])
  simpa using h

theorem actual_initial_mismatch_bound_one :
    eventTotalVariation (pointLaw false) (pointLaw true) ≤ 1 := by
  have h := path_tv_le_product (pointLaw false) (pointLaw true)
    (initial false) (initial true) 0 keep keep keep
    (actual_prefix false) (actual_prefix true) (by exact bot_le) (by exact bot_le)
    (fun _ => le_rfl) (fun _ => le_rfl)
    (fun _ => (0 : ℝ)) (fun _ => by norm_num) (fun _ => by norm_num)
    summable_zero (fun _ _ => by simp)
    (ε := 1) (by norm_num) (by norm_num) (by simp)
  simpa using h

theorem actual_initial_mismatch_exact_one :
    eventTotalVariation (pointLaw false) (pointLaw true) = 1 := by
  apply le_antisymm actual_initial_mismatch_bound_one
  have hE : MeasurableSet {w : ℕ → Bool | w 0 = false} :=
    (measurableSet_singleton false).preimage (measurable_pi_apply 0)
  have h := abs_measureReal_sub_le_eventTotalVariation
    (pointLaw false) (pointLaw true) hE
  simpa [Measure.real,pointLaw,Measure.dirac_apply' _ hE] using h

def singleLeak (n : ℕ) : ℝ := if n=0 then 1 else 0

theorem singleLeak_summable : Summable singleLeak := (hasSum_ite_eq 0 (1 : ℝ)).summable

theorem unit_defect_boundary_budget :
    1-(1-(1/4 : ℝ))*(∏' n, (1-singleLeak n)) = 1 := by
  rw [unit_defect_product singleLeak (n := 0) (by simp [singleLeak])]
  ring

theorem positive_recurring_defect_not_summable {η : ℝ} (hη : 0 < η) :
    ¬ Summable (fun _n : ℕ => η) := by
  intro hs
  have hz : η=0 := tendsto_nhds_unique tendsto_const_nhds hs.tendsto_atTop_zero
  linarith

theorem recurring_leak_only_trivial_limit :
    Tendsto (fun n => 1-(1-(1/4 : ℝ))*retained (fun _ => (1/100 : ℝ)) n)
      atTop (𝓝 1) := recurring_leak_budget_tendsto_one (by norm_num) (by norm_num)

end PermanssonResearch.Probability.FullPathProductRegression
