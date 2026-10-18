import PermanssonResearch.StrategicWorld.ActionTraceStatePrefix
import PermanssonLean.StrategicWorld.WellPosedness

/-! Literal canonical state-law transport from action traces to original models. -/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch.ActionTrace
set_option autoImplicit false

variable {S X Action Move : Type} [Fintype S] [Fintype X] [Fintype Move]
  [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace Action] [MeasurableSpace Move]
  [DiscreteMeasurableSpace S] [DiscreteMeasurableSpace X] [DiscreteMeasurableSpace Move]

abbrev TypedState := PermanssonLean.JointState S X

def finiteStatePrefix {Y : Type} (n : ℕ) (w : ℕ → Y) : StatePrefix Y n := fun j => w j

def prefixFromIic {Y : Type} (n : ℕ) (h : (j : Finset.Iic n) → Y) : StatePrefix Y n :=
  fun j => h ⟨j, Finset.mem_Iic.mpr (Nat.le_of_lt_succ j.isLt)⟩

def prefixToIic {Y : Type} (n : ℕ) (h : StatePrefix Y n) : (j : Finset.Iic n) → Y :=
  fun j => h ⟨j, Nat.lt_succ_of_le (Finset.mem_Iic.mp j.2)⟩

theorem snoc_finiteStatePrefix {Y : Type} (n : ℕ) (w : ℕ → Y) :
    Fin.snoc (finiteStatePrefix n w) (w (n+1)) = finiteStatePrefix (n+1) w := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [finiteStatePrefix]
  · simp [finiteStatePrefix]

/-- Finite probability measures are determined by all real expectations. -/
theorem measure_eq_of_finite_integrals {Y : Type} [Fintype Y] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ f : Y → ℝ, (∫ y, f y ∂μ) = ∫ y, f y ∂ν) : μ = ν := by
  apply Measure.ext_of_measureReal_singleton
  intro y
  simpa only [integral_indicator_one (measurableSet_singleton y)]
    using h (({y} : Set Y).indicator (1 : Y → ℝ))

/-- A row-by-row equality to the actual induced kernel transports the
independently computed complete Markov state-prefix expectations. -/
theorem original_prefix_expect (M : PermanssonLean.StrategicWorldModel S X Action)
    (K : TypedState → Row TypedState) (μ : Row TypedState)
    (hK : ∀ y, (K y).measure = M.inducedKernel y)
    (n : ℕ) (f : StatePrefix TypedState n → ℝ) :
    (∫ w, f (finiteStatePrefix n w) ∂M.pathLaw μ.measure) = (markovPrefix K μ n).expect f := by
  letI := PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov M
  induction n with
  | zero =>
      have hh := congrArg (fun ν => ∫ h, f (prefixFromIic 0 h) ∂ν)
        (PermanssonLean.StrategicWorldModel.pathLaw_prefix_zero M μ.measure)
      rw [integral_map_of_stronglyMeasurable (by fun_prop) (.of_discrete),
        integral_map_of_stronglyMeasurable (by fun_prop) (.of_discrete)] at hh
      change (∫ w, f (finiteStatePrefix 0 w) ∂M.pathLaw μ.measure) =
        ∫ y, f (fun _ => y) ∂μ.measure at hh
      simpa only [markovPrefix, Row.expect_map] using hh.trans
        (Row.expect_eq_integral μ (fun y => f (fun _ => y))).symm
  | succ n ih =>
      have hh := congrArg (fun ν => ∫ z, f (Fin.snoc (prefixFromIic n z.1) z.2) ∂ν)
        (PermanssonLean.StrategicWorldModel.pathLaw_has_transition_pair M μ.measure n)
      rw [Measure.integral_compProd (Integrable.of_finite),
        integral_map_of_stronglyMeasurable (by fun_prop) (.of_discrete),
        integral_map_of_stronglyMeasurable (by fun_prop) (.of_discrete)] at hh
      change (∫ w, ∫ z, f (Fin.snoc (finiteStatePrefix n w) z) ∂M.inducedKernel (w n)
        ∂M.pathLaw μ.measure) =
          ∫ w, f (Fin.snoc (finiteStatePrefix n w) (w (n+1))) ∂M.pathLaw μ.measure at hh
      simp_rw [← hK, ← Row.expect_eq_integral, snoc_finiteStatePrefix] at hh
      have hi := ih (fun h => (K (h (Fin.last n))).expect (fun z => f (Fin.snoc h z)))
      change (∫ w, (K (w n)).expect (fun z => f (Fin.snoc (finiteStatePrefix n w) z))
        ∂M.pathLaw μ.measure) = _ at hi
      rw [hi] at hh
      simpa only [markovPrefix, Row.expect_bind, Row.expect_map] using hh.symm

/-- Full literal state-erasure equality with the existing original canonical
path law. The actual-kernel identification premise is explicit and must be
proved by every model adapter, rather than inferred from a filename. -/
theorem canonical_state_erasure_eq_original
    (M : PermanssonLean.StrategicWorldModel S X Action)
    (G : Game TypedState Move) (π : TypedState → Row Move) (μ : Row TypedState)
    (hK : ∀ y, (stateStep G π y).measure = M.inducedKernel y) :
    (canonicalLaw G (markovBehavior π) μ).map statePath = M.pathLaw μ.measure := by
  have hm : Measurable (statePath (Y := PermanssonLean.JointState S X) (A := Move)) := by
    refine Measurable.of_eval (fun n => ?_)
    have hlast : Measurable (fun h : History (PermanssonLean.JointState S X) (Move × Move) n =>
      last n h) := Measurable.of_discrete
    exact hlast.comp (measurable_pi_apply n)
  apply PermanssonLean.StrategicWorldModel.measure_eq_of_prefix_maps_eq
  intro n
  apply measure_eq_of_finite_integrals
  intro f
  have hf : StronglyMeasurable f := .of_discrete
  have hp : StronglyMeasurable (fun w : ℕ → PermanssonLean.JointState S X =>
      f (Preorder.frestrictLe n w)) := hf.comp_measurable (by fun_prop)
  rw [integral_map_of_stronglyMeasurable (by fun_prop) hf,
    integral_map_of_stronglyMeasurable hm hp,
    integral_map_of_stronglyMeasurable (by fun_prop) hf]
  have hl := canonical_baseline_state_prefix G π μ n (fun h => f (prefixToIic n h))
  have hr := original_prefix_expect M (stateStep G π) μ hK n (fun h => f (prefixToIic n h))
  exact hl.trans hr.symm

end PermanssonResearch.ActionTrace
