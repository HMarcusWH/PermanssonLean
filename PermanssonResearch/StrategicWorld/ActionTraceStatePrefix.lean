import PermanssonResearch.StrategicWorld.ActionTraceCanonical

/-! Full finite state-prefix erasure of a Markov baseline action trace. -/

namespace PermanssonResearch.ActionTrace

open MeasureTheory ProbabilityTheory
set_option autoImplicit false
universe u
variable {Y A : Type u} [Fintype Y] [Fintype A]

abbrev StatePrefix (Y : Type u) (n : ℕ) := Fin (n+1) → Y

/-- Erase actions only when considering a state marginal, never when defining reward. -/
def states : (n : ℕ) → History Y (A × A) n → StatePrefix Y n
  | 0, h => fun _ => h
  | n+1, h => Fin.snoc (states n h.1) h.2.2

@[simp] theorem states_last (n : ℕ) (h : History Y (A × A) n) :
    states n h (Fin.last n) = last n h := by
  cases n <;> simp [states, last]

/-- An independently generated Markov state-prefix row. -/
noncomputable def markovPrefix (K : Y → Row Y) (μ : Row Y) :
    (n : ℕ) → Row (StatePrefix Y n)
  | 0 => μ.map (fun y _ => y)
  | n+1 => (markovPrefix K μ n).bind (fun h => (K (h (Fin.last n))).map (fun z => Fin.snoc h z))

/-- Exact equality for every finite state-prefix observable. Earlier actions
remain available to the strategy, but are integrated out in this marginal. -/
theorem baseline_state_prefix (G : Game Y A) (π : Y → Row A) (μ : Row Y)
    (n : ℕ) (f : StatePrefix Y n → ℝ) :
    (law G (markovBehavior π) μ n).expect (fun h => f (states n h)) =
      (markovPrefix (stateStep G π) μ n).expect f := by
  induction n with
  | zero => simp [law, states, markovPrefix]
  | succ n ih =>
      rw [law_step_expect]
      have hi := ih (fun h => (stateStep G π (h (Fin.last n))).expect
        (fun z => f (Fin.snoc h z)))
      simp only [states_last, stateStep, Row.expect_bind] at hi
      simpa only [markovBehavior, states, last, markovPrefix,
        stateStep, Row.expect_bind, Row.expect_map] using hi

section Canonical

variable [MeasurableSpace Y] [MeasurableSpace A]
  [DiscreteMeasurableSpace Y] [DiscreteMeasurableSpace A]

/-- Prefixing a fixed past creates no probability on a different past. -/
theorem next_prefix_support (G : Game Y A) (σ : BehavioralPolicy Y A)
    (n : ℕ) (h : History Y (A × A) n) :
    (next G σ n h).measure {z | z.1 ≠ h} = 0 := by
  classical
  have hh : (next G σ n h).expect
      (({z : History Y (A × A) (n+1) | z.1 ≠ h} : Set _).indicator (fun _ => (1 : ℝ))) = 0 := by
    simp [next, Set.indicator]
  rw [Row.expect_eq_integral] at hh
  change (∫ z, ({z : History Y (A × A) (n+1) | z.1 ≠ h} : Set _).indicator
    (1 : History Y (A × A) (n+1) → ℝ) z ∂(next G σ n h).measure) = 0 at hh
  rw [integral_indicator_one (MeasurableSet.of_discrete)] at hh
  exact ((ENNReal.toReal_eq_zero_iff _).mp hh).resolve_right (measure_ne_top _ _)

/-- Adjacent canonical coordinates are consistent alternating histories almost
surely. The redundant Ionescu coordinates therefore encode one action trace. -/
theorem canonical_coherent (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y) (n : ℕ) :
    ∀ᵐ w ∂canonicalLaw G σ μ, (w (n+1)).1 = w n := by
  classical
  let E : Set (((j : Finset.Iic n) → History Y (A × A) j) × History Y (A × A) (n+1)) :=
    {z | z.2.1 ≠ z.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩}
  have hE : MeasurableSet E := by
    exact (measurableSet_eq_fun (by fun_prop) (by fun_prop)).compl
  have hz : ((canonicalLaw G σ μ).map (Preorder.frestrictLe n) ⊗ₘ
      canonicalHistoryKernel G σ n) E = 0 := by
    rw [Measure.compProd_apply hE]
    have hinner (h : (j : Finset.Iic n) → History Y (A × A) j) :
        canonicalHistoryKernel G σ n h {z | (h,z) ∈ E} = 0 := by
      exact next_prefix_support G σ n (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
    change (∫⁻ h, canonicalHistoryKernel G σ n h {z | (h,z) ∈ E}
      ∂(canonicalLaw G σ μ).map (Preorder.frestrictLe n)) = 0
    calc
      _ = ∫⁻ _h, (0 : ENNReal) ∂(canonicalLaw G σ μ).map (Preorder.frestrictLe n) :=
        lintegral_congr (fun h => hinner h)
      _ = 0 := lintegral_zero
  rw [canonical_step_pair, Measure.map_apply (by fun_prop) hE] at hz
  exact hz

def statePath (w : (n : ℕ) → History Y (A × A) n) : ℕ → Y := fun n => last n (w n)

theorem canonical_state_prefix (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y)
    (n : ℕ) :
    ∀ᵐ w ∂canonicalLaw G σ μ,
      (fun j : Fin (n+1) => statePath w j) = states n (w n) := by
  induction n with
  | zero =>
      apply ae_of_all
      intro w
      funext j
      have hj : j = 0 := Fin.eq_zero j
      subst j
      rfl
  | succ n ih =>
      filter_upwards [ih, canonical_coherent G σ μ n] with w hw hc
      funext j
      refine Fin.lastCases ?_ (fun k => ?_) j
      · simp [statePath, states, last]
      · simp only [states, Fin.snoc_castSucc, hc]
        exact congrFun hw k

/-- Exact canonical finite state-prefix expectations of a Markov baseline. -/
theorem canonical_baseline_state_prefix (G : Game Y A) (π : Y → Row A) (μ : Row Y)
    (n : ℕ) (f : StatePrefix Y n → ℝ) :
    (∫ w, f (fun j => statePath w j) ∂canonicalLaw G (markovBehavior π) μ) =
      (markovPrefix (stateStep G π) μ n).expect f := by
  calc
    _ = ∫ w, f (states n (w n)) ∂canonicalLaw G (markovBehavior π) μ := by
      apply integral_congr_ae
      filter_upwards [canonical_state_prefix G (markovBehavior π) μ n] with w hw
      rw [hw]
    _ = _ := (canonical_expect G (markovBehavior π) μ n _).trans
      (baseline_state_prefix G π μ n f)

end Canonical

end PermanssonResearch.ActionTrace
