import PermanssonResearch.MultiAgent.ProductGame

/-! F-LUMP: the all-state, all-admissible-control criterion is equivalent to
the actual next-key conditional row at every full finite history. A policy is
nonanticipating because its domain contains only the history through that time.
This concerns the declared controlled kernel, not causal identifiability. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultiAgent.BehavioralAutonomy

set_option autoImplicit false

variable {Y Q C : Type*} [MeasurableSpace Y] [MeasurableSpace Q] [MeasurableSpace C]
variable [Fintype C] [MeasurableSingletonClass C]

abbrev History (Y : Type*) (n : ℕ) := Fin (n+1) → Y

def last (n : ℕ) (h : History Y n) : Y := h (Fin.last n)

theorem measurable_last (n : ℕ) : Measurable (last (Y := Y) n) := measurable_pi_apply _

/-- Sample the declared control from the full past, then sample the actual
controlled row and retain both draws. -/
noncomputable def controlledMarked (K : Kernel (Y × C) Y) (n : ℕ)
    (π : Kernel (History Y n) C) : Kernel (History Y n) (C × Y) :=
  π ⊗ₖ K.comap (fun hc : History Y n × C => (last n hc.1,hc.2))
    (((measurable_last n).comp measurable_fst).prodMk measurable_snd)

noncomputable def controlledKey (K : Kernel (Y × C) Y) (q : Y → Q)
    (n : ℕ) (π : Kernel (History Y n) C) : Kernel (History Y n) Q :=
  (controlledMarked K n π).map (q ∘ Prod.snd)

def RowAutonomous (K : Kernel (Y × C) Y) (q : Y → Q)
    (legal : Y → Set C) (L : Kernel Q Q) : Prop :=
  ∀ y c, c ∈ legal y → (K (y,c)).map q = L (q y)

def HistoryAutonomous (K : Kernel (Y × C) Y) (q : Y → Q)
    (legal : Y → Set C) (L : Kernel Q Q) : Prop :=
  ∀ (n : ℕ) (π : Kernel (History Y n) C) (_ : IsMarkovKernel π)
    (h : History Y n), π h (legal (last n h)) = 1 →
      controlledKey K q n π h = L (q (last n h))

theorem row_iff_all_histories (K : Kernel (Y × C) Y) [IsMarkovKernel K]
    (q : Y → Q) (hq : Measurable q) (legal : Y → Set C) (L : Kernel Q Q) :
    RowAutonomous K q legal L ↔ HistoryAutonomous K q legal L := by
  classical
  constructor
  · intro hrow n π hπ h hlegal
    letI := hπ
    have hlegalmeas : MeasurableSet (legal (last n h)) :=
      (Set.toFinite _).measurableSet
    have hae : ∀ᵐ c ∂π h, c ∈ legal (last n h) :=
      (mem_ae_iff_prob_eq_one hlegalmeas).mpr hlegal
    ext E hE
    rw [controlledKey, Kernel.map_apply' _ (hq.comp measurable_snd) _ hE,
      controlledMarked, Kernel.compProd_apply (hE.preimage (hq.comp measurable_snd))]
    change (∫⁻ c, K (last n h,c) (q ⁻¹' E) ∂π h) = _
    calc
      _ = ∫⁻ _c, L (q (last n h)) E ∂π h := by
        apply lintegral_congr_ae
        filter_upwards [hae] with c hc
        have heq := congrArg (fun μ : Measure Q => μ E) (hrow (last n h) c hc)
        simpa [Measure.map_apply hq hE] using heq
      _ = L (q (last n h)) E := by simp
  · intro hh y c hc
    let π : Kernel (History Y 0) C := Kernel.const _ (Measure.dirac c)
    let h : History Y 0 := fun _ => y
    have hlegal : π h (legal (last 0 h)) = 1 := by
      simp [π,last,h,Measure.dirac_apply, (Set.toFinite (legal y)).measurableSet,hc]
    have heq := hh 0 π inferInstance h hlegal
    ext E hE
    have hmeas : Measurable (q ∘ Prod.snd : C × Y → Q) := hq.comp measurable_snd
    have heval := congrArg (fun μ : Measure Q => μ E) heq
    rw [controlledKey, Kernel.map_apply' _ hmeas _ hE,controlledMarked,
      Kernel.compProd_apply (hE.preimage hmeas)] at heval
    change (∫⁻ d, K (y,d) (q ⁻¹' E) ∂Measure.dirac c) = L (q y) E at heval
    rw [lintegral_dirac] at heval
    simpa [Measure.map_apply hq hE] using heval

/-- The existence formulation uses a single common row kernel at every state
and every time; observing one initial distribution cannot establish it. -/
theorem exists_row_iff_all_histories (K : Kernel (Y × C) Y) [IsMarkovKernel K]
    (q : Y → Q) (hq : Measurable q) (legal : Y → Set C) :
    (∃ L : Kernel Q Q, RowAutonomous K q legal L) ↔
      ∃ L : Kernel Q Q, HistoryAutonomous K q legal L :=
  exists_congr (fun L => row_iff_all_histories K q hq legal L)

end PermanssonResearch.MultiAgent.BehavioralAutonomy
