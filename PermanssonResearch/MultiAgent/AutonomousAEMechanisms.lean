import PermanssonResearch.MultiAgent.AutonomousAETransport

/-! M-AE: baseline primitive agreement at every actual time implies equality of
the entire original treated trajectory laws in the autonomous subclass. -/

namespace PermanssonResearch.MultiAgent.Autonomous

open MeasureTheory ProbabilityTheory Set PermanssonLean
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {S0 S1 S2 X A1 A2 : Type*}
variable [MeasurableSpace S0] [MeasurableSpace S1] [MeasurableSpace S2]
variable [MeasurableSpace X] [MeasurableSpace A1] [MeasurableSpace A2]

attribute [local instance] StrategicWorldModel.inducedKernel_isMarkov

def baselineStateLaw (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (μ : Measure (State S0 S1 S2 X)) (t : ℕ) : Measure (State S0 S1 S2 X) :=
  stateLaw (G.toModel P).inducedKernel μ t

def baselineKeyLaw (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (μ : Measure (State S0 S1 S2 X)) (t : ℕ) : Measure (S0 × S2) :=
  (baselineStateLaw G P μ t).map anchorKey

/-- The hypotheses concern the baseline's actual primitive laws. Updates are
compared under its actual joint old-state/action/next-world law at every time. -/
structure BaselineAEAgreement (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (a b : PlayerTwoMechanism S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (μ : Measure (State S0 S1 S2 X)) : Prop where
  action_a : ∀ t, G.player2.action =ᵐ[baselineStateLaw G P μ t] a.action
  action_b : ∀ t, G.player2.action =ᵐ[baselineStateLaw G P μ t] b.action
  update_a : ∀ t, ∀ᵐ z ∂(baselineStateLaw G P μ t ⊗ₘ (G.toModel P).actionWorldKernel),
    G.player2.update ((z.1,z.2.1),z.2.2) = a.update ((z.1,z.2.1),z.2.2)
  update_b : ∀ t, ∀ᵐ z ∂(baselineStateLaw G P μ t ⊗ₘ (G.toModel P).actionWorldKernel),
    G.player2.update ((z.1,z.2.1),z.2.2) = b.update ((z.1,z.2.1),z.2.2)

variable {G : TwoPlayerGenerator S0 S1 S2 X A1 A2}
variable {a b : PlayerTwoMechanism S0 S1 S2 X A1 A2}

theorem baselineStateLaw_actual (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X)
    [IsMarkovKernel P] (μ : Measure (State S0 S1 S2 X)) [IsProbabilityMeasure μ] (t : ℕ) :
    baselineStateLaw G P μ t =
      ((G.toModel P).pathLaw μ).map (fun w : ℕ → State S0 S1 S2 X => w t) :=
  stateLaw_eq_actual_marginal _ μ t

theorem baseline_key_recursions (da : Profile G a) (db : Profile G b)
    [IsMarkovKernel da.common] [IsMarkovKernel da.action] [IsMarkovKernel da.update]
    [IsMarkovKernel db.common] [IsMarkovKernel db.action] [IsMarkovKernel db.update]
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (μ : Measure (State S0 S1 S2 X)) [IsProbabilityMeasure μ]
    (h : BaselineAEAgreement G a b P μ) (t : ℕ) :
    baselineKeyLaw G P μ (t+1) = da.keyKernel ∘ₘ baselineKeyLaw G P μ t ∧
      baselineKeyLaw G P μ (t+1) = db.keyKernel ∘ₘ baselineKeyLaw G P μ t := by
  constructor
  · calc
      baselineKeyLaw G P μ (t+1) = stateLaw da.keyKernel (μ.map anchorKey) (t+1) :=
        da.baseline_key_marginal P μ h.action_a h.update_a (t+1)
      _ = da.keyKernel ∘ₘ stateLaw da.keyKernel (μ.map anchorKey) t := rfl
      _ = da.keyKernel ∘ₘ baselineKeyLaw G P μ t :=
        congrArg (fun ν => da.keyKernel ∘ₘ ν)
          (da.baseline_key_marginal P μ h.action_a h.update_a t).symm
  · calc
      baselineKeyLaw G P μ (t+1) = stateLaw db.keyKernel (μ.map anchorKey) (t+1) :=
        db.baseline_key_marginal P μ h.action_b h.update_b (t+1)
      _ = db.keyKernel ∘ₘ stateLaw db.keyKernel (μ.map anchorKey) t := rfl
      _ = db.keyKernel ∘ₘ baselineKeyLaw G P μ t :=
        congrArg (fun ν => db.keyKernel ∘ₘ ν)
          (db.baseline_key_marginal P μ h.action_b h.update_b t).symm

theorem treated_key_marginals (da : Profile G a) (db : Profile G b)
    [IsMarkovKernel da.common] [IsMarkovKernel da.action] [IsMarkovKernel da.update]
    [IsMarkovKernel db.common] [IsMarkovKernel db.action] [IsMarkovKernel db.update]
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (μ : Measure (State S0 S1 S2 X)) [IsProbabilityMeasure μ]
    (h : BaselineAEAgreement G a b P μ)
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2) (t : ℕ) :
    (stateLaw ((G.openLoop r a).toModel P).inducedKernel μ t).map anchorKey =
        baselineKeyLaw G P μ t ∧
      (stateLaw ((G.openLoop r b).toModel P).inducedKernel μ t).map anchorKey =
        baselineKeyLaw G P μ t := by
  exact ⟨(da.actual_key_marginal r P μ t).trans
      (da.baseline_key_marginal P μ h.action_a h.update_a t).symm,
    (db.actual_key_marginal r P μ t).trans
      (db.baseline_key_marginal P μ h.action_b h.update_b t).symm⟩

theorem treated_rows_ae [StandardBorelSpace A2] [StandardBorelSpace S2]
    (da : Profile G a) (db : Profile G b)
    [IsMarkovKernel da.common] [IsMarkovKernel da.action] [IsMarkovKernel da.update]
    [IsMarkovKernel db.common] [IsMarkovKernel db.action] [IsMarkovKernel db.update]
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (μ : Measure (State S0 S1 S2 X)) [IsProbabilityMeasure μ]
    (h : BaselineAEAgreement G a b P μ)
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2) (t : ℕ) :
    ((G.openLoop r a).toModel P).inducedKernel =ᵐ[
      stateLaw ((G.openLoop r a).toModel P).inducedKernel μ t]
      ((G.openLoop r b).toModel P).inducedKernel := by
  haveI : IsProbabilityMeasure (baselineStateLaw G P μ t) := stateLaw_isProbability _ μ t
  have hfactor := primitive_factor_agreement da db P (baselineStateLaw G P μ t)
    (h.action_a t) (h.action_b t) (h.update_a t) (h.update_b t)
  have hprimitive := actual_primitive_agreement_of_key_agreement da db r P
    (stateLaw ((G.openLoop r a).toModel P).inducedKernel μ t)
    (baselineKeyLaw G P μ t) (treated_key_marginals da db P μ h r t).1
    hfactor.1 hfactor.2
  exact actual_rows_ae_of_primitive_agreement G r a b P _ hprimitive.1 hprimitive.2

/-- Full original infinite-law equality for every stationary treated player-one
mechanism. No full-row or path-law equality is assumed in this theorem. -/
theorem ae_anchors_pathLaw_eq
    [StandardBorelSpace S0] [StandardBorelSpace S1] [StandardBorelSpace S2]
    [StandardBorelSpace X] [StandardBorelSpace A2]
    (da : Profile G a) (db : Profile G b)
    [IsMarkovKernel da.common] [IsMarkovKernel da.action] [IsMarkovKernel da.update]
    [IsMarkovKernel db.common] [IsMarkovKernel db.action] [IsMarkovKernel db.update]
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (μ : Measure (State S0 S1 S2 X)) [IsProbabilityMeasure μ]
    (h : BaselineAEAgreement G a b P μ)
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2) :
    ((G.openLoop r a).toModel P).pathLaw μ = ((G.openLoop r b).toModel P).pathLaw μ := by
  apply pathLaw_eq_of_rows_ae
  exact treated_rows_ae da db P μ h r

theorem ae_anchors_path_property_eq
    [StandardBorelSpace S0] [StandardBorelSpace S1] [StandardBorelSpace S2]
    [StandardBorelSpace X] [StandardBorelSpace A2]
    (da : Profile G a) (db : Profile G b)
    [IsMarkovKernel da.common] [IsMarkovKernel da.action] [IsMarkovKernel da.update]
    [IsMarkovKernel db.common] [IsMarkovKernel db.action] [IsMarkovKernel db.update]
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (μ : Measure (State S0 S1 S2 X)) [IsProbabilityMeasure μ]
    (h : BaselineAEAgreement G a b P μ)
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2)
    {Z : Type*} (ψ : Measure (ℕ → State S0 S1 S2 X) → Z) :
    ψ (((G.openLoop r a).toModel P).pathLaw μ) =
      ψ (((G.openLoop r b).toModel P).pathLaw μ) :=
  congrArg ψ (ae_anchors_pathLaw_eq da db P μ h r)

end
end PermanssonResearch.MultiAgent.Autonomous
