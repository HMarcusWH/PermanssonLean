import PermanssonResearch.ReverseSolver.InfiniteSafetyPathSemantics
import PermanssonResearch.ReverseSolver.GreatestControlledInvariant

/-! Infinite controlled safety, with actual path probabilities. The same
deterministic stationary selector attains the optimum for every initial state;
the upper bound quantifies over all real, full-history behavioral controllers. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch.ReverseSolver.InfiniteSafety
open ControlledKernel FiniteMonitor

noncomputable section
variable {C : Type*} [DecidableEq C] [Fintype C] {n : ℕ}

def safetyProbability (sys : FiniteControlSystem C n) (σ : BehavioralPolicy sys)
    (G : Finset (Fin n)) (y : Fin n) : ℝ :=
  (pathLaw sys σ y (safeForever G)).toReal

/-- Upper bound on the actual infinite event, for every real behavioral law. -/
theorem infiniteSafety_mass_upper (sys : FiniteControlSystem C n)
    (σ : BehavioralPolicy sys) (G : Finset (Fin n)) (y : Fin n) :
    pathLaw sys σ y (safeForever G)≤ENNReal.ofReal (limitValue sys G y) := by
  rw [limitValue,ENNReal.ofReal_iInf]
  apply le_iInf
  intro N
  calc
    pathLaw sys σ y (safeForever G)≤pathLaw sys σ y (safeThrough G N) :=
      measure_mono (fun w hw t _ => hw t)
    _ = ENNReal.ofReal (survival sys σ G N (initialHistory y)) :=
      pathLaw_safeThrough sys σ G y N
    _ ≤ ENNReal.ofReal (horizonValue sys G N y) :=
      ENNReal.ofReal_le_ofReal (survival_le_horizonValue sys σ G N (initialHistory y))

/-- A stationary selector of the limiting equation attains that limit on
the actual infinite physical safety event. -/
theorem infiniteSafety_stationary_mass (sys : FiniteControlSystem C n)
    (G : Finset (Fin n)) (y : Fin n) :
    pathLaw sys (stationaryBehavioral sys (stationaryPolicy sys G)) y (safeForever G)=
      ENNReal.ofReal (limitValue sys G y) := by
  apply le_antisymm
  · exact infiniteSafety_mass_upper sys _ G y
  · rw [pathLaw_safeForever_eq_iInf]
    apply le_iInf
    intro N
    rw [pathLaw_safeThrough]
    exact ENNReal.ofReal_le_ofReal (limitValue_le_stationary_survival_initial sys G N y)

theorem infiniteSafety_upper (sys : FiniteControlSystem C n) (σ : BehavioralPolicy sys)
    (G : Finset (Fin n)) (y : Fin n) :
    safetyProbability sys σ G y≤limitValue sys G y :=
  ENNReal.toReal_le_of_le_ofReal (limitValue_nonnegative sys G y)
    (infiniteSafety_mass_upper sys σ G y)

theorem infiniteSafety_stationary_attains (sys : FiniteControlSystem C n)
    (G : Finset (Fin n)) (y : Fin n) :
    safetyProbability sys (stationaryBehavioral sys (stationaryPolicy sys G)) G y=
      limitValue sys G y := by
  rw [safetyProbability,infiniteSafety_stationary_mass,
    ENNReal.toReal_ofReal (limitValue_nonnegative sys G y)]

/-- Complete infinite-safety contract: one deterministic stationary policy
attains the value simultaneously at every state, against all behavioral pasts. -/
theorem deterministic_stationary_infinite_optimum (sys : FiniteControlSystem C n)
    (G : Finset (Fin n)) :
    ∃ π : StateFeedback sys, ∀ y : Fin n,
      safetyProbability sys (stationaryBehavioral sys π) G y=limitValue sys G y ∧
      ∀ σ : BehavioralPolicy sys, safetyProbability sys σ G y≤limitValue sys G y := by
  exact ⟨stationaryPolicy sys G,fun y =>
    ⟨infiniteSafety_stationary_attains sys G y,fun σ => infiniteSafety_upper sys σ G y⟩⟩

theorem infiniteSafety_isGreatest (sys : FiniteControlSystem C n)
    (G : Finset (Fin n)) (y : Fin n) :
    IsGreatest {p : ℝ | ∃ σ : BehavioralPolicy sys, safetyProbability sys σ G y=p}
      (limitValue sys G y) := by
  constructor
  · exact ⟨stationaryBehavioral sys (stationaryPolicy sys G),infiniteSafety_stationary_attains sys G y⟩
  · rintro p ⟨σ,rfl⟩
    exact infiniteSafety_upper sys σ G y

/-- The finite computed core is exactly the region from which some allowed
controller keeps the actual physical trajectory in G almost surely. -/
theorem invariantCore_iff_almostSureSafety (sys : FiniteControlSystem C n)
    (G : Finset (Fin n)) (y : Fin n) :
    y ∈ invariantCore sys G ↔
      ∃ σ : BehavioralPolicy sys, safetyProbability sys σ G y=1 := by
  rw [invariantCore_eq_valueOneSet,mem_valueOneSet]
  constructor
  · intro hv
    exact ⟨stationaryBehavioral sys (stationaryPolicy sys G),
      (infiniteSafety_stationary_attains sys G y).trans hv⟩
  · rintro ⟨σ,hσ⟩
    exact le_antisymm (limitValue_bounds sys G y).2
      (by simpa only [hσ] using infiniteSafety_upper sys σ G y)

end
end PermanssonResearch.ReverseSolver.InfiniteSafety
