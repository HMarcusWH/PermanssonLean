import PermanssonResearch.MultiAgent.Protocols

/-! F-FEAS: legal actions must intersect across the entire own-key fibre.
The statements use actual probability kernels. Nonempty individual legal
menus alone are insufficient. No reachable-domain shortcut is assumed. -/

open MeasureTheory ProbabilityTheory Set PermanssonLean
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultiAgent

def fibreLegal {Y Q A : Type*} (q : Y → Q) (legal : Y → Set A) (k : Q) : Set A :=
  {a | ∀ y, q y = k → a ∈ legal y}

theorem measurableSet_fibreLegal
    {Y Q A : Type*} [Countable Y] [MeasurableSpace A]
    (q : Y → Q) (legal : Y → Set A) (hlegal : ∀ y, MeasurableSet (legal y)) (k : Q) :
    MeasurableSet (fibreLegal q legal k) := by
  classical
  have heq : fibreLegal q legal k = ⋂ y, {a | q y = k → a ∈ legal y} := by
    ext a
    simp [fibreLegal]
  rw [heq]
  apply MeasurableSet.iInter
  intro y
  by_cases h : q y = k
  · simpa [h] using hlegal y
  · simp [h]

/-- Full legal mass at every state is exactly full mass in each realized
fibre intersection. Countability licenses the simultaneous AE intersection. -/
theorem keyLaw_feasible_iff
    {Y Q A : Type*} [Countable Y] [MeasurableSpace Q] [MeasurableSpace A]
    (q : Y → Q) (legal : Y → Set A) (hlegal : ∀ y, MeasurableSet (legal y))
    (K : Kernel Q A) [IsMarkovKernel K] :
    (∀ y, K (q y) (legal y) = 1) ↔
      ∀ k ∈ Set.range q, K k (fibreLegal q legal k) = 1 := by
  classical
  constructor
  · intro h k hk
    apply (mem_ae_iff_prob_eq_one (measurableSet_fibreLegal q legal hlegal k)).mp
    change ∀ᵐ a ∂K k, ∀ y, q y = k → a ∈ legal y
    rw [ae_all_iff]
    intro y
    by_cases hy : q y = k
    · have hprob : K k (legal y) = 1 := hy ▸ h y
      have hae := (mem_ae_iff_prob_eq_one (hlegal y)).mpr hprob
      simpa [hy] using hae
    · simp [hy]
  · intro h y
    have hae := (mem_ae_iff_prob_eq_one
      (measurableSet_fibreLegal q legal hlegal (q y))).mpr (h (q y) ⟨y, rfl⟩)
    apply (mem_ae_iff_prob_eq_one (hlegal y)).mp
    filter_upwards [hae] with a ha
    exact ha y rfl

/-- Exact finite existence criterion; a deterministic own-key selector is a
witness whenever all fibre intersections are nonempty. -/
theorem exists_feasible_keyKernel_iff
    {Y Q A : Type*} [Finite Y] [Finite Q]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [MeasurableSpace A] [MeasurableSingletonClass A] [Finite A]
    (q : Y → Q) (hq : Function.Surjective q) (legal : Y → Set A) :
    (∃ K : Kernel Q A, IsMarkovKernel K ∧ ∀ y, K (q y) (legal y) = 1) ↔
      ∀ k, (fibreLegal q legal k).Nonempty := by
  classical
  have hlegal : ∀ y, MeasurableSet (legal y) :=
    fun y => (Set.to_countable (legal y)).measurableSet
  constructor
  · rintro ⟨K, hK, hfeas⟩ k
    letI : IsMarkovKernel K := hK
    have hmass := (keyLaw_feasible_iff q legal hlegal K).mp hfeas k (hq k)
    by_contra hn
    have hempty : fibreLegal q legal k = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [hempty] at hmass
  · intro h
    let f : Q → A := fun k => Classical.choose (h k)
    have hf : ∀ k, f k ∈ fibreLegal q legal k := fun k => Classical.choose_spec (h k)
    let K : Kernel Q A := Kernel.deterministic f (measurable_of_countable f)
    refine ⟨K, inferInstance, ?_⟩
    intro y
    have hmem : f (q y) ∈ legal y := hf (q y) y rfl
    simp [K, Kernel.deterministic_apply, Measure.dirac_apply, hlegal y, hmem]

/-- The old private state is a lawful strict update; any feasible key action
kernel therefore extends to an actual original player-two mechanism. -/
noncomputable def strictAnchorOfKeyKernel
    {S0 S1 S2 X A1 A2 : Type*}
    [MeasurableSpace S0] [MeasurableSpace S1] [MeasurableSpace S2]
    [MeasurableSpace X] [MeasurableSpace A1] [MeasurableSpace A2]
    (K : Kernel (S0 × S2) A2) [IsMarkovKernel K] :
    PlayerTwoMechanism S0 S1 S2 X A1 A2 where
  action := K.comap anchorKey measurable_anchorKey
  update := (Kernel.deterministic (fun u : (S0 × S2) × A2 => u.1.2)
    (by fun_prop)).comap anchorUpdateKey measurable_anchorUpdateKey
  action_isMarkov := inferInstance
  update_isMarkov := inferInstance

theorem strictAnchorOfKeyKernel_strict
    {S0 S1 S2 X A1 A2 : Type*}
    [MeasurableSpace S0] [MeasurableSpace S1] [MeasurableSpace S2]
    [MeasurableSpace X] [MeasurableSpace A1] [MeasurableSpace A2]
    (K : Kernel (S0 × S2) A2) [IsMarkovKernel K] :
    IsStrictlyNonReactive (strictAnchorOfKeyKernel (S1 := S1) (X := X) (A1 := A1) K) :=
  ⟨⟨K, rfl⟩, ⟨_, rfl⟩⟩

/-- Finite legal-action criterion for the original strict player-two mechanism.
The restriction is imposed at every state in an own-key fibre. -/
theorem exists_feasible_strictAnchor_iff
    {S0 S1 S2 X A1 A2 : Type*}
    [MeasurableSpace S0] [MeasurableSpace S1] [MeasurableSpace S2]
    [MeasurableSpace X] [MeasurableSpace A1] [MeasurableSpace A2]
    [Finite S0] [Finite S1] [Finite S2] [Finite X] [Finite A2]
    [MeasurableSingletonClass S0] [MeasurableSingletonClass S1]
    [MeasurableSingletonClass S2] [MeasurableSingletonClass X]
    [MeasurableSingletonClass A2] [Nonempty S1] [Nonempty X]
    (legal : JointState (GameState S0 S1 S2) X → Set A2) :
    (∃ a : PlayerTwoMechanism S0 S1 S2 X A1 A2,
      IsStrictlyNonReactive a ∧ ∀ y, a.action y (legal y) = 1) ↔
      ∀ k : S0 × S2, (fibreLegal anchorKey legal k).Nonempty := by
  classical
  let rep : S0 × S2 → JointState (GameState S0 S1 S2) X :=
    fun k => ((k.1, (Classical.choice ‹Nonempty S1›, k.2)),
      Classical.choice ‹Nonempty X›)
  have hq : Function.Surjective
      (anchorKey (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) :=
    fun k => ⟨rep k, rfl⟩
  constructor
  · rintro ⟨a, ha, hlegal⟩
    letI := a.action_isMarkov
    let K : Kernel (S0 × S2) A2 := a.action.comap rep (measurable_of_countable rep)
    apply (exists_feasible_keyKernel_iff anchorKey hq legal).mp
    refine ⟨K, inferInstance, fun y => ?_⟩
    change a.action (rep (anchorKey y)) (legal y) = 1
    rw [ha.action_eq (y := rep (anchorKey y)) (y' := y) rfl]
    exact hlegal y
  · intro h
    obtain ⟨K, hK, hlegal⟩ := (exists_feasible_keyKernel_iff anchorKey hq legal).mpr h
    letI := hK
    refine ⟨strictAnchorOfKeyKernel K, strictAnchorOfKeyKernel_strict K, ?_⟩
    intro y
    exact hlegal y

section OrderedSelector

variable {Y Q A : Type*} [Fintype Y] [Fintype A] [LinearOrder A] [DecidableEq Q]
variable (q : Y → Q) (legal : Y → Set A) [hlegalDec : ∀ y, DecidablePred (legal y)]

/-- Executable finite intersection, with the input action order held fixed. -/
def legalFibreMenu (k : Q) : Finset A := by
  letI : DecidablePred (fun a : A => ∀ y, q y = k → a ∈ legal y) := fun a => by
    letI : DecidablePred (fun y : Y => q y = k → a ∈ legal y) := fun y => by
      letI : Decidable (a ∈ legal y) := hlegalDec y a
      infer_instance
    exact Fintype.decidableForallFintype
  exact Finset.univ.filter fun a => ∀ y, q y = k → a ∈ legal y

theorem mem_legalFibreMenu (k : Q) (a : A) :
    a ∈ legalFibreMenu q legal k ↔ a ∈ fibreLegal q legal k := by
  simp [legalFibreMenu, fibreLegal]

theorem legalFibreMenu_nonempty (k : Q) (h : (fibreLegal q legal k).Nonempty) :
    (legalFibreMenu q legal k).Nonempty := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, (mem_legalFibreMenu q legal k a).mpr ha⟩

def leastFibreAction (k : Q) (h : (fibreLegal q legal k).Nonempty) : A :=
  (legalFibreMenu q legal k).min' (legalFibreMenu_nonempty q legal k h)

theorem leastFibreAction_legal (k : Q) (h : (fibreLegal q legal k).Nonempty) :
    leastFibreAction q legal k h ∈ fibreLegal q legal k :=
  (mem_legalFibreMenu q legal k _).mp (Finset.min'_mem _ _)

theorem leastFibreAction_le (k : Q) (h : (fibreLegal q legal k).Nonempty)
    (a : A) (ha : a ∈ fibreLegal q legal k) : leastFibreAction q legal k h ≤ a :=
  Finset.min'_le _ _ ((mem_legalFibreMenu q legal k a).mpr ha)

end OrderedSelector

end PermanssonResearch.MultiAgent
