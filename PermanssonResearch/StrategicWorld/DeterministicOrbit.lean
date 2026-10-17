import PermanssonLean.StrategicWorld.WellPosedness
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-!
# Deterministic strategic-world models (research support for F1)

If every one-step induced kernel is a Dirac mass `δ_{f y}`, the canonical path
law from `δ_y` is the Dirac mass at the orbit `n ↦ f^[n] y`. This is proved for
ARBITRARY measurable spaces through the frozen v0.1.8 uniqueness theorem
`pathLaw_existsUnique` (no singleton-measurability needed for the path law).
For deterministic `α → P → U` components on singleton-measurable action and world
spaces, `inducedKernel_eq_dirac_of_deterministic` identifies the induced kernel.
Used by the F1 protocol witnesses; nothing here restricts the general theorems.
-/

namespace PermanssonResearch.StrategicWorld

set_option autoImplicit false
open PermanssonLean

universe uS uX uA uW uK
variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

/-- The orbit `n ↦ f^[n] y` of a deterministic one-step map. -/
def detOrbit (f : JointState S X → JointState S X) (y : JointState S X) :
    ℕ → JointState S X :=
  fun n => f^[n] y

omit [MeasurableSpace S] [MeasurableSpace X] in
theorem detOrbit_succ (f : JointState S X → JointState S X) (y : JointState S X) (n : ℕ) :
    detOrbit f y (n+1) = f (detOrbit f y n) := by
  simp [detOrbit, Function.iterate_succ_apply']

/-- A Dirac first law composed with a Markov kernel is the pushforward of the
kernel row along the pairing map (no singleton-measurability needed). -/
theorem dirac_compProd_eq_map {W : Type uW} {K : Type uK} [MeasurableSpace W]
    [MeasurableSpace K] (p : W) (κ : Kernel W K) [IsMarkovKernel κ] :
    Measure.dirac p ⊗ₘ κ = (κ p).map (Prod.mk p) := by
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.compProd_apply_prod hs ht,
    ← lintegral_indicator hs,
    lintegral_dirac' _ ((Kernel.measurable_coe κ ht).indicator hs),
    Measure.map_apply measurable_prodMk_left (hs.prod ht)]
  by_cases hp : p ∈ s
  · rw [Set.indicator_of_mem hp]
    congr 1
    ext z; simp [hp]
  · rw [Set.indicator_of_notMem hp]
    have : (Prod.mk p ⁻¹' (s ×ˢ t) : Set K) = ∅ := by
      ext z; simp [hp]
    rw [this, measure_empty]

/-- **Deterministic canonical path law.** If the induced kernel is the Dirac
mass at `f y` for every `y`, the canonical path law from `y` is the Dirac mass
at the deterministic orbit. Arbitrary measurable spaces; proved by the frozen
v0.1.8 well-posedness uniqueness theorem. -/
theorem pathLaw_dirac_of_deterministic
    (M : StrategicWorldModel S X A)
    (f : JointState S X → JointState S X)
    (hK : ∀ y, M.inducedKernel y = Measure.dirac (f y))
    (y : JointState S X) :
    M.pathLaw (Measure.dirac y) = Measure.dirac (detOrbit f y) := by
  have := StrategicWorldModel.inducedKernel_isMarkov M
  refine (StrategicWorldModel.pathLaw_existsUnique M (Measure.dirac y)).unique
    (StrategicWorldModel.pathLaw_spec M (Measure.dirac y))
    ⟨inferInstance, ?_, ?_⟩
  · rw [Measure.map_dirac' (Preorder.measurable_frestrictLe 0),
      Measure.map_dirac' (MeasurableEquiv.measurable _)]
    congr 1
    funext i
    have hi : (i : ℕ) = 0 := Nat.le_zero.mp (Finset.mem_Iic.mp i.2)
    change detOrbit f y i = _
    rw [hi]
    rfl
  · intro n
    rw [Measure.map_dirac' (Preorder.measurable_frestrictLe n),
      Measure.map_dirac' (by fun_prop), dirac_compProd_eq_map]
    change ((M.inducedKernel (detOrbit f y n))).map _ = _
    rw [hK, Measure.map_dirac' measurable_prodMk_left]
    congr 1
    exact Prod.ext rfl (detOrbit_succ f y n).symm

/-- Deterministic `α → P → U` (singleton-measurable action and world spaces):
the induced kernel is the Dirac mass at the composed step. -/
theorem inducedKernel_eq_dirac_of_deterministic
    [MeasurableSingletonClass X] [MeasurableSingletonClass A]
    (M : StrategicWorldModel S X A)
    (ga : JointState S X → A) (gw : WorldInput S X A → X) (gu : UpdateInput S X A → S)
    (ha : ∀ y, M.generator.action y = Measure.dirac (ga y))
    (hw : ∀ i, M.world i = Measure.dirac (gw i))
    (hu : ∀ i, M.generator.update i = Measure.dirac (gu i))
    (y : JointState S X) :
    M.inducedKernel y =
      Measure.dirac (gu ((y, ga y), gw (y, ga y)), gw (y, ga y)) := by
  ext E hE
  rw [StrategicWorldModel.inducedKernel_apply M y hE, ha, lintegral_dirac, hw,
    lintegral_dirac, hu,
    Measure.dirac_apply' _ (show MeasurableSet {s' | (s', gw (y, ga y)) ∈ E} from
      hE.preimage measurable_prodMk_right),
    Measure.dirac_apply' _ hE]
  simp [Set.indicator]

end PermanssonResearch.StrategicWorld
