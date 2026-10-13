import PermanssonResearch.ReverseSolver.RationalBSCC
import Mathlib.Tactic

/-!
# C10 — exact rational boundary-value certificates

The certificate checker is algebraic. It checks the full list of computed
classes, all Dirichlet boundary/harmonic equations, boundedness, and that
the class weights sum to one at every state. A separate probabilistic
uniqueness theorem is required to identify these checked vectors with
canonical infinite-path absorption probabilities.
-/
namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

/-- A numerical table of class-specific exact rational absorption weights. -/
structure DirichletCertificate (n : ℕ) where
  classes : Finset (Finset (Fin n))
  weight : Finset (Fin n) → Fin n → ℚ

/-- States belonging to any claimed bottom recurrent class. -/
def recurrentUnion {n : ℕ} (cert : DirichletCertificate n) : Finset (Fin n) :=
  cert.classes.biUnion (fun C => C)

/-- Explicit finite rational equations. The first conjunct also ensures
there are no omitted/duplicated classes relative to the executable graph
proposal; this is NOT yet a theorem about the abstract canonical selector. -/
def DirichletConditions {n : ℕ}
    (K : RationalMarkovMatrix n) (cert : DirichletCertificate n) : Prop :=
  cert.classes = bottomClasses K ∧
  (∀ C ∈ cert.classes, ∀ x : Fin n,
    if x ∈ recurrentUnion cert then
      cert.weight C x = (if x ∈ C then 1 else 0)
    else
      cert.weight C x = ∑ y : Fin n, K.entry x y * cert.weight C y) ∧
  (∀ C ∈ cert.classes, ∀ x : Fin n,
    0 ≤ cert.weight C x ∧ cert.weight C x ≤ 1) ∧
  (∀ x : Fin n, (∑ C ∈ cert.classes, cert.weight C x) = 1)

/-- Check class equations through the computable finite *state*
representatives. This avoids quantifying over all possible Finsets, for
which Lean does not synthesize a constructive decidability instance. -/
def ComponentConditions {n : ℕ}
    (K : RationalMarkovMatrix n) (cert : DirichletCertificate n)
    (i : Fin n) : Prop :=
  let C := component K i
  C ∈ cert.classes →
    (∀ x : Fin n,
      if x ∈ recurrentUnion cert then
        cert.weight C x = (if x ∈ C then 1 else 0)
      else cert.weight C x =
        ∑ y : Fin n, K.entry x y * cert.weight C y) ∧
    (∀ x : Fin n, 0 ≤ cert.weight C x ∧ cert.weight C x ≤ 1)

/-- The complete row property only quantifies over physically finite
states, with exact rational comparisons; install its explicit constructive
decider before asking for a finite universal Boolean check. -/
private instance componentConditions_decidable {n : ℕ}
    (K : RationalMarkovMatrix n) (cert : DirichletCertificate n)
    (i : Fin n) :
    Decidable (ComponentConditions K cert i) := by
  unfold ComponentConditions
  infer_instance

/-- Exact finite checker; the graph contract forces every listed class
to be the component of at least one physical state. -/
def checkDirichlet {n : ℕ}
    (K : RationalMarkovMatrix n) (cert : DirichletCertificate n) : Bool :=
  decide (cert.classes = bottomClasses K) &&
  decide (∀ i : Fin n, ComponentConditions K cert i) &&
  decide (∀ x : Fin n,
    (∑ C ∈ cert.classes, cert.weight C x) = 1)

/-- Every listed bottom class has a computed physical representative. -/
private theorem listed_component {n : ℕ}
    (K : RationalMarkovMatrix n) (cert : DirichletCertificate n)
    (hclasses : cert.classes = bottomClasses K)
    (C : Finset (Fin n)) (hC : C ∈ cert.classes) :
    ∃ i : Fin n, component K i = C := by
  have hb : C ∈ bottomClasses K := by simpa [hclasses] using hC
  have hImg : C ∈ (Finset.univ : Finset (Fin n)).image (component K) :=
    (Finset.mem_filter.mp hb).1
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hImg
  exact ⟨i, hi⟩

/-- The checker is sound for the COMPLETE finite list of equations,
including every recurrent boundary, transient harmonic row, bounds and
normalization. Only the finite state type is enumerated at runtime. -/
theorem checkDirichlet_sound {n : ℕ}
    (K : RationalMarkovMatrix n) (cert : DirichletCertificate n)
    (h : checkDirichlet K cert = true) :
    DirichletConditions K cert := by
  unfold checkDirichlet at h
  obtain ⟨hAB, hTotal⟩ := (andB_eq_true_iff _ _).mp h
  obtain ⟨hClass, hRows⟩ := (andB_eq_true_iff _ _).mp hAB
  have hClass' : cert.classes = bottomClasses K :=
    of_decide_eq_true hClass
  have hRows' : ∀ i : Fin n, ComponentConditions K cert i :=
    of_decide_eq_true hRows
  have hTotal' : ∀ x : Fin n,
      (∑ C ∈ cert.classes, cert.weight C x) = 1 :=
    of_decide_eq_true hTotal
  refine ⟨hClass', ?_, ?_, hTotal'⟩
  · intro C hC x
    obtain ⟨i, hi⟩ := listed_component K cert hClass' C hC
    have hAt : ComponentConditions K cert i := hRows' i
    have hMem : component K i ∈ cert.classes := by simpa [hi] using hC
    have hs := (hAt hMem).1 x
    simpa [ComponentConditions, hi] using hs
  · intro C hC x
    obtain ⟨i, hi⟩ := listed_component K cert hClass' C hC
    have hAt : ComponentConditions K cert i := hRows' i
    have hMem : component K i ∈ cert.classes := by simpa [hi] using hC
    have hs := (hAt hMem).2 x
    simpa [ComponentConditions, hi] using hs

/-- Every checked column stays in [0,1], at every state. -/
theorem checked_weight_bounds {n : ℕ}
    (K : RationalMarkovMatrix n) (cert : DirichletCertificate n)
    (h : checkDirichlet K cert = true)
    (C : Finset (Fin n)) (hC : C ∈ cert.classes) (x : Fin n) :
    0 ≤ cert.weight C x ∧ cert.weight C x ≤ 1 :=
  (checkDirichlet_sound K cert h).2.2.1 C hC x

/-- Every checked state's destination probabilities add to exactly one. -/
theorem checked_class_mass_one {n : ℕ}
    (K : RationalMarkovMatrix n) (cert : DirichletCertificate n)
    (h : checkDirichlet K cert = true) (x : Fin n) :
    (∑ C ∈ cert.classes, cert.weight C x) = 1 :=
  (checkDirichlet_sound K cert h).2.2.2 x

end C10
end ReverseSolver
end PermanssonResearch