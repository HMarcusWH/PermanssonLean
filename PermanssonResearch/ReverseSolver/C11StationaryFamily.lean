import PermanssonResearch.ReverseSolver.C11ClassStationaryCertificate
import Mathlib.Tactic

/-!
# C11-A — complete finite stationary-certificate family

A complete ordered table must include every computed bottom SCC exactly once.
The order is presentation only; no class is dropped, duplicated or invented.
Every entry must pass the complete rational stationary checker. The family
is not a weighted mixture or a baseline-regime certificate.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace C11

set_option autoImplicit false

open C10

def classKeys {n : ℕ} (rs : List (ClassStationaryCandidate n)) :
    List (Finset (Fin n)) :=
  rs.map (fun r => r.classStates)

def checkStationaryFamily {n : ℕ}
    (K : RationalMarkovMatrix n)
    (rs : List (ClassStationaryCandidate n)) : Bool :=
  decide (0 < n) &&
  decide ((classKeys rs).Nodup) &&
  decide ((classKeys rs).toFinset = bottomClasses K) &&
  rs.all (fun r => checkClassStationary K r)

theorem checkStationaryFamily_sound {n : ℕ}
    (K : RationalMarkovMatrix n) (rs : List (ClassStationaryCandidate n))
    (hc : checkStationaryFamily K rs = true) :
    (classKeys rs).Nodup ∧
    (classKeys rs).toFinset = bottomClasses K ∧
    ∀ r ∈ rs, checkClassStationary K r = true := by
  have hh := (andB_eq_true_iff _ _).mp hc
  have hmid := (andB_eq_true_iff _ _).mp hh.1
  have hl := (andB_eq_true_iff _ _).mp hmid.1
  refine ⟨of_decide_eq_true hl.2, of_decide_eq_true hmid.2, ?_⟩
  intro r hr
  have hAll : ∀ x ∈ rs, checkClassStationary K x = true := by
    simpa only [List.all_eq_true] using hh.2
  exact hAll r hr

/-- An empty table at dimension zero is NOT an accepted family. -/
theorem checkStationaryFamily_zero_rejected
    (K : RationalMarkovMatrix 0)
    (rs : List (ClassStationaryCandidate 0)) :
    checkStationaryFamily K rs = false := by
  cases h : checkStationaryFamily K rs with
  | false => rfl
  | true =>
      unfold checkStationaryFamily at h
      have hh := (andB_eq_true_iff _ _).mp h
      have hmid := (andB_eq_true_iff _ _).mp hh.1
      have hl := (andB_eq_true_iff _ _).mp hmid.1
      have hn : 0 < (0 : ℕ) := of_decide_eq_true hl.1
      omega

/-- Every computed bottom class has a checked receipt entry. -/
theorem checked_family_complete {n : ℕ}
    (K : RationalMarkovMatrix n) (rs : List (ClassStationaryCandidate n))
    (hc : checkStationaryFamily K rs = true)
    (C : Finset (Fin n)) (hC : C ∈ bottomClasses K) :
    ∃ r ∈ rs, r.classStates = C ∧ checkClassStationary K r = true := by
  have h := checkStationaryFamily_sound K rs hc
  have hMember : C ∈ (classKeys rs).toFinset := by
    rw [h.2.1]
    exact hC
  have hm : C ∈ classKeys rs := by simpa using hMember
  rcases List.mem_map.mp hm with ⟨r, hr, hclass⟩
  exact ⟨r, hr, hclass, h.2.2 r hr⟩

/-- Any present entry is one of the genuine complete bottom classes. -/
theorem checked_family_no_extra {n : ℕ}
    (K : RationalMarkovMatrix n) (rs : List (ClassStationaryCandidate n))
    (hc : checkStationaryFamily K rs = true)
    (r : ClassStationaryCandidate n) (hr : r ∈ rs) :
    r.classStates ∈ bottomClasses K := by
  have hAccepted : checkClassStationary K r = true :=
    (checkStationaryFamily_sound K rs hc).2.2 r hr
  exact (checkClassStationary_sound K r hAccepted).2.1

end C11
end ReverseSolver
end PermanssonResearch
