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
  decide (classKeys rs).Nodup &&
  decide ((classKeys rs).toFinset = bottomClasses K) &&
  rs.all (fun r => checkClassStationary K r)

theorem checkStationaryFamily_sound {n : ℕ}
    (K : RationalMarkovMatrix n) (rs : List (ClassStationaryCandidate n))
    (hc : checkStationaryFamily K rs = true) :
    (classKeys rs).Nodup ∧
    (classKeys rs).toFinset = bottomClasses K ∧
    ∀ r ∈ rs, checkClassStationary K r = true := by
  have hh := (andB_eq_true_iff _ _).mp hc
  have hl := (andB_eq_true_iff _ _).mp hh.1
  refine ⟨of_decide_eq_true hl.1, of_decide_eq_true hl.2, ?_⟩
  intro r hr
  have hAll : ∀ x ∈ rs, checkClassStationary K x = true := by
    simpa only [List.all_eq_true] using hh.2
  exact hAll r hr

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
  exact (checkClassStationary_sound K r
    (checkStationaryFamily_sound K rs hc).2.2 r hr).2.1

end C11
end ReverseSolver
end PermanssonResearch
