import PermanssonResearch.ReverseSolver.ComputableFiniteMonitor
import Mathlib.Data.Vector.Basic

/-!
# Array-backed backwards monitor tables

An explicit enumeration of the finite summary state is input data. Each
backwards layer constructs one vector of vectors from the already computed
next layer. Every table lookup is proved equal to the scalar rational
reference recursion. No floating-point operation or numerical tolerance is
used, and no bit-complexity theorem is asserted.
-/

namespace PermanssonResearch.ReverseSolver.FiniteMonitor

open ControlledKernel

variable {C S : Type*} [DecidableEq C] {n q : ℕ}

abbrev MonitorTable (n q : ℕ) := Vector (Vector ℚ q) n

def tableRead (e : Fin q ≃ S) (v : MonitorTable n q) (y : Fin n) (s : S) : ℚ :=
  v[y.val][(e.symm s).val]

def rollingMonitorTable (sys : FiniteControlSystem C n) (M : Monitor C n S)
    (e : Fin q ≃ S) : ℕ → ℕ → MonitorTable n q
  | 0, _ => Vector.ofFn (fun y => Vector.ofFn (fun s => M.reward y (e s)))
  | r+1, t =>
      let next := rollingMonitorTable sys M e r (t+1)
      Vector.ofFn (fun y => Vector.ofFn (fun s =>
        maximumScore sys M (tableRead e next) t y (e s)))

theorem rollingMonitorTable_eq_computedValue (sys : FiniteControlSystem C n)
    (M : Monitor C n S) (e : Fin q ≃ S) (r t : ℕ) (y : Fin n) (s : S) :
    tableRead e (rollingMonitorTable sys M e r t) y s=computedValue sys M r t y s := by
  induction r generalizing t y s with
  | zero => simp only [tableRead,rollingMonitorTable,Vector.getElem_ofFn,
      Fin.eta,Equiv.apply_symm_apply,computedValue]
  | succ r ih =>
      have he : tableRead e (rollingMonitorTable sys M e r (t+1))=
          computedValue sys M r (t+1) := by
        funext z u
        exact ih (t+1) z u
      simpa only [tableRead,rollingMonitorTable,Vector.getElem_ofFn,
        Fin.eta,Equiv.apply_symm_apply,computedValue] using
        congrArg (fun v => maximumScore sys M v t y s) he

theorem rollingMonitorTable_eq_value (sys : FiniteControlSystem C n)
    (M : Monitor C n S) (e : Fin q ≃ S) (r t : ℕ) (y : Fin n) (s : S) :
    tableRead e (rollingMonitorTable sys M e r t) y s=value sys M r t y s :=
  (rollingMonitorTable_eq_computedValue sys M e r t y s).trans
    (computedValue_eq_value sys M r t y s)

end PermanssonResearch.ReverseSolver.FiniteMonitor
