import PermanssonResearch.X1.InterventionNumericalBridge

/-! Candidate literals from certificates/x1_exact_tables.json. The recurrence
is checked below and uniqueness identifies this table with the actual kernels. -/

namespace PermanssonResearch.X1.InterventionNumerics
set_option autoImplicit false

def tableData (learner restrain reset : Bool) : Fin 4 → Fin 18 → ℚ :=
  match learner, restrain, reset with
  | false, false, false => ![
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![1/4, 13/20, 1/4, 13/20, 1/4, 13/20, 1/4, 13/20, 1/4, 13/20, 1/4, 13/20, 1/4, 13/20, 1/4, 13/20, 1/4, 13/20],
    ![7/20, 51/100, 7/20, 51/100, 7/20, 51/100, 7/20, 51/100, 7/20, 51/100, 7/20, 51/100, 7/20, 51/100, 7/20, 51/100, 7/20, 51/100],
    ![39/100, 227/500, 39/100, 227/500, 39/100, 227/500, 39/100, 227/500, 39/100, 227/500, 39/100, 227/500, 39/100, 227/500, 39/100, 227/500, 39/100, 227/500]]
  | false, true, false => ![
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![1/4, 9/10, 1/4, 9/10, 1/4, 9/10, 1/4, 9/10, 1/4, 9/10, 1/4, 9/10, 1/4, 9/10, 1/4, 9/10, 1/4, 9/10],
    ![33/80, 167/200, 33/80, 167/200, 33/80, 167/200, 33/80, 167/200, 33/80, 167/200, 33/80, 167/200, 33/80, 167/200, 33/80, 167/200, 33/80, 167/200],
    ![829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000]]
  | false, false, true => ![
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![1/4, 13/20, 1/4, 13/20, 1/4, 13/20, 1/4, 13/20, 1/4, 13/20, 1/4, 13/20, 1/4, 13/20, 1/4, 13/20, 1/4, 13/20],
    ![7/20, 51/100, 7/20, 51/100, 7/20, 51/100, 7/20, 51/100, 7/20, 51/100, 7/20, 51/100, 7/20, 51/100, 7/20, 51/100, 7/20, 51/100],
    ![39/100, 227/500, 39/100, 227/500, 39/100, 227/500, 39/100, 227/500, 39/100, 227/500, 39/100, 227/500, 39/100, 227/500, 39/100, 227/500, 39/100, 227/500]]
  | false, true, true => ![
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![1/4, 9/10, 1/4, 9/10, 1/4, 9/10, 1/4, 9/10, 1/4, 9/10, 1/4, 9/10, 1/4, 9/10, 1/4, 9/10, 1/4, 9/10],
    ![33/80, 167/200, 33/80, 167/200, 33/80, 167/200, 33/80, 167/200, 33/80, 167/200, 33/80, 167/200, 33/80, 167/200, 33/80, 167/200, 33/80, 167/200],
    ![829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000]]
  | true, false, false => ![
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![361/1600, 7/8, 19/160, 61/80, 19/1600, 13/20, 19/160, 61/80, 1/16, 13/20, 1/160, 43/80, 19/1600, 13/20, 1/160, 43/80, 1/1600, 17/40],
    ![32129/160000, 1846503/3200000, 3287/25600, 66879/160000, 87913/1280000, 57447/160000, 3287/25600, 66879/160000, 2279/25600, 11367/32000, 15959/256000, 208971/640000, 87913/1280000, 57447/160000, 15959/256000, 208971/640000, 146603/2560000, 946287/3200000],
    ![156778329/1024000000, 2062936471/6400000000, 26359593/204800000, 686994469/2560000000, 37975053/409600000, 121690031/512000000, 26359593/204800000, 686994469/2560000000, 23298513/204800000, 8381459/32000000, 195050913/2048000000, 1172162957/5120000000, 37975053/409600000, 121690031/512000000, 195050913/2048000000, 1172162957/5120000000, 1772710593/20480000000, 5050479049/25600000000]]
  | true, true, false => ![
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![1/4, 9/10, 1/4, 9/10, 1/4, 9/10, 1/4, 9/10, 1/4, 9/10, 1/4, 9/10, 1/4, 9/10, 1/4, 9/10, 1/4, 9/10],
    ![33/80, 167/200, 33/80, 167/200, 33/80, 167/200, 33/80, 167/200, 33/80, 167/200, 33/80, 167/200, 33/80, 167/200, 33/80, 167/200, 33/80, 167/200],
    ![829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000]]
  | true, false, true => ![
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![361/1600, 7/8, 19/160, 61/80, 19/1600, 13/20, 19/160, 61/80, 1/16, 13/20, 1/160, 43/80, 19/1600, 13/20, 1/160, 43/80, 1/1600, 17/40],
    ![24967/128000, 369/640, 1693/12800, 3267/6400, 8893/128000, 711/1600, 1693/12800, 3267/6400, 127/1280, 711/1600, 847/12800, 2421/6400, 8893/128000, 711/1600, 847/12800, 2421/6400, 8047/128000, 999/3200],
    ![1813449/10240000, 20543/51200, 143571/1024000, 185549/512000, 1057971/10240000, 41417/128000, 143571/1024000, 185549/512000, 12369/102400, 41417/128000, 103809/1024000, 145787/512000, 1057971/10240000, 41417/128000, 103809/1024000, 145787/512000, 1018209/10240000, 62953/256000]]
  | true, true, true => ![
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![1/4, 9/10, 1/4, 9/10, 1/4, 9/10, 1/4, 9/10, 1/4, 9/10, 1/4, 9/10, 1/4, 9/10, 1/4, 9/10, 1/4, 9/10],
    ![33/80, 167/200, 33/80, 167/200, 33/80, 167/200, 33/80, 167/200, 33/80, 167/200, 33/80, 167/200, 33/80, 167/200, 33/80, 167/200, 33/80, 167/200],
    ![829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000, 829/1600, 3171/4000]]

def stateIndex (y : Y) : Fin 18 :=
  ⟨6 * y.1.1.val + 2 * y.1.2.val + (if y.2 then 1 else 0), by
    have h₁ := y.1.1.isLt
    have h₂ := y.1.2.isLt
    split_ifs <;> omega⟩

def table (learner restrain reset : Bool) (t : Fin 4) (y : Y) : ℚ :=
  tableData learner restrain reset t (stateIndex y)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem table_zero : ∀ (learner restrain reset : Bool) (y : Y),
    table learner restrain reset 0 y = indicator y.2 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem table_step : ∀ (learner restrain reset : Bool) (t : Fin 3) (y : Y),
    table learner restrain reset ⟨t.val + 1, by omega⟩ y =
      ∑ z : Y, entry learner restrain reset y z *
        table learner restrain reset ⟨t.val, by omega⟩ z := by
  decide +kernel

/-- Uniqueness of the checked finite recurrence. The table is not the
definition of the rational dynamic program. -/
theorem table_eq_terminal (learner restrain reset : Bool) (t : Fin 4) (y : Y) :
    table learner restrain reset t y = terminal learner restrain reset t.val y := by
  have h : ∀ (n : ℕ) (hn : n < 4) (z : Y),
      table learner restrain reset ⟨n, hn⟩ z = terminal learner restrain reset n z := by
    intro n
    induction n with
    | zero => intro hn z; exact table_zero learner restrain reset z
    | succ n ih =>
        intro hn z
        rw [show table learner restrain reset ⟨n+1, hn⟩ z =
          ∑ w : Y, entry learner restrain reset z w *
            table learner restrain reset ⟨n, by omega⟩ w from
          table_step learner restrain reset ⟨n, by omega⟩ z]
        simp only [terminal]
        apply Finset.sum_congr rfl
        intro w _
        rw [ih (by omega)]
  exact h t.val t.isLt y

end PermanssonResearch.X1.InterventionNumerics

namespace PermanssonResearch.X1

open PermanssonLean PermanssonLean.RegimeSpecification

theorem original_property_eq_table (m : Mode) (r u : Bool) (y : Y) :
    baselinePropertyValue property (protocolModel m r u) y =
      (InterventionNumerics.table (learnerFlag m) r u 3 y : ℝ) := by
  rw [InterventionNumerics.table_eq_terminal]
  exact original_property_eq_rational m r u y

end PermanssonResearch.X1

