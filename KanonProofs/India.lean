import Mathlib.Tactic

/-!
# India: Schedule VDA, no set-off (#48)

The app's `inReport` (`src/lib/report/report.ts`) and "tax if you sold today" for India (`src/lib/findings/
findings.ts`, `sellAll` and the year's profit): s115BBH of the Income-tax Act and the ITR-2 utility's Schedule VDA.
Every transfer is a row; its income is consideration less cost, entered as nil for a loss (`=MAX(col6 − col5, 0)`); the
total is the sum of the rows' incomes, and a loss can't be set off against any of them. Tax: 30%, plus 4% cess.

Proved, for a list of transfers (cost, consideration):

* each row's income is never below 0, and is consideration less cost when that isn't negative;
* adding a transfer, at a loss or not, never lowers the total;
* the total is at least the net of all the rows (the set-off a loss would give is never taken);
* the tax is 31.2% of the total (30% and 4% cess, multiplied out).

Out of scope: the rounding to whole rupees (each figure rounded, the income from the rounded figures: rule 188 of the
validation rules), the surcharge, the 1% TDS credit, and which coins each transfer took (the lot ledger).
-/

namespace Kanon.India

/-- One row's income: consideration less cost, nil for a loss. -/
def income (cost consideration : ℚ) : ℚ := max (consideration - cost) 0

/-- The year's total: every row's income added up. -/
def total (rows : List (ℚ × ℚ)) : ℚ := (rows.map (fun r => income r.1 r.2)).sum

/-- **#48** A row's income is never below 0, and is consideration less cost when that isn't negative. -/
theorem row_income (c v : ℚ) : 0 ≤ income c v ∧ (c ≤ v → income c v = v - c) := by
  refine ⟨le_max_right _ _, fun h => max_eq_left (by linarith)⟩

/-- **#48** Adding a transfer, at a loss or not, never lowers the total. -/
theorem no_set_off (rows : List (ℚ × ℚ)) (r : ℚ × ℚ) : total rows ≤ total (r :: rows) := by
  simp only [total, List.map_cons, List.sum_cons]
  linarith [(row_income r.1 r.2).1]

/-- **#48** The total is never below the net of all the rows: a loss's set-off is never taken. -/
theorem at_least_net : ∀ (rows : List (ℚ × ℚ)), (rows.map (fun r => r.2 - r.1)).sum ≤ total rows
  | [] => by simp [total]
  | r :: rs => by
    have ih := at_least_net rs
    simp only [total, List.map_cons, List.sum_cons] at *
    have : r.2 - r.1 ≤ income r.1 r.2 := le_max_left _ _
    linarith

/-- The tax: 30% of the total, plus 4% cess on it. -/
def tax (rows : List (ℚ × ℚ)) : ℚ := total rows * (30 / 100) * (104 / 100)

/-- **#48** The tax is 31.2% of the total. -/
theorem tax_rate (rows : List (ℚ × ℚ)) : tax rows = total rows * (312 / 1000) := by
  unfold tax; ring

end Kanon.India
