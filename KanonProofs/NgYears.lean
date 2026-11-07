import Mathlib.Tactic

/-!
# Nigeria: the year's crypto gains from 2026 (#49)

The app's `ngReport` (`src/lib/report/report.ts`): NRS guidelines on the taxation of virtual assets (31 July 2026),
9.4, under the Nigeria Tax Act 2025. Each year's gains and losses (each worked out in dollars and turned into naira at
its day's rate, 9.1) net together; a net loss carries forward with no end and comes off only later crypto gains; what
is left is the year's taxable crypto income.

Proved, for a year's net result `r` and the loss carried in `c` (≥ 0):

* what is taxable is what the carried loss leaves, never below 0; the loss carried on is what is left negative, never
  below 0; a year has one or the other, never both;
* over a run of years, the taxable amounts added up are exactly the results added up, less the loss carried in, plus
  the loss still carried at the end: every loss comes off once, none is lost or used twice.

Out of scope: the dollar working and the rates (9.1; the app's reader), the income tax bands on the result (#9's
model of Nigeria's bands), the 1% withholding credit, and years up to 2025 (Capital Gains Tax, shown as an estimate).
-/

namespace Kanon.NgYears

/-- One year: what is taxable, and the loss carried on. -/
def year (r c : ℚ) : ℚ × ℚ := (max (r - c) 0, max (c - r) 0)

/-- **#49** One year: taxable is what the carried loss leaves; the loss carried on is what is left negative; never
below 0; never both. -/
theorem year_rule (r c : ℚ) :
    0 ≤ (year r c).1 ∧ 0 ≤ (year r c).2 ∧ ((year r c).1 = 0 ∨ (year r c).2 = 0) ∧ (year r c).1 - (year r c).2 = r - c := by
  simp only [year]
  rcases le_total (r - c) 0 with h | h
  · refine ⟨le_max_right _ _, le_max_right _ _, Or.inl (max_eq_right h), ?_⟩
    rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · refine ⟨le_max_right _ _, le_max_right _ _, Or.inr (max_eq_right (by linarith)), ?_⟩
    rw [max_eq_left h, max_eq_right (by linarith)]; ring

/-- A run of years: the taxable amounts added up, and the loss still carried at the end. -/
def run : List ℚ → ℚ → ℚ × ℚ
  | [], c => (0, c)
  | r :: rs, c =>
    let y := year r c
    let rest := run rs y.2
    (y.1 + rest.1, rest.2)

/-- **#49** Over a run of years: taxable in all = the results added up, less the loss carried in, plus what's still
carried at the end. -/
theorem run_conserves : ∀ (rs : List ℚ) (c : ℚ), (run rs c).1 = rs.sum - c + (run rs c).2
  | [], c => by simp [run]
  | r :: rs, c => by
    have ih := run_conserves rs (year r c).2
    have hy := (year_rule r c).2.2.2
    simp only [run, List.sum_cons]
    rw [ih]; linarith

end Kanon.NgYears
