import Mathlib.Tactic

/-!
# Brazil: crypto on foreign platforms from 2024 (#46)

Lei 14.754/2023 as the app applies it (`src/lib/engine/br.ts`, `abroadYears`; the rule and its sources in the app's
`data/official/br-abroad.md`): sales on a foreign platform from 2024 leave the monthly regime (no R$35,000 exemption, no
monthly DARF); each year's results net together; a net gain, less the loss carried in, is taxed at 15% with the
annual return; a net loss carries forward with what is left, each loss used once, no carry-back.

Proved, for a year's net result `r` and the loss carried in `c` (≥ 0):

* the tax is 15% of what is left after the carried loss, 0 when nothing is left, never below 0;
* the loss carried on is exactly what the year's result and the carried loss leave negative, never below 0;
* a year either pays tax or carries a loss on, never both;
* over a run of years, the taxes in all are exactly 15% of the results added up, less the loss carried in, plus the
  loss still carried at the end: every loss comes off once, none is used twice or lost.

Out of scope: which sales are on a foreign platform (the app's list of Brazilian platforms), the reais conversion and
the average cost.
-/

namespace Kanon.BrAbroad

/-- One year: the tax and the loss carried on. -/
def year (r c : ℚ) : ℚ × ℚ :=
  if 0 < r - c then ((15 / 100) * (r - c), 0) else (0, c - r)

/-- **#46** The tax is 15% of what the carried loss leaves, never below 0; the loss carried on is what is left
negative, never below 0; never both. -/
theorem year_rule (r c : ℚ) :
    (year r c).1 = (15 / 100) * max (r - c) 0 ∧ (year r c).2 = max (c - r) 0 ∧ 0 ≤ (year r c).1 ∧ 0 ≤ (year r c).2 ∧
      ((year r c).1 = 0 ∨ (year r c).2 = 0) := by
  unfold year
  split_ifs with h
  · refine ⟨by rw [max_eq_left h.le], by rw [max_eq_right (by linarith)], by positivity, le_refl _, Or.inr rfl⟩
  · push_neg at h
    refine ⟨by rw [max_eq_right h]; ring, by rw [max_eq_left (by linarith)], le_refl _, by linarith, Or.inl rfl⟩

/-- A run of years: the taxes in all, and the loss still carried at the end. -/
def run : List ℚ → ℚ → ℚ × ℚ
  | [], c => (0, c)
  | r :: rs, c =>
    let y := year r c
    let rest := run rs y.2
    (y.1 + rest.1, rest.2)

/-- **#46** Over a run of years, the taxes in all are 15% of (the results added up, less the loss carried in, plus the
loss still carried at the end): every loss comes off once, none is lost. -/
theorem run_conserves : ∀ (rs : List ℚ) (c : ℚ),
    (run rs c).1 = (15 / 100) * (rs.sum - c + (run rs c).2)
  | [], c => by simp [run]
  | r :: rs, c => by
    have ih := run_conserves rs (year r c).2
    simp only [run, List.sum_cons]
    rw [ih]
    unfold year
    split_ifs with h
    · ring
    · ring

end Kanon.BrAbroad
