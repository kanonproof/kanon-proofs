import Mathlib.Tactic

/-!
# South Korea: virtual-asset income from 2027 (#44)

The app's engine (`src/lib/engine/kr.ts`, `krTax`) and its "tax if you sold today" (`src/lib/exit/plan.ts`, KR):
virtual-asset income is taxed from 1 January 2027 (a sale or a swap, National Tax Service), on the year's gains and
losses netted together, less a ₩2.5 million basic deduction, at 20%, with local income tax of a tenth of that (22% in
all); nothing before 2027. Coins held before 2027 count at the higher of what was paid and their value at the end of
2026: `deemedCost` is defined in the engine but not applied yet (the app says so). The cost method (Korea's yearly
total average) is outside this proof.

Proved, for the year's net gain `g` (won):

* before 2027, the tax is 0;
* from 2027, it is 0 up to the deduction and 22% of what is above it, never negative;
* more gain never means less tax, and each extra won above the deduction adds 0.22;
* the tax on a sale made today, worked out as the year's tax with it less the year's tax without it (the app's way),
  never goes below 0 for a sale at a gain, and is 0 when the year stays within the deduction;
* the cost counted for a coin held before 2027 is never below what was paid, nor below its end-of-2026 value, and is
  one of the two.
-/

namespace Kanon.Korea

def startYear : ℕ := 2027
def deduction : ℚ := 2500000

/-- The year's tax on its net gain: national 20% over the deduction, plus local tax of a tenth of it. -/
def tax (g : ℚ) (year : ℕ) : ℚ :=
  if year < startYear then 0 else max (g - deduction) 0 * (1 / 5) * (11 / 10)

/-- **#44** Before 2027: nothing. -/
theorem before_2027 (g : ℚ) (year : ℕ) (h : year < startYear) : tax g year = 0 := by
  simp [tax, h]

/-- **#44** From 2027: 22% of what is above the deduction, 0 up to it, never negative. -/
theorem from_2027 (g : ℚ) (year : ℕ) (h : startYear ≤ year) :
    tax g year = max (g - deduction) 0 * (22 / 100) ∧ (g ≤ deduction → tax g year = 0) ∧ 0 ≤ tax g year := by
  have hn : ¬ year < startYear := not_lt.mpr h
  refine ⟨by simp [tax, hn]; ring, fun hg => ?_, ?_⟩
  · simp [tax, hn, max_eq_right (sub_nonpos.mpr hg)]
  · simp only [tax, hn, if_false]; positivity

/-- **#44** More gain never means less tax. -/
theorem monotone (g g' : ℚ) (year : ℕ) (h : g ≤ g') : tax g year ≤ tax g' year := by
  unfold tax; split_ifs
  · exact le_refl _
  · have : max (g - deduction) 0 ≤ max (g' - deduction) 0 := max_le_max (by linarith) (le_refl _)
    nlinarith

/-- **#44** Above the deduction, each extra won adds exactly 0.22. -/
theorem marginal (g d : ℚ) (year : ℕ) (hy : startYear ≤ year) (hg : deduction ≤ g) (hd : 0 ≤ d) :
    tax (g + d) year - tax g year = d * (22 / 100) := by
  rw [(from_2027 _ _ hy).1, (from_2027 _ _ hy).1, max_eq_left (by linarith), max_eq_left (by linarith)]; ring

/-- The tax on a sale made today: the year's tax with it, less without it (`taxOn`, KR). -/
def saleTax (sofar gain : ℚ) (year : ℕ) : ℚ := tax (sofar + gain) year - tax sofar year

/-- **#44** A sale at a gain never has tax below 0, and has none when the year stays within the deduction. -/
theorem sale_tax (sofar gain : ℚ) (year : ℕ) (hg : 0 ≤ gain) :
    0 ≤ saleTax sofar gain year ∧ (sofar + gain ≤ deduction → saleTax sofar gain year ≤ 0) := by
  unfold saleTax
  refine ⟨sub_nonneg.mpr (monotone _ _ _ (by linarith)), fun h => ?_⟩
  by_cases hy : year < startYear
  · simp [before_2027 _ _ hy]
  · have hy' : startYear ≤ year := not_lt.mp hy
    rw [(from_2027 _ _ hy').2.1 h]; linarith [(from_2027 sofar _ hy').2.2]

/-- What a coin held before 2027 counts as costing. -/
def deemedCost (paid endOf2026 : ℚ) : ℚ := max paid endOf2026

/-- **#44** Never below what was paid, never below the end-of-2026 value, and one of the two. -/
theorem deemed_cost (paid v : ℚ) :
    paid ≤ deemedCost paid v ∧ v ≤ deemedCost paid v ∧ (deemedCost paid v = paid ∨ deemedCost paid v = v) := by
  unfold deemedCost
  exact ⟨le_max_left _ _, le_max_right _ _, max_choice _ _⟩

end Kanon.Korea
