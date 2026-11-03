import Mathlib.Tactic
import KanonProofs.Lots

/-!
# Germany: the Anlage SO and futures results (#37)

Coins held privately in Germany are taxed under § 23 EStG (private Veräußerungsgeschäfte), as KANON's report
(`src/lib/report/report.ts`, `deReport`, `deLines`; `src/lib/engine/de.ts`, `deTaxableGain`) works it out:

* **The threshold is all or nothing (Freigrenze, § 23 (3) sentence 5).** If the year's net result from such sales is
  under the threshold (€1,000 from 2024, €600 before), none of it is taxed; at the threshold or above, all of it is.
  The threshold is never taken off like an allowance.
* **Each sale is counted once, in one place** (by construction: the report's order of tests, written out). A sale of coins held more than a year is tax-free (§ 23 (1) no. 2) and
  only counted as such; a futures result (a Hyperliquid position's profit or loss) is not a private sale and is kept
  off the form, totalled apart (capital income, Anlage KAP); coins given up as fees or that left with no record are not
  sales, nor is a part sold for nothing that cost nothing. Every other sale is a row of the form. No sale is in two of
  these, and none is lost.
* **The form's lines add up** (by construction, as `deLines` builds them). Lines 46-51 take the first sale (proceeds 48, cost 49, result 51 = 48 - 49) and line 59
  the rest, in whole euros: 51 + 59 is the year's result, rounded, exactly.
* **The threshold by year** is the model's; the app's estimate of this year's tax uses €1,000 (every year it estimates
  is 2024 or later), and its report shows each year's own threshold.
* **A futures result is held since the position opened, and leaves nothing behind.** A gain is booked as that part of
  the position, bought for nothing on the day it was opened, sold for the gain; a loss as that part bought for the
  coins given up and ended worth nothing. In the lot ledger the result's gain is exactly the profit or loss, its lot
  is dated to the opening day, and no coins of the position are left over afterwards (`toEvents`, kind `result`).

The holding period itself (more than a year, on calendar dates) is proved in `Tightened.lean`; the income tax tariff is
checked against the Federal Finance Ministry's calculator in the app's tests.
-/

namespace Kanon.Germany

/-- The year's threshold in euros: €600 up to 2023, €1,000 from 2024 (Wachstumschancengesetz). -/
def threshold (year : ℕ) : ℚ := if 2024 ≤ year then 1000 else 600

/-- The taxable part of a year's net private-sale result `g`. -/
def taxable (year : ℕ) (g : ℚ) : ℚ := if g < threshold year then 0 else g

/-- **#37 Freigrenze** Under the threshold, nothing of the year's result is taxed. -/
theorem under_threshold (year : ℕ) (g : ℚ) (h : g < threshold year) : taxable year g = 0 := by
  simp [taxable, h]

/-- **#37 Freigrenze** At the threshold or above, all of it is taxed: the threshold is not taken off. -/
theorem at_or_over (year : ℕ) (g : ℚ) (h : threshold year ≤ g) : taxable year g = g := by
  simp [taxable, not_lt.mpr h]

/-- **#37 Freigrenze** The taxable part is either nothing or the whole result, never a part of it. -/
theorem all_or_nothing (year : ℕ) (g : ℚ) : taxable year g = 0 ∨ taxable year g = g := by
  unfold taxable; split_ifs <;> simp

/-- **#37 Freigrenze** A year's net loss is never taxed. -/
theorem loss_untaxed (year : ℕ) (g : ℚ) (h : g ≤ 0) : taxable year g = 0 := by
  apply under_threshold; unfold threshold; split_ifs <;> linarith

/-! ### Each sale counted once -/

/-- What a ledger sale is, as far as the report is concerned. -/
structure Sale where
  /-- A real sale (not coins given up as a fee, nor coins that left with no record). -/
  real : Bool
  /-- Nothing sold for nothing (an empty part). -/
  empty : Bool
  futures : Bool
  /-- Held more than a year. -/
  long : Bool
  gain : ℚ

inductive Place | skipped | futures | taxFree | onForm
  deriving DecidableEq

/-- Where the report puts a sale, in the order it decides. -/
def place (s : Sale) : Place :=
  if s.real = false ∨ s.empty then .skipped
  else if s.futures then .futures
  else if s.long then .taxFree
  else .onForm

def countAt (p : Place) (ss : List Sale) : ℕ := (ss.filter (fun s => place s = p)).length

/-- The year's result on the form: the sum of its rows. -/
def formResult (ss : List Sale) : ℚ := ((ss.filter (fun s => place s = .onForm)).map Sale.gain).sum

/-- **#37** Every sale is in exactly one place: skipped, futures, tax-free or on the form. -/
theorem counted_once (ss : List Sale) :
    countAt .skipped ss + countAt .futures ss + countAt .taxFree ss + countAt .onForm ss = ss.length := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    simp only [countAt, List.filter_cons] at ih ⊢
    cases h : place s <;> simp <;> omega

/-- **#37** A futures result is never on the Anlage SO, and never counted as tax-free under the one-year rule. -/
theorem futures_off_form (s : Sale) (hr : s.real = true) (he : s.empty = false) (hf : s.futures = true) :
    place s = .futures := by
  simp [place, hr, he, hf]

/-- **#37** A real sale of coins held a year or less that isn't a futures result is a row of the form. -/
theorem short_on_form (s : Sale) (hr : s.real = true) (he : s.empty = false) (hf : s.futures = false)
    (hl : s.long = false) : place s = .onForm := by
  simp [place, hr, he, hf, hl]

/-- **#37** Coins held more than a year never add to the form's result, whatever they sold for. -/
theorem long_not_in_result (ss : List Sale) (s : Sale) (hl : s.long = true) :
    formResult (s :: ss) = formResult ss := by
  simp [formResult, List.filter_cons, place, hl]
  split_ifs <;> simp_all

/-! ### The form's lines -/

/-- Lines 48, 49, 51 and 59 from the rows' proceeds and costs (already in cents) and the year's result. -/
structure Lines where
  r48 : ℤ
  r49 : ℤ
  r51 : ℤ
  r59 : ℤ

/-- `round` is the rounding to whole euros the form uses; the first row's figures and the year's result go in. -/
def lines (round : ℚ → ℤ) (firstProceeds firstCost yearResult : ℚ) : Lines :=
  let r48 := round firstProceeds
  let r49 := round firstCost
  { r48, r49, r51 := r48 - r49, r59 := round yearResult - (r48 - r49) }

/-- **#37** Line 51 is line 48 less line 49, and lines 51 and 59 add up to the year's result in whole euros. -/
theorem lines_add_up (round : ℚ → ℤ) (p c g : ℚ) :
    (lines round p c g).r51 = (lines round p c g).r48 - (lines round p c g).r49 ∧
      (lines round p c g).r51 + (lines round p c g).r59 = round g := by
  simp [lines]

/-! ### Futures results in the lot ledger -/

open Kanon.Lots in
/-- A result of a position opened on day `opened`, of size `q` (in smallest units, `q > 0`): a gain of `g` cents, or a
loss of `l` cents (one of them 0). The lot booked, dated to the opening: a gain's costs nothing, a loss's costs the
coins given up. It is then sold whole: a gain's for `g`, a loss's for nothing. -/
def resultLot (opened q l : ℕ) : Kanon.Lots.Lot := { acquired := opened, qty := q, cost := l }

open Kanon.Lots in
/-- **#37 Futures** In the lot ledger (#3's sale), the result's lot is sold whole at the cost it was booked at, so the
gain (what it sold for less that cost) is exactly the profit `g` (booked at no cost, sold for `g`) or the loss `-l`
(booked at `l`, sold for nothing); the lot is dated to the day the position was opened; and nothing of the position is
left over. -/
theorem result_exact (opened q g l : ℕ) (hq : 0 < q) :
    ((g : ℤ) - (sell [resultLot opened q 0] q).2.1 = g ∧ (sell [resultLot opened q 0] q).2.2 = []) ∧
      ((0 : ℤ) - (sell [resultLot opened q l] q).2.1 = -(l : ℤ) ∧ (sell [resultLot opened q l] q).2.2 = []) ∧
      (sell [resultLot opened q l] q).1 = q ∧ (resultLot opened q l).acquired = opened := by
  have h0 : q ≠ 0 := Nat.pos_iff_ne_zero.mp hq
  simp [sell, resultLot, h0]

end Kanon.Germany
