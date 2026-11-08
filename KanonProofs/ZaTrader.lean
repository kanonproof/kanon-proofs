import Mathlib.Tactic

/-!
# South Africa: investing or trading (#51)

SARS taxes crypto "on revenue account under gross income" when it is traded as a business, and as a capital gain
(Eighth Schedule) when it is held as an investment. The app (`src/lib/report/report.ts` zaReport, `src/lib/engine/za.ts`
zaTax with `trader`) uses the person's own answer. For one year with gains less losses `g`, annual exclusion `X ≥ 0`
and no capital loss brought in (a trader carries none):

* **An investor adds 40% of what is left after the exclusion** (the exclusion shrinks the total towards zero, gain or
  loss: paragraphs 5 to 7, 10), **and nothing for a net loss** (proved below).
* **A trader adds `g` in full** (the rule, by definition): no exclusion, no inclusion rate; a net loss counts in full.
* **For a net gain, the trader's figure is never below the investor's**, so choosing "trader" never shows less
  income from a gain than investing would.
-/

namespace Kanon.ZaTrader

/-- The exclusion shrinks the year's total towards zero (gain or loss), never past it. -/
def afterExclusion (g X : ℚ) : ℚ := if g > X then g - X else if g < -X then g + X else 0

/-- What an investor adds to taxable income: 40% of a net gain left after the exclusion (a loss adds nothing now). -/
def investorTaxable (g X : ℚ) : ℚ := max (afterExclusion g X) 0 * (2 / 5)

/-- What a trader adds: the year's gains less losses, in full (the rule itself, as the app applies it; the theorems
below compare it with investing). -/
def traderTaxable (g : ℚ) : ℚ := g

/-- **#51** For a net gain, a trader's taxable figure is never below an investor's. -/
theorem trader_not_below_investor (g X : ℚ) (hg : 0 ≤ g) (hX : 0 ≤ X) : investorTaxable g X ≤ traderTaxable g := by
  unfold investorTaxable traderTaxable afterExclusion
  split_ifs with h1 h2
  · have : max (g - X) 0 = g - X := max_eq_left (by linarith)
    rw [this]; nlinarith
  · linarith
  · simp; linarith

/-- **#51** An investor's figure is 40% of the gain above the exclusion, nothing up to it, and nothing for a net loss. -/
theorem investor_figure (g X : ℚ) (hX : 0 ≤ X) :
    (X < g → investorTaxable g X = (g - X) * (2 / 5)) ∧ (g ≤ X → investorTaxable g X = 0) := by
  constructor
  · intro h; unfold investorTaxable afterExclusion; rw [if_pos h, max_eq_left (by linarith)]
  · intro h; unfold investorTaxable afterExclusion
    rw [if_neg (by linarith)]
    split_ifs with h2
    · rw [max_eq_right (by linarith)]; ring
    · simp

end Kanon.ZaTrader
