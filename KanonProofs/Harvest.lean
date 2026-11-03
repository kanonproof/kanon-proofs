import Mathlib.Tactic

/-!
# The tax-loss finder (#38)

For each coin worth less than was paid, KANON shows what selling it today would take off this tax year's tax
(`src/lib/findings/harvest.ts`): the tax on the year's sales so far, by the country's own engine, without and with that
loss. Proved here, for a tax engine that taxes the year's result as one figure (the UK, South Africa, Japan, and Germany
on coins held a year or less), whose tax never falls as that result rises (the brackets of #7) and is never below 0:

* **The saving shown is never below 0 and never more than the tax there is to save.** It is the tax on the year so far
  less the tax with the loss, kept at 0 or more.
* **For the same year so far, a bigger loss never shows a smaller saving.** Not claimed for the US, which taxes
  short-term and long-term results at different rates: there a smaller short-term loss can save more than a bigger
  long-term one.
* **Only losses are listed, and only where they save something:** a coin that would sell at a gain is never listed,
  and nothing is listed when the year so far has no tax to save.
* **US: a net capital loss comes off other income only up to $3,000 a year** ($1,500 married filing separately,
  26 U.S.C. § 1211(b)): the limit itself.

Which coins count (in Germany only those held a year or less, and never a futures result, which is capital income) and
the order the list is shown in (biggest saving first) are how the app builds its input and sorts, tested there.
-/

namespace Kanon.Harvest

variable (tax : ℚ → ℚ)

/-- What a loss `l` (0 or below) would take off the tax on the year's result `g` so far. -/
def saving (g l : ℚ) : ℚ := max (tax g - tax (g + l)) 0

/-- **#38** The saving is never below 0. -/
theorem saving_nonneg (g l : ℚ) : 0 ≤ saving tax g l := le_max_right _ _

/-- **#38** The saving is never more than the year's tax so far, for an engine whose tax is never below 0. -/
theorem saving_le_tax (g l : ℚ) (hpos : ∀ x, 0 ≤ tax x) (h0 : 0 ≤ tax g) : saving tax g l ≤ tax g := by
  unfold saving; have := hpos (g + l); exact max_le (by linarith) h0

/-- **#38** A bigger loss never shows a smaller saving, for an engine whose tax never falls as the result rises. -/
theorem bigger_loss_saves_more (g l l' : ℚ) (hmono : Monotone tax) (h : l ≤ l') :
    saving tax g l' ≤ saving tax g l := by
  unfold saving
  have : tax (g + l) ≤ tax (g + l') := hmono (by linarith)
  exact max_le_max (by linarith) le_rfl

/-- **#38** A gain (selling a coin worth more than it cost) never shows a saving. -/
theorem gain_saves_nothing (g l : ℚ) (hmono : Monotone tax) (h : 0 ≤ l) : saving tax g l = 0 := by
  unfold saving
  have : tax g ≤ tax (g + l) := hmono (by linarith)
  exact max_eq_right (by linarith)

/-- A holding the finder may list: selling every lot today would give `short` (held a year or less) and `long`. -/
structure Holding where
  short : ℚ
  long : ℚ

/-- What counts as the holding's loss: in Germany only coins held a year or less; elsewhere both. -/
def lossOf (germany : Bool) (h : Holding) : ℚ := if germany then h.short else h.short + h.long

/-- Listed when that is a loss and it saves something. -/
def listed (germany : Bool) (g : ℚ) (h : Holding) : Prop :=
  lossOf germany h < 0 ∧ 0 < saving tax g (lossOf germany h)

/-- **#38** When the year so far has no tax to save, nothing is listed. -/
theorem nothing_to_save (germany : Bool) (g : ℚ) (h : Holding) (hpos : ∀ x, 0 ≤ tax x) (h0 : tax g = 0) :
    ¬ listed tax germany g h := by
  intro hl
  have := saving_le_tax tax g (lossOf germany h) hpos (by rw [h0])
  linarith [hl.2]

/-- **#38** A holding that would sell at a gain overall (in Germany: on its coins held a year or less) is never listed,
for an engine whose tax never falls as the result rises. -/
theorem gain_never_listed (germany : Bool) (g : ℚ) (h : Holding) (hmono : Monotone tax) (hg : 0 ≤ lossOf germany h) :
    ¬ listed tax germany g h := by
  intro hl; have h2 := hl.2; rw [gain_saves_nothing tax g _ hmono hg] at h2; exact lt_irrefl _ h2

/-- **#38 US** A net capital loss taken off other income: at most the year's limit, $3,000 ($1,500 married filing
separately), 26 U.S.C. § 1211(b). -/
def usLimit (separately : Bool) : ℚ := if separately then 1500 else 3000

def usOffset (separately : Bool) (net : ℚ) : ℚ := max net (-usLimit separately)

theorem us_cap (separately : Bool) (net : ℚ) : -usLimit separately ≤ usOffset separately net := le_max_right _ _

theorem us_whole_loss_under_cap (separately : Bool) (net : ℚ) (h : -usLimit separately ≤ net) :
    usOffset separately net = net := max_eq_left h

end Kanon.Harvest
