import Mathlib.Tactic

/-!
# UK 2024/25: the rate change on 30 October 2024 (#52)

Capital Gains Tax on "other" gains (crypto) rose from 10%/20% to 18%/24% for disposals from 30 October 2024. HMRC's
SA108 notes 2025 (page CGN 13): the annual exempt amount and allowable losses are set first against the gains on or
after 30 October (the higher rates), then against the earlier gains. The app (`src/lib/report/report.ts`, gbReport,
`taxRange`) does that and shows the tax between all-in-the-basic-band (10% and 18%) and none-in-it (20% and 24%).

Proved, for gains `pre` (to 29 October) and `post` (from 30 October), deductions `d` with `0 ≤ d ≤ pre + post`, and
rates `r1 ≤ r2` on the earlier and later gains:
* **HMRC's order never costs more.** Setting `d` against `post` first gives no more tax than any other split of `d`.
* **Nothing is lost or counted twice.** The taxable amounts after the split add up to `pre + post - d`.
-/

namespace Kanon.UkRateChange

/-- The tax when `a` of the deductions `d` go against the later gains and the rest against the earlier ones. -/
def tax (pre post d a r1 r2 : ℚ) : ℚ := (pre - (d - a)) * r1 + (post - a) * r2

/-- HMRC's order: as much as possible against the later gains. -/
def hmrc (post d : ℚ) : ℚ := min d post

/-- **#52** Setting the deductions against the later gains first never gives more tax than any other split. -/
theorem hmrc_least (pre post d a r1 r2 : ℚ) (hr : r1 ≤ r2) (ha : a ≤ min d post) :
    tax pre post d (hmrc post d) r1 r2 ≤ tax pre post d a r1 r2 := by
  unfold tax hmrc
  nlinarith [mul_le_mul_of_nonneg_right (sub_nonneg.mpr ha) (sub_nonneg.mpr hr)]

/-- **#52** After HMRC's split, the taxable earlier and later gains add up to all the gains less the deductions, and
neither is below zero when `0 ≤ d ≤ pre + post` and the gains are not negative. -/
theorem split_adds_up (pre post d : ℚ) (hpre : 0 ≤ pre) (hpost : 0 ≤ post) (hdp : d ≤ pre + post) :
    (pre - (d - hmrc post d)) + (post - hmrc post d) = pre + post - d ∧
      0 ≤ pre - (d - hmrc post d) ∧ 0 ≤ post - hmrc post d := by
  unfold hmrc
  refine ⟨by ring, ?_, ?_⟩
  · rcases le_total d post with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  · linarith [min_le_right d post]

end Kanon.UkRateChange
