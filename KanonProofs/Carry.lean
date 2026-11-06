import Mathlib.Tactic

/-!
# Losses carried into later years: US and UK (#45)

The app's reports (`src/lib/report/report.ts`): the US report chains Schedule D year by year (`netGains` in
`src/lib/engine/us.ts`), the UK report chains the losses brought forward (`gbTax` in `src/lib/engine/gb.ts`). South
Africa's assessed loss is #9 (`zaYear`).

**US** (Schedule D and its carryover worksheet, IRC §1211(b), §1212(b)): the year's net result plus the loss carried in;
a net loss comes off other income up to a limit ($3,000; $1,500 married filing separately), the rest carries to the
next year, also through a year with no sales. Modelled on the total (the app also keeps short and long term apart),
assuming the loss taken each year is all used against other income (enough of it) and that these are the person's only
capital gains and losses (the app says both).

**UK** (TCGA 1992 s2(2), s3(5A)): the year's losses come off its gains in full; losses brought forward only bring the
gain down to the tax-free amount (the Annual Exempt Amount); what isn't used, and a net loss this year, carries on.
Again the person's only gains (others share the tax-free amount: the app says so).

Proved:

* US: exactly the net loss, up to the limit, is taken off other income and exactly the rest carries on (never below 0,
  never above the limit); a year with a gain takes and carries nothing;
  over a run of years, every loss is used up or still carried, and nothing more.
* UK: losses brought forward are used exactly down to the tax-free amount, never more than there are; the taxable gain
  is what is left above it; used plus carried on is exactly what was brought plus this year's net loss.
-/

namespace Kanon.Carry

/-! ## United States -/

/-- One year: the year's net result `r`, the loss carried in `c` (≥ 0), the limit `lim` (≥ 0). -/
structure UsStep where
  /-- Net after the carryover. -/
  net : ℚ
  /-- Taken off other income this year. -/
  deducted : ℚ
  /-- Carried to next year. -/
  carried : ℚ

def usYear (r c lim : ℚ) : UsStep :=
  let net := r - c
  if net < 0 then ⟨net, min (-net) lim, -net - min (-net) lim⟩ else ⟨net, 0, 0⟩

/-- **#45** US, one year: exactly the net loss (the result less the loss carried in), up to the limit, is taken off
other income, and exactly the rest carries on; a year with a net gain takes and carries nothing. Taken is never below 0
nor above the limit. -/
theorem us_year (r c lim : ℚ) (hl : 0 ≤ lim) :
    let s := usYear r c lim
    s.deducted = min (max (c - r) 0) lim ∧ s.carried = max (c - r) 0 - s.deducted ∧ 0 ≤ s.deducted ∧ s.deducted ≤ lim ∧
      0 ≤ s.carried := by
  simp only [usYear]
  split_ifs with h
  · have hm : max (c - r) 0 = -(r - c) := by rw [max_eq_left (by linarith)]; ring
    refine ⟨by rw [hm], by rw [hm], le_min (by linarith) hl, min_le_right _ _, by linarith [min_le_left (-(r - c)) lim]⟩
  · push_neg at h
    have hm : max (c - r) 0 = 0 := max_eq_right (by linarith)
    simp [hm, hl]

/-- What the year's gain absorbed of the loss carried in. -/
def absorbed (r c : ℚ) : ℚ := min (max r 0) c

/-- **#45** US, one year: the loss carried in plus this year's loss is exactly what the year's gain absorbed, what was
taken off other income and what carries on. -/
theorem us_year_conserves (r c lim : ℚ) (hc : 0 ≤ c) :
    c + max (-r) 0 = absorbed r c + (usYear r c lim).deducted + (usYear r c lim).carried := by
  simp only [usYear, absorbed]
  split_ifs with h
  · simp only
    rcases le_total r 0 with hr | hr
    · rw [max_eq_left (by linarith : 0 ≤ -r), max_eq_right hr, min_eq_left hc]; ring
    · rw [max_eq_right (by linarith : -r ≤ 0), max_eq_left hr, min_eq_left (by linarith)]; ring
  · push_neg at h
    rw [max_eq_right (by linarith : -r ≤ 0), max_eq_left (by linarith : (0:ℚ) ≤ r), min_eq_right (by linarith)]; simp

/-- A run of years (a year with no sales is a result of 0), the loss carried from each into the next: in all, what the
gains absorbed, what was taken off other income, and what is still carried at the end. -/
def usRun (lim : ℚ) : List ℚ → ℚ → ℚ × ℚ × ℚ
  | [], c => (0, 0, c)
  | r :: rs, c =>
    let s := usYear r c lim
    let rest := usRun lim rs s.carried
    (absorbed r c + rest.1, s.deducted + rest.2.1, rest.2.2)

/-- **#45** US, over a run of years: every loss (with what was carried in) is absorbed by a gain, taken off other
income, or still carried at the end. Nothing is lost or invented. -/
theorem us_run (lim : ℚ) (hl : 0 ≤ lim) :
    ∀ (rs : List ℚ) (c : ℚ), 0 ≤ c →
      c + (rs.map (fun r => max (-r) 0)).sum = (usRun lim rs c).1 + (usRun lim rs c).2.1 + (usRun lim rs c).2.2
  | [], c, _ => by simp [usRun]
  | r :: rs, c, hc => by
    have hcar : 0 ≤ (usYear r c lim).carried := (us_year r c lim hl).2.2.2.2
    have ih := us_run lim hl rs _ hcar
    have hy := us_year_conserves r c lim hc
    simp only [usRun, List.map_cons, List.sum_cons]
    linarith

/-! ## United Kingdom -/

/-- One year: gains `g` and losses `l` (each ≥ 0), losses brought forward `bf` (≥ 0), the tax-free amount `a` (≥ 0). -/
structure GbStep where
  used : ℚ
  carried : ℚ
  taxable : ℚ

def gbYear (g l bf a : ℚ) : GbStep :=
  let net := g - l
  let used := if a < net then min bf (net - a) else 0
  let after := net - used
  ⟨used, bf - used + max (-after) 0, max (after - a) 0⟩

/-- **#45** UK: losses brought forward are used exactly down to the tax-free amount (all that's needed to bring the gain
there, never more than there are); the taxable gain is what is left above the tax-free amount; used + carried = brought
forward + this year's net loss. -/
theorem gb_year (g l bf a : ℚ) (hbf : 0 ≤ bf) (ha : 0 ≤ a) :
    let s := gbYear g l bf a
    s.used = min bf (max (g - l - a) 0) ∧ s.taxable = max (g - l - s.used - a) 0 ∧
      s.used + s.carried = bf + max (-(g - l)) 0 ∧ 0 ≤ s.used ∧ s.used ≤ bf := by
  simp only [gbYear]
  split_ifs with h
  · have hm : max (g - l - a) 0 = g - l - a := max_eq_left (by linarith)
    have h1 : min bf (g - l - a) ≤ g - l - a := min_le_right _ _
    refine ⟨by rw [hm], trivial, ?_, le_min hbf (by linarith), min_le_left _ _⟩
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]; ring
  · push_neg at h
    have hm : max (g - l - a) 0 = 0 := max_eq_right (by linarith)
    refine ⟨by rw [hm, min_eq_right hbf], trivial, by simp, le_refl _, hbf⟩

end Kanon.Carry
