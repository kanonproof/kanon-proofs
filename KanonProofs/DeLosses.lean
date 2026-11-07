import Mathlib.Tactic

/-!
# Germany: private-sale losses across years (#47)

The app's `deLosses` (`src/lib/report/report.ts`; the rule and its sources in the app's `data/official/de-losses.md`):
§ 23 (3) sentences 5, 7 and 8 EStG with § 10d. Each year's own net result from private sales is tested against that
year's limit (€600 to 2023, €1,000 from 2024) before any carried loss (BFH IX R 27/04): under it, the year is tax-free
and no carried loss is used; at or over it, all of it is taxable and a loss carried forward comes off it, never below
0. A loss year's loss goes first to the year before, as far as that year is taxable, and the rest carries forward.

Proved, for one year with result `n`, its limit `lim` (> 0), and the loss carried in `f` (≥ 0):

* a year under its limit (from 0) is tax-free and keeps the carried loss whole;
* a year at or over it uses exactly as much of the carried loss as it can (up to its result), is taxed on what's left,
  never below 0, and carries on the rest;
* a loss year is never taxed; its loss goes back as far as last year's taxable amount allows, the rest forward, and
  back + forward is exactly the loss;
* in every case, the carried loss used plus the carried loss left is the carried loss in, plus this year's loss less
  what went back (nothing lost or invented);
* over a run of years, passed from one to the next as the app's loop does (each year's taxable amount is the next
  year's carry-back target): the carried losses used, plus those carried back, plus what's still carried, are exactly
  the loss carried in plus every year's loss.

Out of scope: the €1 million base of § 10d (only part of a carried loss above it is usable: the app says so), the choice
to drop the carry-back (the app shows the automatic case and says the choice exists), and
which sales are private sales (held a year or less: the lot ledger).
-/

namespace Kanon.DeLosses

/-- One year: last year's taxable amount `prev` (≥ 0). Returns what goes back, what's used of the carried loss, this
year's taxable amount and the loss carried on. -/
structure Step where
  back : ℚ
  used : ℚ
  taxable : ℚ
  forward : ℚ

def year (n lim f prev : ℚ) : Step :=
  if n < 0 then
    let b := min (-n) prev
    ⟨b, 0, 0, f + (-n - b)⟩
  else if lim ≤ n then
    let u := min f n
    ⟨0, u, n - u, f - u⟩
  else ⟨0, 0, 0, f⟩

/-- **#47** Under the limit (from 0): tax-free, nothing used, the carried loss kept whole. -/
theorem under_limit (n lim f prev : ℚ) (h0 : 0 ≤ n) (h : n < lim) :
    year n lim f prev = ⟨0, 0, 0, f⟩ := by
  simp [year, not_lt.mpr h0, not_le.mpr h]

/-- **#47** At or over the limit: uses as much of the carried loss as it can, taxed on the rest, never below 0. -/
theorem over_limit (n lim f prev : ℚ) (hl : 0 < lim) (h : lim ≤ n) :
    let s := year n lim f prev
    s.used = min f n ∧ s.taxable = n - min f n ∧ s.forward = f - min f n ∧ 0 ≤ s.taxable ∧ 0 ≤ s.forward := by
  have hn : ¬ n < 0 := by linarith
  simp only [year, hn, h, if_false, if_true]
  exact ⟨trivial, trivial, trivial, by linarith [min_le_right f n], by linarith [min_le_left f n]⟩

/-- **#47** A loss year: never taxed; its loss goes back as far as last year's taxable amount allows, the rest
forward; back + forward added = the loss. -/
theorem loss_year (n lim f prev : ℚ) (hp : 0 ≤ prev) (h : n < 0) :
    let s := year n lim f prev
    s.taxable = 0 ∧ s.back = min (-n) prev ∧ 0 ≤ s.back ∧ s.back ≤ prev ∧ s.back + (s.forward - f) = -n := by
  simp only [year, h, if_true]
  refine ⟨trivial, trivial, le_min (by linarith) hp, min_le_right _ _, by ring⟩

/-- **#47** Nothing lost or invented: the carried loss used plus what's carried on is what was carried in, plus this
year's loss less what went back. -/
theorem conserves (n lim f prev : ℚ) :
    let s := year n lim f prev
    s.used + s.forward = f + (max (-n) 0 - s.back) := by
  unfold year
  split_ifs with h1 h2
  · simp only; rw [max_eq_left (by linarith)]; ring
  · simp only; rw [max_eq_right (by linarith)]; ring
  · simp only; rw [max_eq_right (by linarith)]; ring

/-- A run of years, oldest first, each with its result and its limit (a year with no sales is a result of 0): the
carried loss and the year before's taxable amount pass from one year to the next, as in the app's loop. Returns the
carried losses used, the losses carried back, and the loss still carried at the end. -/
def run : List (ℚ × ℚ) → ℚ → ℚ → ℚ × ℚ × ℚ
  | [], f, _ => (0, 0, f)
  | (n, lim) :: rest, f, prev =>
    let s := year n lim f prev
    let r := run rest s.forward s.taxable
    (s.used + r.1, s.back + r.2.1, r.2.2)

/-- **#47** Over a run of years: the carried losses used, plus the losses carried back, plus the loss still carried at
the end, are exactly the loss carried in plus every year's loss. Nothing is used twice or lost. -/
theorem run_conserves : ∀ (ys : List (ℚ × ℚ)) (f prev : ℚ),
    (run ys f prev).1 + (run ys f prev).2.1 + (run ys f prev).2.2 = f + (ys.map (fun y => max (-y.1) 0)).sum
  | [], f, prev => by simp [run]
  | (n, lim) :: rest, f, prev => by
    have ih := run_conserves rest (year n lim f prev).forward (year n lim f prev).taxable
    have hy := conserves n lim f prev
    simp only [run, List.map_cons, List.sum_cons] at *
    linarith

end Kanon.DeLosses
