import KanonProofs.Lots
/-!
# Which coins count as sold, per country (#5)

Countries name different rules for which coins a sale uses. The UK's same-day, 30-day and pool rules
are in `UkMatch.lean`. Here:

* **Oldest first (FIFO)**, the default in the US and most countries: only the oldest coins are used,
  and every newer lot is left exactly as it was.
* **Holding period** (Germany's one-year rule; the US long-term / short-term split): each coin sold is
  counted once, as either held long enough or not.
* **Average cost** (Brazil, Japan, South Africa's weighted average): a sale takes its share of the
  pool's cost; what's left keeps the same average, to within one smallest unit of rounding.
-/

namespace Kanon.Matching
open Kanon.Lots

/-- **#5 FIFO** After an oldest-first sale, the lots left are the newest ones in their original order:
a run of the oldest lots is gone, the next one may be partly used, and every newer lot is untouched. -/
theorem fifo_newest_left (ls : List Lot) (q : Nat) :
    ∃ k, (sell ls q).2.2.drop 1 = ls.drop (k + 1) ∧
      ((sell ls q).2.2.map Lot.acquired) = (ls.drop k).map Lot.acquired := by
  induction ls generalizing q with
  | nil => exact ⟨0, by simp [sell], by simp [sell]⟩
  | cons l ls ih =>
    unfold sell
    by_cases h0 : q = 0
    · exact ⟨0, by simp [h0], by simp [h0]⟩
    · by_cases hlt : q < l.qty
      · exact ⟨0, by simp [h0, hlt], by simp [h0, hlt]⟩
      · obtain ⟨k, h1, h2⟩ := ih (q - l.qty)
        refine ⟨k + 1, ?_, ?_⟩
        · simp only [h0, hlt, if_false]; simpa using h1
        · simp only [h0, hlt, if_false]; simpa using h2

/-- Oldest-first sale split by holding period: (coins held over `days`, coins held `days` or less). -/
def sellSplit (today days : Nat) : List Lot → Nat → Nat × Nat
  | [], _ => (0, 0)
  | l :: ls, q =>
    let long := today - l.acquired > days
    if q = 0 then (0, 0)
    else if q < l.qty then (if long then (q, 0) else (0, q))
    else
      let r := sellSplit today days ls (q - l.qty)
      if long then (l.qty + r.1, r.2) else (r.1, l.qty + r.2)

/-- **#5 Holding period** Every coin sold is counted exactly once: held-long plus held-short is what was sold.
(Germany: coins held over a year are tax-free; US: over a year is long-term.) -/
theorem split_total (today days : Nat) (ls : List Lot) (q : Nat) :
    (sellSplit today days ls q).1 + (sellSplit today days ls q).2 = (sell ls q).1 := by
  induction ls generalizing q with
  | nil => simp [sellSplit, sell]
  | cons l ls ih =>
    unfold sellSplit sell
    by_cases h0 : q = 0
    · simp [h0]
    · by_cases hlt : q < l.qty
      · by_cases hl : today - l.acquired > days <;> simp [h0, hlt, hl]
      · have := ih (q - l.qty)
        by_cases hl : today - l.acquired > days <;> simp [h0, hlt, hl] <;> omega

/-- **#5 Holding period** If every lot is old enough, the whole sale is held-long (tax-free in Germany). -/
theorem all_long (today days : Nat) (ls : List Lot) (q : Nat) (h : ∀ l ∈ ls, today - l.acquired > days) :
    (sellSplit today days ls q).2 = 0 := by
  induction ls generalizing q with
  | nil => simp [sellSplit]
  | cons l ls ih =>
    have hl := h l (List.mem_cons_self ..)
    have hr := ih (q - l.qty) (fun m hm => h m (List.mem_cons_of_mem _ hm))
    unfold sellSplit
    by_cases h0 : q = 0
    · simp [h0]
    · by_cases hlt : q < l.qty <;> simp [h0, hlt, hl, hr]

/-- An average-cost pool of one coin. -/
structure Pool where
  qty : Nat
  cost : Nat

/-- Cost a sale of `q` coins takes from the pool: its share, rounded down. -/
def avgTake (p : Pool) (q : Nat) : Nat := p.cost * q / p.qty

def avgSell (p : Pool) (q : Nat) : Pool := ⟨p.qty - q, p.cost - avgTake p q⟩

/-- **#5 Average cost** Cost taken plus cost left is exactly the pool's cost: nothing created or lost. -/
theorem avg_conserves (p : Pool) (q : Nat) (h : q ≤ p.qty) : avgTake p q + (avgSell p q).cost = p.cost := by
  have : avgTake p q ≤ p.cost := by
    unfold avgTake
    rcases Nat.eq_zero_or_pos p.qty with hq | hq
    · simp [hq]
    · exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm p.qty]; exact Nat.mul_le_mul_left _ h)
  simp [avgSell]; omega

/-- **#5 Average cost** What's left keeps the pool's average price: its cost is the old average times the
coins left, rounded by less than one unit per coin (cost·(n−q) ≤ left·n < cost·(n−q) + n). -/
theorem avg_kept (p : Pool) (q : Nat) (h : q ≤ p.qty) (hn : 0 < p.qty) :
    p.cost * (p.qty - q) ≤ (avgSell p q).cost * p.qty ∧
    (avgSell p q).cost * p.qty < p.cost * (p.qty - q) + p.qty := by
  have hc := avg_conserves p q h
  simp only [avgSell, avgTake] at *
  have lo := Nat.div_mul_le_self (p.cost * q) p.qty
  have hi := Nat.lt_mul_div_succ (p.cost * q) hn
  have e1 : p.cost * (p.qty - q) = p.cost * p.qty - p.cost * q := Nat.mul_sub p.cost p.qty q
  have e2 : (p.cost - p.cost * q / p.qty) * p.qty = p.cost * p.qty - p.cost * q / p.qty * p.qty := Nat.sub_mul _ _ _
  have e3 : p.cost * q ≤ p.cost * p.qty := Nat.mul_le_mul_left _ h
  have e4 : p.qty * (p.cost * q / p.qty + 1) = p.cost * q / p.qty * p.qty + p.qty := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm]
  rw [e1, e2]
  omega

end Kanon.Matching
