import Mathlib.Tactic
import Mathlib.Data.Rat.Defs

/-!
# A bridge move between two average-cost pools (#35)

#34 says what a coin crossing a chain's own bridge under another name must keep in the lot ledger. Countries that
tax from a running average (Brazil's custo médio, the UK's section 104 pool, Japan's moving average, South Africa's
weighted average) hold no lots: each coin's name has one pool, a quantity and what it cost. The move then takes coins
out of the pool of the old name, at that pool's average cost, and adds them to the pool of the new name.

Proved here for a model of that move in exact fractions: no cost is created or lost, the coins left behind keep
their average, the coins that moved carry it with them, and neither pool can go below zero. Where the history shows
more coins moving than were ever seen bought, the pool gives all it has and the rest arrives costing nothing: the
missing purchase is not invented.

What this is and is not. It is the arithmetic of the move for a pool that holds coins and a move of a positive
amount, the case the app's Brazil, UK-pool, South Africa weighted-average, and Japan and Thailand moving-average
engines all compute the same way. It is not a proof about the TypeScript itself: the app works in 40-digit decimals,
so its results can differ from these fractions in the last digit. Not covered: Japan's total-average method (the
year's average is worked out once for the whole year, so a move there is valued differently), pools the history
shows as negative, and the order of buys, moves and sales within one day. Those are tested in the app.
-/

namespace Kanon.PoolMove

/-- A cost pool: how many coins, and what they cost in total. -/
structure Pool where
  qty : ℚ
  cost : ℚ

/-- Coins that really leave the source: what was asked for, or all it holds if it holds less. -/
def taken (src : Pool) (q : ℚ) : ℚ := min q src.qty

/-- The cost that travels with them: their share of the pool's cost. -/
def carried (src : Pool) (q : ℚ) : ℚ := if src.qty = 0 then 0 else src.cost * taken src q / src.qty

/-- The source after the move. -/
def left (src : Pool) (q : ℚ) : Pool := { qty := src.qty - taken src q, cost := src.cost - carried src q }

/-- The destination after the move: all `q` coins arrive, with the carried cost. -/
def arrived (src dst : Pool) (q : ℚ) : Pool := { qty := dst.qty + q, cost := dst.cost + carried src q }

/-- **#35** No cost is created or lost by the move, whatever the amounts. -/
theorem cost_conserved (src dst : Pool) (q : ℚ) :
    (left src q).cost + (arrived src dst q).cost = src.cost + dst.cost := by
  simp only [left, arrived]; ring

/-- **#35** When the source holds the coins, none are created or lost either. -/
theorem qty_conserved (src dst : Pool) (q : ℚ) (hq : q ≤ src.qty) :
    (left src q).qty + (arrived src dst q).qty = src.qty + dst.qty := by
  simp only [left, arrived, taken, min_eq_left hq]; ring

/-- **#35** The coins that moved carry the source's average cost, to the last unit. -/
theorem carried_at_average (src : Pool) (q : ℚ) (hpos : 0 < src.qty) (_h0 : 0 < q) (hq : q ≤ src.qty) :
    carried src q = q * (src.cost / src.qty) := by
  simp only [carried, taken, min_eq_left hq, if_neg (ne_of_gt hpos)]; ring

/-- **#35** The coins left behind in the source keep the average they had. (The destination's average is the blend of
what it held and what arrived.) -/
theorem average_kept (src : Pool) (q : ℚ) (hpos : 0 < src.qty) (_h0 : 0 < q) (hq : q < src.qty) :
    (left src q).cost / (left src q).qty = src.cost / src.qty := by
  have h1 : src.qty ≠ 0 := ne_of_gt hpos
  have h2 : src.qty - q ≠ 0 := by linarith [sub_pos.mpr hq] |> ne_of_gt
  simp only [left, carried, taken, min_eq_left (le_of_lt hq), if_neg h1]
  field_simp

/-- **#35** Moving everything empties the source and carries its whole cost. -/
theorem whole_pool (src : Pool) (q : ℚ) (hpos : 0 < src.qty) (hq : src.qty ≤ q) :
    (left src q).qty = 0 ∧ (left src q).cost = 0 ∧ carried src q = src.cost := by
  have h1 : src.qty ≠ 0 := ne_of_gt hpos
  have hc : carried src q = src.cost := by
    simp only [carried, taken, min_eq_right hq, if_neg h1]; field_simp
  refine ⟨by simp [left, taken, min_eq_right hq], by simp [left, hc], hc⟩

/-- **#35** More coins moving than were ever seen bought: the excess arrives costing nothing. The destination gains
exactly what the source had, never an invented purchase. -/
theorem excess_costs_nothing (src dst : Pool) (q : ℚ) (hpos : 0 < src.qty) (hq : src.qty ≤ q) :
    (arrived src dst q).cost = dst.cost + src.cost ∧ (arrived src dst q).qty = dst.qty + q := by
  obtain ⟨_, _, hc⟩ := whole_pool src q hpos hq
  exact ⟨by simp [arrived, hc], rfl⟩

/-- **#35** An empty source gives nothing: the coins arrive, no cost arrives with them, and the source's books stay
as they were. -/
theorem empty_source (src dst : Pool) (q : ℚ) (h0 : src.qty = 0) :
    (arrived src dst q).qty = dst.qty + q ∧ (arrived src dst q).cost = dst.cost ∧ (left src q).cost = src.cost := by
  simp [arrived, left, carried, h0]

/-- **#35** The source never goes below zero, in coins or in cost, and what it gives is never negative. -/
theorem never_negative (src : Pool) (q : ℚ) (hqty : 0 ≤ src.qty) (hcost : 0 ≤ src.cost) (hq : 0 ≤ q) :
    0 ≤ (left src q).qty ∧ 0 ≤ carried src q ∧ 0 ≤ (left src q).cost := by
  have ht0 : 0 ≤ taken src q := le_min hq hqty
  have ht1 : taken src q ≤ src.qty := min_le_right _ _
  refine ⟨by simp only [left]; linarith, ?_, ?_⟩
  · by_cases h : src.qty = 0
    · simp [carried, h]
    · simp only [carried, if_neg h]; positivity
  · by_cases h : src.qty = 0
    · simp [left, carried, h, hcost]
    · have hp : 0 < src.qty := lt_of_le_of_ne hqty (Ne.symm h)
      simp only [left, carried, if_neg h]
      have : src.cost * taken src q / src.qty ≤ src.cost := by
        rw [div_le_iff₀ hp]; nlinarith
      linarith

/-- **#35** Nor does the destination: it only ever gains coins and cost. -/
theorem destination_never_negative (src dst : Pool) (q : ℚ) (hqty : 0 ≤ src.qty) (hcost : 0 ≤ src.cost) (hq : 0 ≤ q)
    (hdq : 0 ≤ dst.qty) (hdc : 0 ≤ dst.cost) :
    dst.qty ≤ (arrived src dst q).qty ∧ dst.cost ≤ (arrived src dst q).cost ∧ 0 ≤ (arrived src dst q).qty ∧ 0 ≤ (arrived src dst q).cost := by
  obtain ⟨_, hc, _⟩ := never_negative src q hqty hcost hq
  simp only [arrived]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **#35** Moving makes no gain of its own: sell everything in both pools afterwards, for whatever price, and the
gain is what it would have been had nothing moved. (Selling only part of a destination that already held coins uses
its blended average, so the gain can fall in a different sale; the total over all sales is the same.) -/
theorem no_gain_from_moving (src dst : Pool) (q proceeds : ℚ) :
    proceeds - ((left src q).cost + (arrived src dst q).cost) = proceeds - (src.cost + dst.cost) := by
  rw [cost_conserved]

end Kanon.PoolMove
