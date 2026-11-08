import Mathlib.Tactic

/-!
# Coins that arrive as another coin, counted in that coin (#55)

When coins are put into a vault (or otherwise become another token), the coins that arrive are counted in the token
they arrive as: `t` coins in become `a` shares (`toQty`), and they carry exactly the cost `c` the coins had. The pooled
engines (the UK, Brazil, Japan) add `a` shares and `c` to the share's pool; the lot engines (South Africa, Thailand)
move each lot with its cost and its quantity times `a / t` (`src/lib/engine/{gb,br,jp,za,th}.ts`). Proved below, for
`t, a > 0` and `0 ≤ c`:

* **Selling `k` of the `a` shares costs `k / a` of `c`**: nothing for none, all of `c` for all, never more than `c`,
  and selling in parts costs the same as at once.
* **Lot by lot, scaling each lot's quantity by `a / t` turns the coins' quantities into exactly the `a` shares.**

Not proved here, and said so: that no cost is made or lost by the move (how the engines are written, carrying `c` as
it is; Japan's total average costs what arrives at the source coin's average for the year instead); Japan's
total-average solver with coins counted in two units; and rounding: these are exact numbers, and the app gets exactly
the `a` shares by letting the last lot take what is left (`src/lib/engine/scale.ts`), which the tests check.
-/

namespace Kanon.MoveUnits

open Finset BigOperators

/-- The cost of `k` of the `a` shares that arrived carrying cost `c`. -/
def shareCost (c a k : ℚ) : ℚ := c * (k / a)

/-- **#55** Selling none costs nothing, selling all `a` shares costs exactly `c`, and any `0 ≤ k ≤ a` costs between. -/
theorem share_cost_bounds (c a k : ℚ) (hc : 0 ≤ c) (ha : 0 < a) (hk0 : 0 ≤ k) (hka : k ≤ a) :
    shareCost c a 0 = 0 ∧ shareCost c a a = c ∧ 0 ≤ shareCost c a k ∧ shareCost c a k ≤ c := by
  unfold shareCost
  refine ⟨by simp, by rw [div_self (ne_of_gt ha), mul_one], mul_nonneg hc (div_nonneg hk0 (le_of_lt ha)), ?_⟩
  have : k / a ≤ 1 := (div_le_one ha).mpr hka
  nlinarith [div_nonneg hk0 (le_of_lt ha)]

/-- **#55** Selling the shares in parts, as the engines do (the second part from what is left: `a − k` shares costing
`c − shareCost c a k`), costs the same in total as selling them at once. -/
theorem share_cost_additive (c a k l : ℚ) (ha : 0 < a) (hk : k < a) :
    shareCost c a k + shareCost (c - shareCost c a k) (a - k) l = shareCost c a (k + l) := by
  unfold shareCost
  have h : a - k ≠ 0 := sub_ne_zero.mpr (ne_of_gt hk)
  have h' : a ≠ 0 := ne_of_gt ha
  field_simp

/-- **#55** Lot by lot: scaling each lot's quantity by `a / t` (the `t` coins put in being the lots' quantities) gives
exactly the `a` shares that arrived. (Each lot keeps its own cost, unchanged by the move.) -/
theorem lots_scale {n : ℕ} (q : Fin n → ℚ) (a : ℚ) (ht : 0 < ∑ i, q i) :
    (∑ i, q i * (a / ∑ j, q j)) = a := by
  rw [← Finset.sum_mul, mul_div_assoc', mul_comm, mul_div_assoc, div_self (ne_of_gt ht), mul_one]

end Kanon.MoveUnits
