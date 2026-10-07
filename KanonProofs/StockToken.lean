/-!
# Stock Token value (#29)

A Robinhood Stock Token stands for some number of shares: its multiplier (Robinhood's `uiMultiplier()`, scaled by
10^18). Dividends and splits change the multiplier, never the number of tokens you hold. A token's own price (the
Chainlink feed, and what My money values it at) is the share price × the multiplier.

Whole units, so every equation is exact: the balance in the token's smallest unit, the share price in cents, the
multiplier in its 10^18 scale. Shown here: valuing by the token's own price is the same as tokens × share price ×
multiplier; and when the multiplier rises (a dividend), the value added is exactly the extra shares at the share
price, nothing more and nothing less, and it is nothing when the multiplier doesn't change.
-/

namespace Kanon.StockToken

/-- A token's own price: the share price × shares per token. -/
def feedPrice (sharePrice multiplier : Nat) : Nat := sharePrice * multiplier

/-- What a balance is worth: tokens × share price × shares per token. -/
def value (balance sharePrice multiplier : Nat) : Nat := balance * sharePrice * multiplier

/-- Shares a balance stands for. -/
def shares (balance multiplier : Nat) : Nat := balance * multiplier

/-- The value a multiplier rise adds: the extra shares at the share price. -/
def added (balance sharePrice before after : Nat) : Nat := sharePrice * (shares balance after - shares balance before)

/-- **#29** Valuing a balance by the token's own price is the same as tokens × share price × multiplier. -/
theorem value_by_feed (b p m : Nat) : b * feedPrice p m = value b p m := by
  unfold feedPrice value; rw [Nat.mul_assoc]

/-- **#29** A multiplier rise adds exactly the extra shares at the share price: the value after is the value before
plus that, nothing lost or invented. -/
theorem rise_adds_exactly (b p m m' : Nat) (h : m ≤ m') : value b p m' = value b p m + added b p m m' := by
  unfold value added shares
  have hs : b * m ≤ b * m' := Nat.mul_le_mul_left b h
  rw [Nat.mul_sub, Nat.mul_comm b p]
  have : p * (b * m) ≤ p * (b * m') := Nat.mul_le_mul_left p hs
  rw [Nat.mul_assoc p b m, Nat.mul_assoc p b m'] at *
  omega

/-- **#29** No multiplier change, nothing added. -/
theorem no_change_nothing_added (b p m : Nat) : added b p m m = 0 := by
  simp [added]

/-- **#29** Holding tokens at a positive price, a real rise always adds something. -/
theorem rise_adds_something (b p m m' : Nat) (hb : 0 < b) (hp : 0 < p) (h : m < m') : 0 < added b p m m' := by
  unfold added shares
  have : b * m < b * m' := Nat.mul_lt_mul_of_pos_left h hb
  exact Nat.mul_pos hp (by omega)

/-- **#29** The number of tokens never changes with the multiplier: a balance's shares grow exactly with it. -/
theorem shares_grow_with_multiplier (b m m' : Nat) (h : m ≤ m') : shares b m ≤ shares b m' :=
  Nat.mul_le_mul_left b h

end Kanon.StockToken
