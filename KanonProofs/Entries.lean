import Mathlib.Tactic

/-!
# Transactions added by hand, and a fee kept from coins just bought (#39)

**Added by hand** (`src/lib/manual.ts`, `problem` and `manualFile`). A transaction the person types in is read as rows
of an exchange file from an account called "Manual", so every engine treats it like any other. Proved here, for the
rows one entry makes:

* a **buy** brings in the coins and takes out the money paid, fee included: the total plus the fee (the money map
  then values the coins at the money paid, #31);
* a **sale** takes out the coins and brings in the total, with the fee as its own row: what is left is the total less
  the fee, more than 0 (an entry whose fee is not below the total is refused);
* coins **sent** leave with the network fee, paid in the coin itself, as its own row; coins **received** or taken as
  **income** come in, and no money moves;
* an entry the app refuses makes no rows at all. (The model's test is the amounts: coins above 0, a fee not below 0, a
  total above 0 for buys and sales, a sale's fee below its total. The app's other tests, the date, coin and currency,
  are tested there.)

**A fee kept from coins just bought** (`src/lib/money-map/map.ts`, the exchange-fee step). An exchange that keeps part
of the coins it just bought for the person as its fee: only what reached them was bought. The fee row is taken off
those coins instead of selling older coins for nothing (26 CFR 1.1001-7(b)(2)(ii)(B) and its Example 5). Proved: the
coins that arrive are the coins bought less the fee, never below 0 nor above what was bought, and the wallet's change
in that coin over the transaction is what it was with the fee as its own row (simple arithmetic, written out).
-/

namespace Kanon.Entries

inductive Kind | buy | sell | received | sent | income
  deriving DecidableEq

structure Entry where
  kind : Kind
  qty : ℚ
  /-- Total paid or received, in money (buys and sales). -/
  total : ℚ
  /-- 0 when there is none. -/
  fee : ℚ

/-- One row: of the coin or of the money, how much in (+) or out (-), and whether it is a fee or income. -/
structure Row where
  coin : Bool
  amount : ℚ
  fee : Bool := false
  income : Bool := false

/-- When an entry can be used (`problem` returns nothing). -/
def Valid (e : Entry) : Prop :=
  0 < e.qty ∧ 0 ≤ e.fee ∧ ((e.kind = .buy ∨ e.kind = .sell) → 0 < e.total) ∧ (e.kind = .sell → e.fee < e.total)

/-- The rows an entry makes. -/
def rows (e : Entry) : List Row :=
  match e.kind with
  | .buy => [{ coin := true, amount := e.qty }, { coin := false, amount := -(e.total + e.fee) }]
  | .sell => [{ coin := true, amount := -e.qty }, { coin := false, amount := e.total }] ++
      (if 0 < e.fee then [{ coin := false, amount := -e.fee, fee := true }] else [])
  | .sent => [{ coin := true, amount := -e.qty }] ++
      (if 0 < e.fee then [{ coin := true, amount := -e.fee, fee := true }] else [])
  | .received => [{ coin := true, amount := e.qty }]
  | .income => [{ coin := true, amount := e.qty, income := true }]

def rowsOf (es : List Entry) [DecidablePred Valid] : List Row :=
  es.flatMap (fun e => if Valid e then rows e else [])

def coinSum (rs : List Row) : ℚ := ((rs.filter (·.coin)).map Row.amount).sum
def moneySum (rs : List Row) : ℚ := ((rs.filter (fun r => !r.coin)).map Row.amount).sum

/-- **#39 Buy** The coins come in, and the money paid, fee included, goes out: that is what they cost. -/
theorem buy_rows (e : Entry) (h : e.kind = .buy) :
    coinSum (rows e) = e.qty ∧ moneySum (rows e) = -(e.total + e.fee) := by
  simp [rows, h, coinSum, moneySum]

/-- **#39 Sale** The coins go out, and the money that comes in, less the fee, is more than 0. -/
theorem sell_rows (e : Entry) (h : e.kind = .sell) (hv : Valid e) :
    coinSum (rows e) = -e.qty ∧ moneySum (rows e) = e.total - e.fee ∧ 0 < moneySum (rows e) := by
  obtain ⟨_, hf, _, hlt⟩ := hv
  have hlt := hlt h
  by_cases hp : 0 < e.fee
  · simp [rows, h, hp, coinSum, moneySum]; constructor <;> linarith
  · have : e.fee = 0 := by linarith
    simp [rows, h, coinSum, moneySum, this]; linarith

/-- **#39 Sent** The coins and the network fee, paid in the coin, go out; no money moves. -/
theorem sent_rows (e : Entry) (h : e.kind = .sent) (hv : Valid e) :
    coinSum (rows e) = -(e.qty + e.fee) ∧ moneySum (rows e) = 0 := by
  obtain ⟨_, hf, _, _⟩ := hv
  by_cases hp : 0 < e.fee
  · simp [rows, h, hp, coinSum, moneySum]; ring
  · have : e.fee = 0 := by linarith
    simp [rows, h, coinSum, moneySum, this]

/-- **#39 Received, income** The coins come in, and no money moves; income is marked as income. -/
theorem in_rows (e : Entry) (h : e.kind = .received ∨ e.kind = .income) :
    coinSum (rows e) = e.qty ∧ moneySum (rows e) = 0 ∧ ((rows e).any (·.income) ↔ e.kind = .income) := by
  rcases h with h | h <;> simp [rows, h, coinSum, moneySum]

/-- **#39** An entry with a problem makes no rows; the rows of a list of entries are those of its usable entries. -/
theorem invalid_nothing [DecidablePred Valid] (e : Entry) (es : List Entry) (h : ¬ Valid e) :
    rowsOf (e :: es) = rowsOf es := by
  simp [rowsOf, h]

/-! ### A fee kept from coins just bought -/

/-- The coins that reached the wallet: those bought (`got`) less the fee kept from them (`fee`). -/
def arrived (got fee : ℚ) : ℚ := got - fee

/-- **#39 Fee kept** When the fee is no more than the coins bought (the only case the app nets), what arrives is never
below 0, and the wallet's change in that coin over the transaction (`others` being its other rows) is the same as
with the fee as its own row: nothing is created or lost. -/
theorem fee_netted (others got fee : ℚ) (h0 : 0 ≤ fee) (h : fee ≤ got) :
    0 ≤ arrived got fee ∧ arrived got fee ≤ got ∧ others + arrived got fee = others + got + -fee := by
  unfold arrived; refine ⟨by linarith, by linarith, by ring⟩

end Kanon.Entries
