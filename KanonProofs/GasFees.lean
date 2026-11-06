import Mathlib.Tactic

/-!
# Network fees paid in coins (#43)

The money map (`src/lib/money-map/map.ts`, `toEvents`: the swap and fee steps), with each country's rule from its
tax office (`data/official/fees.md` in the app). Paying a network fee in a coin is a disposal of those coins at their
market value in every country covered. What a country allows of the fee's value (`allowed`, any amount from 0: the
app uses the fee's whole value, or 0 in India) goes on the transaction it paid for, here one transaction and its fee:

* **on a swap**: a share of it (`share`) comes off what the coins given up were sold for, never more than that, and the
  rest is added to the cost of what came in. The US, Germany, Brazil, Japan, South Africa and Nigeria put all of it on
  the sale; the UK splits a token-for-token fee 50/50. (South Africa adds it to the base cost of what was given up
  instead, and Japan counts it as an expense of the year's crypto income: the gain, and the year's income, are the
  same.)
* **on a sale for money only** (nothing came in to put a cost on): all of it comes off the sale, up to what the sale
  brought.
* **on a transaction with nothing else in it** (a move between the person's own wallets, an approval, a failed
  transaction): Thailand counts it as a cost, so the fee coins' proceeds are reduced by it; elsewhere it isn't
  allowed.

What was given up is valued at what came in (proof #31), `got` here. Proved, for the coins given up (cost `cost`), the
fee coins (cost `feeCost`, market value `fee`) and what came in, later sold for `later`:

* the fee is never put on the sale beyond what the sale brought, so its proceeds are never below 0;
* over the swap and the later sale of everything that came in, the allowed fee lowers the total gain exactly once,
  whatever the share; the share only decides which sale (and so which tax year) takes it;
* nothing allowed (India): the same as selling the fee coins at market value and deducting nothing;
* a sale for money only: the total is lowered by the fee up to what the sale brought (exactly once when the fee is no
  more than that);
* a purchase with money only: all the allowed fee goes on the cost of what was bought;
* a lone fee in Thailand: only the fee coins' cost is lost; elsewhere their gain is their market value less their cost.

Out of scope here: how the app shares these amounts among several coins on a side (in proportion, in decimals), a fee
an exchange took from the coins it just bought (the app's exchange-fee step, #39), and which wallet paid.
-/

namespace Kanon.GasFees

/-- One swap with a fee paid in coins. `share` is the part of the allowed fee put on the sale. -/
structure Tx where
  cost : ℚ
  got : ℚ
  feeCost : ℚ
  fee : ℚ
  allowed : ℚ
  share : ℚ

/-- What goes on the sale: the share of the allowed fee, never more than what the sale brought (`offSale` in the app). -/
def offSale (t : Tx) : ℚ := min (t.share * t.allowed) t.got

/-- What the sale of the coins given up brings: what came in, less what goes on the sale. -/
def saleProceeds (t : Tx) : ℚ := t.got - offSale t

/-- The cost of what came in: its value, plus the rest of the allowed fee (`onCost` in the app). -/
def boughtCost (t : Tx) : ℚ := t.got + (t.allowed - offSale t)

/-- Gains over the swap, the fee coins (sold at their market value) and the later sale of what came in. -/
def totalGain (t : Tx) (later : ℚ) : ℚ :=
  (saleProceeds t - t.cost) + (t.fee - t.feeCost) + (later - boughtCost t)

/-- **#43** The sale's proceeds are never below 0: no more is put on the sale than it brought. -/
theorem proceeds_nonneg (t : Tx) : 0 ≤ saleProceeds t := by
  unfold saleProceeds offSale; have := min_le_right (t.share * t.allowed) t.got; linarith

/-- **#43** The allowed fee lowers the total gain exactly once, whatever the share (and wherever the cap falls). -/
theorem fee_counted_once (t : Tx) (later : ℚ) :
    totalGain t later = (later - t.cost) + (t.fee - t.feeCost) - t.allowed := by
  unfold totalGain saleProceeds boughtCost; ring

/-- **#43** So the share only moves the fee between the swap and the later sale: over both, the total is the same
(the UK's 50/50 split and the others' all-on-the-sale add up alike). -/
theorem split_same_total (t : Tx) (later s' : ℚ) :
    totalGain t later = totalGain { t with share := s' } later := by
  rw [fee_counted_once, fee_counted_once]

/-- **#43** Nothing allowed (India): the sale keeps its full proceeds, the new coins their value as cost, and the total is
that of the fee coins sold at market value with nothing deducted. -/
theorem nothing_allowed (t : Tx) (later : ℚ) (hg : 0 ≤ t.got) (h : t.allowed = 0) :
    saleProceeds t = t.got ∧ boughtCost t = t.got ∧ totalGain t later = (later - t.cost) + (t.fee - t.feeCost) := by
  have h0 : offSale t = 0 := by unfold offSale; rw [h, mul_zero]; exact min_eq_left hg
  refine ⟨by simp [saleProceeds, h0], by simp [boughtCost, h0, h], by rw [fee_counted_once, h]; ring⟩

/-- A sale for money only (nothing came in): all the allowed fee comes off it, up to what it brought. -/
def moneySaleProceeds (got allowed : ℚ) : ℚ := got - min allowed got

/-- **#43** A sale for money only: never below 0, and the gain is lowered by the fee up to what the sale brought,
exactly by the fee when the fee is no more than that. -/
theorem money_sale (got allowed cost : ℚ) :
    0 ≤ moneySaleProceeds got allowed ∧ moneySaleProceeds got allowed - cost = (got - cost) - min allowed got ∧
      (allowed ≤ got → moneySaleProceeds got allowed - cost = (got - cost) - allowed) := by
  unfold moneySaleProceeds
  refine ⟨by have := min_le_right allowed got; linarith, by ring, fun h => by rw [min_eq_left h]; ring⟩

/-- A purchase with money only (nothing given up but money): nothing to take the fee off, so all of it goes on the cost. -/
def moneyBuyCost (paid allowed : ℚ) : ℚ := paid + allowed

/-- **#43** A purchase with money only: what was bought costs what was paid plus the allowed fee, so its later sale for
`later` gains that much less. -/
theorem money_buy (paid allowed later : ℚ) : later - moneyBuyCost paid allowed = (later - paid) - allowed := by
  unfold moneyBuyCost; ring

/-- The fee coins on a transaction with nothing else in it: their market value, less what the country allows. -/
def loneFeeProceeds (fee allowed : ℚ) : ℚ := fee - allowed

/-- **#43** A lone fee: the fee coins' gain is their market value less their cost, less what the country allows. -/
theorem lone_fee (fee feeCost allowed : ℚ) :
    loneFeeProceeds fee allowed - feeCost = (fee - feeCost) - allowed := by
  unfold loneFeeProceeds; ring

/-- **#43** Thailand (the fee allowed in full): only the fee coins' cost is lost. -/
theorem lone_fee_thailand (fee feeCost : ℚ) : loneFeeProceeds fee fee - feeCost = -feeCost := by
  unfold loneFeeProceeds; ring

/-- **#43** Elsewhere (nothing allowed): the fee coins are sold at their market value. -/
theorem lone_fee_elsewhere (fee feeCost : ℚ) : loneFeeProceeds fee 0 - feeCost = fee - feeCost := by
  unfold loneFeeProceeds; ring

end Kanon.GasFees
