import Mathlib.Tactic

/-!
# Italy: crypto gains of a private person, TUIR art. 67 c. 1 c-sexies and 68 c. 9-bis (quadro RT, quadro RW)

The app's engine `src/lib/engine/it.ts` (`itRun`, `itYears`, `itYearBase`, `itSplit`, `itYearTax`, `itTaxOnSale`,
`itRate`, `itEuros`, `itEarlierIn`, `itEuroConfirmed`, `itIvca`, `itIvcaDue`, `itWorkingDay`, `itDeadlines`), the swap
branch of the classifier `itBook` with `splitMixed` and `isEuroEmt`, and the IVCA sum of `itRw` in
`src/lib/report/it.ts`, and `itReport`'s readings of the pending euro tokens, the years as shown and `now`, at
kanon-app commit 7583be0 (branch claude/italy-32). Sources: TUIR art. 67 c. 1 c-sexies and 68 cc. 5 and 9-bis (L. 197/2022 art. 1
cc. 126-127); L. 207/2024 art. 1 cc. 24-25 (33% from 2026; no €2,000 threshold from 2025); L. 199/2025 art. 1 c. 28
(euro e-money tokens); Agenzia delle Entrate, Circolare 30/E of 27 October 2023 (§§ 3.2.1, 3.3-3.4, pp. 47-48, 51,
55); DL 201/2011 art. 19 c. 18-bis (IVCA, 0.2%); Modello Redditi PF (RT57, RT88-89, RW col. 1-5 and 33, RW8); DPR
435/2001 art. 17; DPR 322/1998 art. 2; DL 70/2011 art. 7 c. 2 l; DL 16/2012 art. 3-quater.

Modelled, in exact fractions where the app uses decimal.js:

* `itRun` (rules 1-4): `take` is its last-in-first-out `take` (the newest lot at the head of the list here, at the end
  of the app's array), `takeAll` its loop over the coins given, `step` its handling of one operation (buy, provento,
  drop, sale or exchange, untaxed swap with the cost split by value or equally), `run` the loop. The app sorts ops by
  time, then kind (buy, provento, swap, sale or part swap, drop; engine/it.ts:98), then the order made; for the ops of one happening (one time)
  that is `byKind`, the filters by kind put end to end. Across times the sort is not modelled.
* `itBook` for a swap happening (`classify`, rules 2-3 and 10): bought with money, sold for money, euro e-money tokens
  redeemed for euros from 2026, untaxed swap of one kind (coins, e-money tokens or NFTs), `splitMixed` for legs of
  more than one kind with no money (Case A: all received of one kind; Case B: all given of one kind; both sides mixed:
  the whole swap is taxed; Case B is one part swap of every coin given, `ItPartSwap`, engine/it.ts:78 and 150-156,
  report/it.ts:319-336), and the taxable exchange (with an NFT and no money, an unpriced side is taken at the other
  side's value). Its other happenings (fees merged one line a day, bridges, proventi, answers, futures) are not
  modelled; a provento's line and lot are `step`'s.
* The euro e-money token rule (`isEuro`, `euroIn`): a token of the issuers' euro set that is not pending (EURCV, EURR)
  always counts; a pending one (`IT_EURO_PENDING`: EURC, EURI, EURQ) counts for a movement only on or after the day
  of a reserve statement for it; EURe and any other coin never. Statements are an abstract list of (token, day), days
  as natural numbers in calendar order (the app's Rome yyyy-mm-dd strings compare the same way); the app keeps one per
  token, a list allows more. Whether a link or title is accepted, and the date it gets (`itEuroOne`, `itEuroLink`,
  `itEuroKnownPage`), are not modelled.
* `itYearBase` and `itYears` (rules 5-8): the net in whole euros, the €2,000 threshold to 2024, the losses on hand
  sorted by year (`sortPool`, a stable sort) and used oldest first within four years (`use`), the residues kept and
  the losses that expire (engine/it.ts:306-341); earlier losses of 2019-2022 (`earlierIn`). The tax (`itSplit`,
  engine/it.ts:369-381, rule 9): to 2025, or with a base not above 0, 26% of the base; from 2026 26% of the whole-euro
  base (RT88) and 7% more on the part at 33% (`other33`): the base before the net was rounded (`exactBase`, the base
  plus the net less the net in whole euros) times the other gain over all the gains (each not below 0), never above
  the base, not rounded; the tax rounded up to the cent (`tax`) and to whole euros 50 cents up (`form`, RT89); the parts
  shown in whole euros (`atOther`, the rest at 26%). `itYearTax` and `itTaxOnSale` (engine/it.ts:386-398, rule 15). Years before 2023
  (no rate) are not modelled.
* The readings (rule 16): `itBook`'s readings (report/it.ts:212-229) take each set of the pending tokens no statement
  covers as euro e-money tokens on every day (`assumed_every_day`); `itReport` (report/it.ts:496-536) runs each, and
  each year starts from the common start (`common`: for each year the losses came from, the least of every reading's
  own pool and last year as shown) and shows the reading the reduce picks (`pickN`: higher tax, then fewer losses
  left, then the first); `now` takes the highest net, the losses carried in as shown and the picked reading's euro
  e-money token net. A reading is given by its years: each year's net and euro e-money token net from its own lines
  (`Reading`); how its lines come from the ops is the rest of this file.
* `itEuros` (half away from zero, decimal.js ROUND_HALF_UP) and `centsUp` (rule 11).
* `itIvca`, the per-account rounding and sum in `itRw`, and `itIvcaDue` (rule 12, RW col. 5 from cols. 1-4), with
  every price known (the app shows no total when a price is missing).
* The IVCA instalments (rule 13) are not computed by the app: they are only said in the report's note (`ReportPdf.tsx`,
  quadro RW). `instalments` models that sentence.
* `itWorkingDay` and `itDeadlines` (rule 14) on day numbers (days from 1 January 1970, the proleptic Gregorian
  calendar), with the holidays as a parameter (`appHol` is the app's fixed list) and the search for a working day
  bounded by 30 days (the app's loop has no bound). The 0.4% for paying late is only said in the app's text.

Departures and what is out of scope:

* The readings: the app's `null` tax branch of the pick is dropped (`itRate` never returns null, so no tax is null);
  the losses' order in a pool and the `origins` sort are not relied on (only the amounts by year); `seen`, the years
  listed, `count`, `carryMixed`, `euroAt33` and which tokens are pending are not modelled; `m ≥ 1` readings are
  numbered from 0 (the reading that assumes none); `Math.min(...)` over no pools (never called) is 0 here.

* Decimal.js precision (40 significant digits): a division such as cost × left ÷ qty, or `vGot ÷ vAll`, is rounded
  there and exact here.
* Quantities here are the amounts without their sign and values are given per leg; the app takes `|amount × f|` and
  `usd × |amount|`. The same for quantities and values not below 0.
* `itYears` keeps the residues in the order of the pool it was given (with the amounts the sorted copy used up); here
  in the sorted order. The same losses and amounts; the order is the same whenever the pool is already in year order,
  as the app's pool is (`earlierIn`, then one loss a year appended).
* Flags, NFT and protocol-stable counts, the exchanges seen, `euroPending` and the report's text are not modelled; nor
  the "sold" answer for a euro e-money token, the harvest finder and the exit planner, the euro conversion and prices,
  `itHoldings`, `itLotsFor`, and how answers and other happenings become ops. Years and days are natural numbers.

D.Lgs. 117/2026 re-enacts the 33% and the euro e-money token rule from 2027 (art. 304 c. 7, same text).
-/


namespace Kanon.Italy

/-! ## Rounding (`itEuros`, `centsUp`) -/

/-- `itEuros`: whole euros, half away from zero (decimal.js ROUND_HALF_UP). -/
def euros (x : ℚ) : ℤ := if 0 ≤ x then ⌊x + 1 / 2⌋ else -⌊-x + 1 / 2⌋

/-- `centsUp`: up to the cent. -/
def centsUp (x : ℚ) : ℚ := (⌈x * 100⌉ : ℚ) / 100

/-! ## The lots: `itRun`'s `take` (rule 4, Circolare 30/E p. 55: L.I.F.O.) -/

/-- A lot: coins and their documented cost. -/
structure Lot where
  qty : ℚ
  cost : ℚ
  deriving DecidableEq

def sumQty (s : List Lot) : ℚ := (s.map Lot.qty).sum
def sumCost (s : List Lot) : ℚ := (s.map Lot.cost).sum

/-- `take`: `left` coins off one asset's stack, newest first (the head is the newest lot). Returns the cost taken, the
coins no lot covered (`short`, at nil cost) and the stack left. A lot only partly used keeps the rest at its own cost
per coin. -/
def take : ℚ → List Lot → ℚ × ℚ × List Lot
  | left, [] => (0, left, [])
  | left, l :: s =>
    if left ≤ 0 then (0, left, l :: s)
    else if l.qty ≤ left then
      (l.cost + (take (left - l.qty) s).1, (take (left - l.qty) s).2.1, (take (left - l.qty) s).2.2)
    else (l.cost * left / l.qty, 0, ⟨l.qty - left, l.cost - l.cost * left / l.qty⟩ :: s)

@[simp] theorem sumCost_nil : sumCost [] = 0 := rfl
@[simp] theorem sumCost_cons (l : Lot) (s : List Lot) : sumCost (l :: s) = l.cost + sumCost s := by simp [sumCost]
@[simp] theorem sumQty_nil : sumQty [] = 0 := rfl
@[simp] theorem sumQty_cons (l : Lot) (s : List Lot) : sumQty (l :: s) = l.qty + sumQty s := by simp [sumQty]

/-- **IT-4** Cost is conserved: the cost taken plus the cost still in the stack is the stack's cost before. -/
theorem take_cost (left : ℚ) (s : List Lot) : (take left s).1 + sumCost (take left s).2.2 = sumCost s := by
  induction s generalizing left with
  | nil => simp [take]
  | cons l s ih =>
    simp only [take]
    split_ifs with h0 h1
    · simp
    · have := ih (left - l.qty); simp only [sumCost_cons]; linarith
    · simp only [sumCost_cons]; ring

/-- **IT-4** Coins are conserved: the coins taken (`left − short`) plus the coins still in the stack are the coins
before. -/
theorem take_qty (left : ℚ) (s : List Lot) :
    (left - (take left s).2.1) + sumQty (take left s).2.2 = sumQty s := by
  induction s generalizing left with
  | nil => simp [take]
  | cons l s ih =>
    simp only [take]
    split_ifs with h0 h1
    · simp
    · have := ih (left - l.qty); simp only [sumQty_cons]; linarith
    · simp only [sumQty_cons]; ring

/-- **IT-4** Newest first, older lots untouched: the stack left is the stack with its `n` newest lots used up, or with
them used up and the next lot reduced by `x` coins (0 < x < its coins) at its own cost per coin. Every lot older than
those is exactly as it was. -/
theorem take_newest_first (left : ℚ) (s : List Lot) :
    ∃ n, (take left s).2.2 = s.drop n ∨
      ∃ l k x, s.drop n = l :: k ∧ 0 < x ∧ x < l.qty ∧
        (take left s).2.2 = ⟨l.qty - x, l.cost - l.cost * x / l.qty⟩ :: k := by
  induction s generalizing left with
  | nil => exact ⟨0, Or.inl rfl⟩
  | cons l s ih =>
    simp only [take]
    split_ifs with h0 h1
    · exact ⟨0, Or.inl rfl⟩
    · obtain ⟨n, hn⟩ := ih (left - l.qty)
      exact ⟨n + 1, by simpa using hn⟩
    · exact ⟨0, Or.inr ⟨l, s, left, rfl, lt_of_not_ge h0, lt_of_not_ge h1, rfl⟩⟩

/-- **IT-4** A lot partly used keeps its cost per coin: (cost − cost × x ÷ qty) ÷ (qty − x) = cost ÷ qty. -/
theorem partial_rate (l : Lot) (x : ℚ) (h0 : 0 < x) (hx : x < l.qty) :
    (l.cost - l.cost * x / l.qty) / (l.qty - x) = l.cost / l.qty := by
  have h1 : l.qty - x ≠ 0 := by linarith
  have h2 : l.qty ≠ 0 := by linarith
  rw [div_eq_div_iff h1 h2]
  field_simp

/-- **IT-1** Coins short (no lot, no document) only once every lot of the asset is used: the stack is then empty. -/
theorem short_only_when_empty (left : ℚ) (s : List Lot) (h : 0 < (take left s).2.1) : (take left s).2.2 = [] := by
  induction s generalizing left with
  | nil => rfl
  | cons l s ih =>
    simp only [take] at h ⊢
    split_ifs at h ⊢ with h0 h1
    · simp at h; linarith
    · exact ih _ h
    · simp at h

/-- Lots hold a positive number of coins (buys and swaps push only those; a partly used lot keeps a positive rest). -/
def Pos (s : List Lot) : Prop := ∀ l ∈ s, 0 < l.qty

/-- **IT-4** Never more than asked: for `left ≥ 0` the coins short are between 0 and `left`, and the stack left still
holds positive lots. -/
theorem take_short_bounds (left : ℚ) (s : List Lot) (hl : 0 ≤ left) (hp : Pos s) :
    0 ≤ (take left s).2.1 ∧ (take left s).2.1 ≤ left ∧ Pos (take left s).2.2 := by
  induction s generalizing left with
  | nil => simp [take, hl, Pos]
  | cons l s ih =>
    have hl0 : 0 < l.qty := hp l (by simp)
    have hs : Pos s := fun x hx => hp x (by simp [hx])
    simp only [take]
    split_ifs with h0 h1
    · exact ⟨hl, le_refl _, hp⟩
    · obtain ⟨a, b, c⟩ := ih (left - l.qty) (by linarith) hs
      exact ⟨a, by linarith, c⟩
    · refine ⟨le_refl _, hl, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simp only; linarith [lt_of_not_ge h1]
      · exact hs x hx

/-- **IT-1** No lot (no document): the cost is nil and every coin is short. -/
theorem take_empty (left : ℚ) : take left [] = (0, left, []) := rfl

/-- The LIFO example of the app's tests: lots of 1 coin at 100 and then 1 coin at 300; selling 1.5 coins takes the
newer lot whole and half the older: cost 350, leaving 0.5 coins at 50. -/
theorem lifo_example :
    take (3 / 2) [⟨1, 300⟩, ⟨1, 100⟩] = (350, 0, [⟨1 / 2, 50⟩]) := by
  simp [take]; norm_num

/-! ## The ledger: `itRun` (rules 1-4) -/

/-- Coins given: an asset (numbered) and a quantity. -/
structure Coin where
  asset : ℕ
  qty : ℚ

/-- Coins come in in an untaxed swap: the asset, quantity and value (none: no price). -/
structure Got where
  asset : ℕ
  qty : ℚ
  value : Option ℚ

/-- `ItOp`: a buy at the money paid (no fees added), a provento (taxed in full, a lot at its value), coins gone with no
tax effect, a taxable sale or exchange at `proceeds`, an untaxed swap with money paid on top, and `part` (`ItPartSwap`,
engine/it.ts:78): the coins given leave as one disposal, newest lots first, `part` of what they cost goes on a line at
`proceeds` and the rest of the cost carries to what came in. `euroEmt`: the line is a euro e-money token's (taxed at
26% from 2026, rule 9). -/
inductive Op
  | buy (asset : ℕ) (qty cost : ℚ)
  | income (asset : ℕ) (qty value : ℚ) (euroEmt : Bool)
  | drop (gave : List Coin)
  | dispose (gave : List Coin) (proceeds : ℚ) (euroEmt : Bool)
  | swap (gave : List Coin) (got : List Got) (paid : ℚ)
  | part (gave : List Coin) (part proceeds : ℚ) (euroEmt : Bool) (got : List Got)

inductive Kind
  | sale
  | income
  deriving DecidableEq

/-- `ItLine`: what was received, the documented cost, the gain, the coins short and whether it is a euro e-money
token's. -/
structure Line where
  kind : Kind
  proceeds : ℚ
  cost : ℚ
  gain : ℚ
  short : ℚ
  euroEmt : Bool

/-- Every asset's stack. -/
abbrev Stacks := ℕ → List Lot

/-- Takes each coin given off its asset's stack, in order: the cost taken, the coins short and the stacks left. -/
def takeAll : Stacks → List Coin → ℚ × ℚ × Stacks
  | st, [] => (0, 0, st)
  | st, c :: cs =>
    let t := take c.qty (st c.asset)
    let r := takeAll (Function.update st c.asset t.2.2) cs
    (t.1 + r.1, t.2.1 + r.2.1, r.2.2)

/-- Pushes a lot on top of its asset's stack. -/
def push (st : Stacks) (a : ℕ) (l : Lot) : Stacks := Function.update st a (l :: st a)

/-- Every value known and above 0 (`allValued` in `itRun`, `all` in `itBook`'s `buys`). -/
def allPos (vs : List (Option ℚ)) : Bool := vs.all (fun v => match v with | some x => decide (0 < x) | none => false)

def wt (v : Option ℚ) : ℚ := v.getD 0

/-- A total split by value when every value is known and above 0, else equally. -/
def portion (total : ℚ) (vs : List (Option ℚ)) (v : Option ℚ) : ℚ :=
  if allPos vs then total * wt v / (vs.map wt).sum else total * 1 / vs.length

/-- Pushes each coin that came in as a lot carrying its portion of `cost`. -/
def pushAll (cost : ℚ) (vs : List (Option ℚ)) : Stacks → List Got → Stacks
  | st, [] => st
  | st, g :: gs => pushAll cost vs (push st g.asset ⟨g.qty, portion cost vs g.value⟩) gs

/-- One op of `itRun`: the stacks after it and the line it makes. -/
def step (st : Stacks) : Op → Stacks × Option Line
  | .buy a q c => (if 0 < q then push st a ⟨q, c⟩ else st, none)
  | .income a q v e => (if 0 < q then push st a ⟨q, v⟩ else st, some ⟨.income, v, 0, v, 0, e⟩)
  | .drop gave => ((takeAll st gave).2.2, none)
  | .dispose gave p e =>
    ((takeAll st gave).2.2, some ⟨.sale, p, (takeAll st gave).1, p - (takeAll st gave).1, (takeAll st gave).2.1, e⟩)
  | .swap gave got paid =>
    let g := got.filter (fun x => decide (0 < x.qty))
    if g = [] then ((takeAll st gave).2.2, none)
    else (pushAll (paid + (takeAll st gave).1) (g.map Got.value) (takeAll st gave).2.2 g, none)
  | .part gave f p e got =>
    let g := got.filter (fun x => decide (0 < x.qty))
    (if g = [] then (takeAll st gave).2.2
     else pushAll ((takeAll st gave).1 - (takeAll st gave).1 * f) (g.map Got.value) (takeAll st gave).2.2 g,
     some ⟨.sale, p, (takeAll st gave).1 * f, p - (takeAll st gave).1 * f, (takeAll st gave).2.1 * f, e⟩)

/-- `itRun`: the lines and the stacks after the last op. -/
def run : Stacks → List Op → List Line × Stacks
  | st, [] => ([], st)
  | st, op :: ops => ((step st op).2.toList ++ (run (step st op).1 ops).1, (run (step st op).1 ops).2)

/-- The cost held over a set of assets. -/
def totalCost (A : Finset ℕ) (st : Stacks) : ℚ := ∑ a ∈ A, sumCost (st a)

theorem total_update (A : Finset ℕ) (st : Stacks) (a : ℕ) (s : List Lot) (h : a ∈ A) :
    totalCost A (Function.update st a s) = totalCost A st - sumCost (st a) + sumCost s := by
  unfold totalCost
  rw [← Finset.add_sum_erase A _ h, ← Finset.add_sum_erase A (fun b => sumCost (st b)) h]
  have : ∑ x ∈ A.erase a, sumCost (Function.update st a s x) = ∑ x ∈ A.erase a, sumCost (st x) :=
    Finset.sum_congr rfl (fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)])
  simp only [Function.update_self, this]; ring

/-- **IT-4** Over the assets given, the cost taken plus the cost still held is the cost held before. -/
theorem takeAll_cost (A : Finset ℕ) (st : Stacks) (gave : List Coin) (h : ∀ c ∈ gave, c.asset ∈ A) :
    (takeAll st gave).1 + totalCost A (takeAll st gave).2.2 = totalCost A st := by
  induction gave generalizing st with
  | nil => simp [takeAll]
  | cons c cs ih =>
    simp only [takeAll]
    have h1 := ih (Function.update st c.asset (take c.qty (st c.asset)).2.2) (fun x hx => h x (by simp [hx]))
    have h2 := total_update A st c.asset (take c.qty (st c.asset)).2.2 (h c (by simp))
    have h3 := take_cost c.qty (st c.asset)
    linarith

/-- **IT-1** No document: when no asset given has a lot, the cost taken is nil and every coin given is short. -/
theorem takeAll_no_lots (st : Stacks) (gave : List Coin) (h : ∀ c ∈ gave, st c.asset = []) :
    (takeAll st gave).1 = 0 ∧ (takeAll st gave).2.1 = (gave.map Coin.qty).sum := by
  induction gave generalizing st with
  | nil => simp [takeAll]
  | cons c cs ih =>
    have hc : st c.asset = [] := h c (by simp)
    have hu : Function.update st c.asset (take c.qty (st c.asset)).2.2 = st := by
      rw [hc]; simp only [take]; rw [← hc]; exact Function.update_eq_self _ _
    simp only [takeAll, hu]
    obtain ⟨a, b⟩ := ih st (fun x hx => h x (by simp [hx]))
    rw [hc]; simp [take, a, b]

theorem map_const_sum {α : Type} (l : List α) (c : ℚ) : (l.map fun _ => c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; push_cast; ring

/-- **IT-2** The portions add up to the total exactly (split by value, or equally when a value is missing). -/
theorem portion_sum (total : ℚ) (vs : List (Option ℚ)) (h : vs ≠ []) :
    (vs.map (portion total vs)).sum = total := by
  unfold portion
  by_cases ha : allPos vs = true
  · simp only [ha, if_true]
    have hpos : 0 < (vs.map wt).sum := by
      apply List.sum_pos
      · intro x hx
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
        have := List.all_eq_true.mp ha v hv
        cases v with
        | none => simp at this
        | some y => simpa [wt] using this
      · simpa using h
    have : (vs.map fun v => total * wt v / (vs.map wt).sum) = (vs.map fun v => (total / (vs.map wt).sum) * wt v) := by
      congr 1; funext v; ring
    rw [this, List.sum_map_mul_left]; field_simp
  · simp only [ha, if_false, Bool.false_eq_true]
    rw [map_const_sum]
    have : (vs.length : ℚ) ≠ 0 := by simpa [List.length_eq_zero_iff] using h
    field_simp

theorem pushAll_cost (A : Finset ℕ) (cost : ℚ) (vs : List (Option ℚ)) (st : Stacks) (got : List Got)
    (h : ∀ g ∈ got, g.asset ∈ A) :
    totalCost A (pushAll cost vs st got) = totalCost A st + (got.map fun g => portion cost vs g.value).sum := by
  induction got generalizing st with
  | nil => simp [pushAll]
  | cons g gs ih =>
    simp only [pushAll, List.map_cons, List.sum_cons]
    rw [ih _ (fun x hx => h x (by simp [hx])), push, total_update A st g.asset _ (h g (by simp))]
    simp; ring

/-- **IT-2** An untaxed swap (crypto for crypto of the same kind) makes no line. -/
theorem swap_no_line (st : Stacks) (gave : List Coin) (got : List Got) (paid : ℚ) :
    (step st (.swap gave got paid)).2 = none := by
  simp only [step]; split_ifs <;> rfl

/-- **IT-2** An untaxed swap conserves cost: over the assets involved, the cost held after is the cost held before plus
the money paid on top. The cost of the coins given goes over to the coins that came in (when at least one came in). -/
theorem swap_conserves (A : Finset ℕ) (st : Stacks) (gave : List Coin) (got : List Got) (paid : ℚ)
    (hg : ∀ c ∈ gave, c.asset ∈ A) (hi : ∀ g ∈ got, g.asset ∈ A)
    (hne : got.filter (fun x => decide (0 < x.qty)) ≠ []) :
    totalCost A (step st (.swap gave got paid)).1 = totalCost A st + paid := by
  simp only [step, hne, if_false]
  have h1 := takeAll_cost A st gave hg
  rw [pushAll_cost A _ _ _ _ (fun g hgm => hi g (List.mem_filter.mp hgm).1)]
  have h2 := portion_sum (paid + (takeAll st gave).1) ((got.filter (fun x => decide (0 < x.qty))).map Got.value)
    (by simpa using hne)
  rw [List.map_map] at h2
  have : ((got.filter (fun x => decide (0 < x.qty))).map fun g =>
      portion (paid + (takeAll st gave).1) ((got.filter (fun x => decide (0 < x.qty))).map Got.value) g.value) =
      ((got.filter (fun x => decide (0 < x.qty))).map
        (portion (paid + (takeAll st gave).1) ((got.filter (fun x => decide (0 < x.qty))).map Got.value) ∘ Got.value)) :=
    rfl
  rw [this, h2]; linarith

/-- **IT-1** A sale or taxable exchange: its line is what was received, the documented cost of the coins given (newest
first) and gain = received − cost; nothing else (no fees) comes off. The coins no lot covers are counted as short. -/
theorem dispose_line (st : Stacks) (gave : List Coin) (p : ℚ) (e : Bool) :
    (step st (.dispose gave p e)).2 =
      some ⟨.sale, p, (takeAll st gave).1, p - (takeAll st gave).1, (takeAll st gave).2.1, e⟩ := rfl

/-- **IT-1** No document: with no lot for any coin given, the cost is nil and the gain is everything received. -/
theorem dispose_no_lots (st : Stacks) (gave : List Coin) (p : ℚ) (e : Bool) (h : ∀ c ∈ gave, st c.asset = []) :
    (step st (.dispose gave p e)).2 = some ⟨.sale, p, 0, p, (gave.map Coin.qty).sum, e⟩ := by
  obtain ⟨a, b⟩ := takeAll_no_lots st gave h
  rw [dispose_line, a, b, sub_zero]

/-- **IT-2** A part swap (`ItPartSwap`, engine/it.ts:150-156): the coins given leave as one disposal taken newest lots
first (`takeAll`, `take`), and the line costs `f` of what those lots cost (the coins short likewise `f` of those no lot
covered), at the proceeds given. -/
theorem part_line (st : Stacks) (gave : List Coin) (f p : ℚ) (e : Bool) (got : List Got) :
    (step st (.part gave f p e got)).2 =
      some ⟨.sale, p, (takeAll st gave).1 * f, p - (takeAll st gave).1 * f, (takeAll st gave).2.1 * f, e⟩ := rfl

/-- **IT-2** A part swap conserves cost: over the assets involved, the cost held after is the cost held before less
the line's cost; the rest of what the coins given cost goes to what came in (when something came in). -/
theorem part_conserves (A : Finset ℕ) (st : Stacks) (gave : List Coin) (f p : ℚ) (e : Bool) (got : List Got)
    (hg : ∀ c ∈ gave, c.asset ∈ A) (hi : ∀ g ∈ got, g.asset ∈ A)
    (hne : got.filter (fun x => decide (0 < x.qty)) ≠ []) :
    totalCost A (step st (.part gave f p e got)).1 = totalCost A st - (takeAll st gave).1 * f := by
  simp only [step, hne, if_false]
  have h1 := takeAll_cost A st gave hg
  rw [pushAll_cost A _ _ _ _ (fun g hgm => hi g (List.mem_filter.mp hgm).1)]
  have h2 := portion_sum ((takeAll st gave).1 - (takeAll st gave).1 * f)
    ((got.filter (fun x => decide (0 < x.qty))).map Got.value) (by simpa using hne)
  rw [List.map_map] at h2
  have : ((got.filter (fun x => decide (0 < x.qty))).map fun g =>
      portion ((takeAll st gave).1 - (takeAll st gave).1 * f)
        ((got.filter (fun x => decide (0 < x.qty))).map Got.value) g.value) =
      ((got.filter (fun x => decide (0 < x.qty))).map
        (portion ((takeAll st gave).1 - (takeAll st gave).1 * f)
          ((got.filter (fun x => decide (0 < x.qty))).map Got.value) ∘ Got.value)) := rfl
  rw [this, h2]; linarith

/-- **IT-3** A provento (staking, rewards): taxed in full at its value when received, with no cost; the coins become a
lot costing that value. -/
theorem income_line (st : Stacks) (a : ℕ) (q v : ℚ) (e : Bool) (hq : 0 < q) :
    (step st (.income a q v e)).2 = some ⟨.income, v, 0, v, 0, e⟩ ∧
      ((step st (.income a q v e)).1 a).head? = some ⟨q, v⟩ := by
  simp [step, hq, push]

/-- **IT-1** A buy is a lot at exactly the money paid (no fee is added). -/
theorem buy_lot (st : Stacks) (a : ℕ) (q c : ℚ) (hq : 0 < q) : ((step st (.buy a q c)).1 a).head? = some ⟨q, c⟩ := by
  simp [step, hq, push]

/-- **IT-2** Circolare 30/E § 3.3 (the app's test): 20 BTC bought for €2,000, 5 of them swapped for 10 ETH worth
€40,000: no line, the ETH costs €500 and the 15 BTC left €1,500. -/
theorem circolare_swap :
    let st := (step (fun _ => []) (.buy 0 20 2000)).1
    let r := step st (.swap [⟨0, 5⟩] [⟨1, 10, some 40000⟩] 0)
    r.2 = none ∧ r.1 1 = [⟨10, 500⟩] ∧ r.1 0 = [⟨15, 1500⟩] := by
  simp [step, push, takeAll, take, pushAll, portion, allPos, wt, Function.update]; norm_num

/-! ## The classifier `itBook` for a swap happening (rules 2-3 and 10; Circolare 30/E §§ 3.3-3.4, pp. 47-48) -/

/-- A crypto movement: asset, quantity (the amount without its sign), value in euros (none: no price), whether it is an
NFT, whether it is an e-money token (`isEmt`, never an NFT: a stablecoin tied to one official currency, MiCA art. 3 c. 1
n. 7) and which of the issuers' own euro tokens it is (`euroToken`: by an exchange's listing or the contract), if any. -/
structure Mv where
  asset : ℕ
  qty : ℚ
  value : Option ℚ
  emt : Bool := false
  nft : Bool := false
  tok : Option ℕ := none

/-! ### Euro e-money tokens by day (`isEuroEmt`, `itEuroConfirmed`; L. 199/2025 art. 1 c. 28) -/

/-- The person's reserve statements for pending tokens: (token, the day of the statement's date `from`), days as
naturals (Rome calendar days in order). The checks on the link or title and on the date (`itEuroOne`) are not
modelled: a statement here is one the app kept. -/
abbrev Statements := List (ℕ × ℕ)

/-- `itEuroConfirmed`: a token is covered on `day` when a statement for it is dated that day or earlier. -/
def confirmed (st : Statements) (day : ℕ) (t : ℕ) : Bool := st.any fun s => s.1 == t && decide (s.2 ≤ day)

/-- `isEuroEmt`: one of the issuers' euro tokens that is not pending (`pend` is `IT_EURO_PENDING`: EURC, EURI, EURQ),
or a pending one that is confirmed. EURCV and EURR are euro tokens not pending; a token with no entry (EURe, any other
coin) is never one. -/
def isEuro (pend conf : ℕ → Bool) (m : Mv) : Bool :=
  match m.tok with
  | some t => !pend t || conf t
  | none => false

/-- `itBook`'s `euro`: the rule for a movement on `day` (its Rome day). -/
def euroIn (pend : ℕ → Bool) (st : Statements) (day : ℕ) : Mv → Bool := isEuro pend (confirmed st day)

/-- `itRate`: 26% to 2025; from 2026 26% for a euro e-money token's line and 33% for any other. -/
def itRate (year : ℕ) (euroEmt : Bool) : ℚ := if year ≤ 2025 then 26 / 100 else if euroEmt then 26 / 100 else 33 / 100

/-- **IT-9** A pending token is not a euro e-money token on a day before every statement's day for it (or with none). -/
theorem pending_before (pend : ℕ → Bool) (st : Statements) (day t : ℕ) (m : Mv) (ht : m.tok = some t)
    (hp : pend t = true) (hy : ∀ s ∈ st, s.1 = t → day < s.2) : euroIn pend st day m = false := by
  simp only [euroIn, isEuro, ht, hp, confirmed, Bool.not_true, Bool.false_or, List.any_eq_false]
  intro s hs; have := hy s hs; simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, not_and, not_le]
  intro h; exact this h

/-- **IT-9** A pending token is a euro e-money token from the day of a statement for it on. -/
theorem pending_from (pend : ℕ → Bool) (st : Statements) (day t d0 : ℕ) (m : Mv) (ht : m.tok = some t)
    (hs : (t, d0) ∈ st) (hy : d0 ≤ day) : euroIn pend st day m = true := by
  simp only [euroIn, isEuro, ht, confirmed, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true]
  exact Or.inr ⟨(t, d0), hs, by simp [hy]⟩

/-- **IT-9** A token not pending (EURCV, EURR) is a euro e-money token on every day, whatever the statements; a coin
that is none of the issuers' euro tokens never is. -/
theorem not_pending (pend : ℕ → Bool) (st : Statements) (day t : ℕ) (m : Mv) :
    (m.tok = some t → pend t = false → euroIn pend st day m = true) ∧ (m.tok = none → euroIn pend st day m = false) := by
  constructor
  · intro ht hp; simp [euroIn, isEuro, ht, hp]
  · intro ht; simp [euroIn, isEuro, ht]

/-- **IT-9** From 2026, a line of a pending token on a day before every statement's day for it is at 33%, and from the
day of a statement for it on at 26%. -/
theorem pending_rate (pend : ℕ → Bool) (st : Statements) (year day t : ℕ) (m : Mv) (ht : m.tok = some t)
    (hp : pend t = true) (h26 : 2026 ≤ year) :
    ((∀ s ∈ st, s.1 = t → day < s.2) → itRate year (euroIn pend st day m) = 33 / 100) ∧
      (∀ d0, (t, d0) ∈ st → d0 ≤ day → itRate year (euroIn pend st day m) = 26 / 100) := by
  have : ¬ year ≤ 2025 := by omega
  constructor
  · intro hy; rw [pending_before pend st day t m ht hp hy]; simp [itRate, this]
  · intro d0 hs hy; rw [pending_from pend st day t d0 m ht hs hy]; simp [itRate, this]

/-- Statements `st2` dated no earlier than `st1`: every statement in `st2` has one in `st1` for the same token on the
same day or before. -/
def noEarlier (st1 st2 : Statements) : Prop := ∀ s ∈ st2, ∃ s' ∈ st1, s'.1 = s.1 ∧ s'.2 ≤ s.2

/-- **IT-9** A later statement date never makes a movement a euro e-money token where an earlier one did not, so it
never lowers the rate of any line: every line is at the same rate or higher (26% → 33%). -/
theorem later_statement_rate (pend : ℕ → Bool) (st1 st2 : Statements) (h : noEarlier st1 st2) (year day : ℕ)
    (m : Mv) :
    (euroIn pend st2 day m = true → euroIn pend st1 day m = true) ∧
      itRate year (euroIn pend st1 day m) ≤ itRate year (euroIn pend st2 day m) := by
  have imp : euroIn pend st2 day m = true → euroIn pend st1 day m = true := by
    simp only [euroIn, isEuro]
    rcases m.tok with _ | t
    · simp
    · simp only [Bool.or_eq_true, Bool.not_eq_true', confirmed, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq]
      rintro (hp | ⟨s, hs, hst, hd⟩)
      · exact Or.inl hp
      · obtain ⟨s', hs', e1, e2⟩ := h s hs
        exact Or.inr ⟨s', hs', e1.trans hst, e2.trans hd⟩
  refine ⟨imp, ?_⟩
  unfold itRate
  rcases h1 : euroIn pend st1 day m <;> rcases h2 : euroIn pend st2 day m <;> simp_all <;> split_ifs <;> norm_num

/-! ### Kinds and the swap -/

/-- `kindOf`: NFT, else e-money token, else coin. -/
def kindOf (m : Mv) : ℕ := if m.nft then 2 else if m.emt then 1 else 0

/-- One kind only (a set of kinds of size 1: false for no legs). -/
def oneKind : List Mv → Bool
  | [] => false
  | m :: ms => ms.all fun x => kindOf x == kindOf m

/-- `sameKind`: every leg on both sides of one kind. -/
def sameKind (a b : List Mv) : Bool := oneKind (a ++ b)

/-- Money moved: its value in euros (none: no rate) and whether it is euros. -/
structure Money where
  value : Option ℚ
  eur : Bool := true

/-- A swap happening: the year and the day (Rome), crypto out and in, money out and in, and `keepsCost` (a coin put
into an app for its receipt coin). -/
structure SwapH where
  year : ℕ
  day : ℕ := 0
  out : List Mv
  inn : List Mv
  fOut : List Money := []
  fIn : List Money := []
  keepsCost : Bool := false

/-- `sum`: the total, none when any value is missing. -/
def sumV : List (Option ℚ) → Option ℚ
  | [] => some 0
  | v :: vs => match v, sumV vs with
    | some a, some b => some (a + b)
    | _, _ => none

def coins (ms : List Mv) : List Coin := ms.map fun m => ⟨m.asset, m.qty⟩
def gots (ms : List Mv) : List Got := ms.map fun m => ⟨m.asset, m.qty, m.value⟩

/-- `buys`: the coins that came in, as buys sharing `total` by value (equally when one has none). -/
def buys (ins : List Mv) (total : ℚ) : List Op :=
  ins.map fun m => .buy m.asset m.qty (portion total (ins.map Mv.value) m.value)

/-- The money paid on top of an untaxed swap (`paid`, kept only when known and above 0). -/
def paidOf (fOut : List Money) : ℚ :=
  if fOut = [] then 0 else match sumV (fOut.map Money.value) with
    | some p => if 0 < p then p else 0
    | none => 0

/-- From 2026, euro e-money tokens only, turned into euros only (L. 199/2025 art. 1 c. 28): no gain or loss. -/
def euroRedeem (euro : Mv → Bool) (h : SwapH) : Bool :=
  decide (2026 ≤ h.year) && h.out.all euro && h.fIn.all Money.eur

/-- `splitMixed` (no money on either side, legs of more than one kind; Circolare 30/E p. 48). Case A, everything
received of one kind: the legs given of that kind (`keep`) carry their cost to what came in, the others (`sell`) are
realised at their value `v`, which is added to the cost carried; nothing of value in `sell`: the whole swap carries.
Case B, everything given of one kind (report/it.ts:319-336): one part swap of every coin given (`ItPartSwap`), the
share `f = vGot ÷ vAll` of what those coins cost (newest lots first) realised at `vGot` and the rest carried to the legs
received of that kind (`keep`); the others (`got`) are bought at their value `vGot`; nothing of value in `got` (or no
value in all): the whole swap carries. None (the
caller taxes the whole swap): both sides mixed, a part empty, a value missing. -/
def splitMixed (euro : Mv → Bool) (out inn : List Mv) : Option (List Op) :=
  if oneKind inn then
    let k := (inn.head?.map kindOf).getD 0
    let keep := out.filter fun m => kindOf m == k
    let sell := out.filter fun m => kindOf m != k
    if keep = [] ∨ sell = [] then none else
    match sumV (sell.map Mv.value) with
    | none => none
    | some v =>
      if v = 0 then some [.swap (coins out) (gots inn) 0]
      else some [.dispose (coins sell) v (sell.all euro), .swap (coins keep) (gots inn) (if 0 < v then v else 0)]
  else if oneKind out then
    let k := (out.head?.map kindOf).getD 0
    let keep := inn.filter fun m => kindOf m == k
    let got := inn.filter fun m => kindOf m != k
    if keep = [] ∨ got = [] then none else
    match sumV (got.map Mv.value), sumV (inn.map Mv.value) with
    | some vg, some va =>
      if vg = 0 ∨ va ≤ 0 then some [.swap (coins out) (gots inn) 0]
      else some (.part (coins out) (vg / va) vg (out.all euro) (gots keep) :: buys got vg)
    | _, _ => none
  else none

/-- The taxable exchange: what was given goes at the value of what came in plus money received less money paid (never
below 0); with an NFT and no money, a missing value of what came in is taken as the value given (Circolare 30/E p. 47);
what came in is bought at that value (or the value given). -/
def exchange (euro : Mv → Bool) (h : SwapH) : List Op :=
  let nft := (h.out ++ h.inn).any Mv.nft
  let vin := (sumV (h.inn.map Mv.value)).or
    (if nft = true ∧ h.fIn = [] ∧ h.fOut = [] then sumV (h.out.map Mv.value) else none)
  let mIn := if h.fIn ≠ [] then sumV (h.fIn.map Money.value) else some 0
  let mOut := if h.fOut ≠ [] then sumV (h.fOut.map Money.value) else some 0
  let proceeds : Option ℚ := match vin, mIn, mOut with
    | some a, some b, some c => some (max (a + b - c) 0)
    | _, _, _ => none
  .dispose (coins h.out) ((proceeds.or (sumV (h.out.map Mv.value))).getD 0) (h.out.all euro) ::
    buys h.inn ((vin.or (sumV (h.out.map Mv.value))).getD 0)

/-- `itBook` for one swap happening, `euro` the euro token rule of its day (`euroIn pend st h.day`). -/
def classify (euro : Mv → Bool) (h : SwapH) : List Op :=
  if h.keepsCost then (if h.out ≠ [] ∧ h.inn ≠ [] then [.swap (coins h.out) (gots h.inn) 0] else [])
  else if h.out = [] then
    (if h.inn ≠ [] then
      buys h.inn (((if h.fOut ≠ [] then sumV (h.fOut.map Money.value) else none).or
        (sumV (h.inn.map Mv.value))).getD 0)
     else [])
  else if h.inn = [] then
    (if h.fIn = [] then [.drop (coins h.out)]
     else if euroRedeem euro h then [.drop (coins h.out)]
     else [.dispose (coins h.out) (((sumV (h.fIn.map Money.value)).or (sumV (h.out.map Mv.value))).getD 0)
       (h.out.all euro)])
  else if h.fIn = [] ∧ sameKind h.out h.inn = true then [.swap (coins h.out) (gots h.inn) (paidOf h.fOut)]
  else match (if h.fIn = [] ∧ h.fOut = [] then splitMixed euro h.out h.inn else none) with
    | some ops => ops
    | none => exchange euro h

/-- `itRun`'s order for ops at one time: buys, proventi, untaxed swaps, sales, drops (each kind in the order made). -/
def rank : Op → ℕ
  | .buy .. => 0
  | .income .. => 1
  | .swap .. => 2
  | .dispose .. => 3
  | .part .. => 3
  | .drop .. => 4

def byKind (ops : List Op) : List Op :=
  ops.filter (rank · == 0) ++ ops.filter (rank · == 1) ++ ops.filter (rank · == 2) ++ ops.filter (rank · == 3) ++
    ops.filter (rank · == 4)

/-- **IT-2** Crypto for crypto of the same kind (all coins, all e-money tokens, or all NFTs) with no money received: one
untaxed swap, with the money paid on top (when known and above 0) added to the cost carried. -/
theorem same_kind_untaxed (euro : Mv → Bool) (h : SwapH) (hk : h.keepsCost = false) (ho : h.out ≠ []) (hi : h.inn ≠ [])
    (hf : h.fIn = []) (hs : sameKind h.out h.inn = true) :
    classify euro h = [.swap (coins h.out) (gots h.inn) (paidOf h.fOut)] := by
  simp [classify, hk, ho, hi, hf, hs]

/-- Legs of no common kind: no leg given has the kind of a leg received. -/
def apart (a b : List Mv) : Prop := ∀ x ∈ a, ∀ y ∈ b, kindOf x ≠ kindOf y

theorem filter_kind_nil (l : List Mv) (y : Mv) (h : ∀ x ∈ l, kindOf x ≠ kindOf y) :
    l.filter (fun m => kindOf m == kindOf y) = [] := by
  rw [List.filter_eq_nil_iff]; intro x hx; simpa using h x hx

/-- With no kind in common, `splitMixed` does not apply: the whole swap is taxed. -/
theorem split_none_apart (euro : Mv → Bool) (out inn : List Mv) (h : apart out inn) :
    splitMixed euro out inn = none := by
  unfold splitMixed
  by_cases h1 : oneKind inn = true
  · cases inn with
    | nil => simp [oneKind] at h1
    | cons y ys =>
      have : out.filter (fun m => kindOf m == kindOf y) = [] := filter_kind_nil out y (fun x hx => h x hx y (by simp))
      simp [h1, this]
  · rw [if_neg h1]
    by_cases h2 : oneKind out = true
    · cases out with
      | nil => simp [oneKind] at h2
      | cons y ys =>
        have : inn.filter (fun m => kindOf m == kindOf y) = [] :=
          filter_kind_nil inn y (fun x hx hk => h y (by simp) x hx hk.symm)
        simp [h2, this]
    · rw [if_neg h2]

/-- **IT-3** Legs of no common kind (a coin for an e-money token or back, crypto for an NFT or back), with no money: a
taxable exchange at the value of what came in (never below 0), and what came in is bought at that value. -/
theorem apart_exchange_taxed (euro : Mv → Bool) (h : SwapH) (v : ℚ) (hk : h.keepsCost = false) (ho : h.out ≠ [])
    (hi : h.inn ≠ []) (hf : h.fIn = []) (hfo : h.fOut = []) (hs : sameKind h.out h.inn = false)
    (ha : apart h.out h.inn) (hv : sumV (h.inn.map Mv.value) = some v) :
    classify euro h = .dispose (coins h.out) (max v 0) (h.out.all euro) :: buys h.inn v := by
  simp [classify, hk, ho, hi, hf, hfo, hs, split_none_apart euro _ _ ha, exchange, hv]

/-- **IT-3** NFTs: an NFT for NFTs (no money in) is an untaxed swap. Crypto for an NFT or an NFT for crypto (every leg
of one side an NFT, none of the other), with no money: a taxable exchange at the value of what came in, or, when that
has no price, at the value of what was given; what came in is bought at that same value. -/
theorem nft_rules (euro : Mv → Bool) (h : SwapH) (hk : h.keepsCost = false) (ho : h.out ≠ []) (hi : h.inn ≠ []) :
    (h.fIn = [] → (∀ m ∈ h.out ++ h.inn, m.nft = true) →
      classify euro h = [.swap (coins h.out) (gots h.inn) (paidOf h.fOut)]) ∧
    (∀ v, h.fIn = [] → h.fOut = [] →
      (((∀ m ∈ h.out, m.nft = true) ∧ ∀ m ∈ h.inn, m.nft = false) ∨
        ((∀ m ∈ h.out, m.nft = false) ∧ ∀ m ∈ h.inn, m.nft = true)) →
      (sumV (h.inn.map Mv.value)).or (sumV (h.out.map Mv.value)) = some v →
      classify euro h = .dispose (coins h.out) (max v 0) (h.out.all euro) :: buys h.inn v) := by
  have kn : ∀ m : Mv, m.nft = true → kindOf m = 2 := fun m hm => by simp [kindOf, hm]
  have kc : ∀ m : Mv, m.nft = false → kindOf m ≠ 2 := fun m hm => by
    unfold kindOf; rw [hm]; simp only [Bool.false_eq_true, if_false]; split_ifs <;> decide
  constructor
  · intro hf hn
    apply same_kind_untaxed euro h hk ho hi hf
    unfold sameKind
    generalize hl : h.out ++ h.inn = l at hn
    cases l with
    | nil => simp at hl; exact absurd hl.1 ho
    | cons y ys =>
      simp only [oneKind, List.all_eq_true, beq_iff_eq]
      intro x hx; rw [kn x (hn x (by simp [hx])), kn y (hn y (by simp))]
  · intro v hf hfo hside hv
    have ha : apart h.out h.inn := by
      intro x hx y hy hxy
      rcases hside with ⟨a, b⟩ | ⟨a, b⟩
      · exact kc y (b y hy) (hxy.symm.trans (kn x (a x hx)))
      · exact kc x (a x hx) (hxy.trans (kn y (b y hy)))
    have hs : sameKind h.out h.inn = false := by
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ ho
      obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hi
      unfold sameKind
      generalize hl : h.out ++ h.inn = l
      cases l with
      | nil => simp at hl; exact absurd hl.1 ho
      | cons z zs =>
        simp only [oneKind, List.all_eq_false, beq_iff_eq]
        have mx : x ∈ z :: zs := hl ▸ (by simp [hx])
        have my : y ∈ z :: zs := hl ▸ (by simp [hy])
        by_contra hc; push_neg at hc
        have e : ∀ w ∈ z :: zs, kindOf w = kindOf z := by
          intro w hw; rcases List.mem_cons.mp hw with rfl | hw
          · rfl
          · exact hc w hw
        exact ha x hx y hy ((e x mx).trans (e y my).symm)
    have hnft : (h.out ++ h.inn).any Mv.nft = true := by
      rcases hside with ⟨a, _⟩ | ⟨_, b⟩
      · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ ho; exact List.any_eq_true.mpr ⟨x, by simp [hx], a x hx⟩
      · obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hi; exact List.any_eq_true.mpr ⟨y, by simp [hy], b y hy⟩
    simp only [classify, hk, ho, hi, hf, hfo, hs, split_none_apart euro _ _ ha, exchange]
    rcases h1 : sumV (h.inn.map Mv.value) with _ | a <;> rcases h2 : sumV (h.out.map Mv.value) with _ | b <;>
      simp_all

/-- **IT-3** Crypto sold for money (outside the 2026 euro e-money token rule): a sale at the money received. -/
theorem sale_for_money (euro : Mv → Bool) (h : SwapH) (m : ℚ) (hk : h.keepsCost = false) (ho : h.out ≠ [])
    (hi : h.inn = []) (hf : h.fIn ≠ []) (hr : euroRedeem euro h = false) (hm : sumV (h.fIn.map Money.value) = some m) :
    classify euro h = [.dispose (coins h.out) m (h.out.all euro)] := by
  simp [classify, hk, ho, hi, hf, hr, hm]

/-- **IT-2** (where the code differs from "money paid on top") Money received with a swap makes the whole swap a
taxable exchange: the first op is a sale of every coin given. -/
theorem money_in_taxed (euro : Mv → Bool) (h : SwapH) (hk : h.keepsCost = false) (ho : h.out ≠ []) (hi : h.inn ≠ [])
    (hf : h.fIn ≠ []) : ∃ p e rest, classify euro h = .dispose (coins h.out) p e :: rest := by
  simp only [classify, hk, ho, hi, hf, Bool.false_eq_true, if_false, ne_eq, not_false_eq_true, false_and, exchange]
  exact ⟨_, _, _, rfl⟩

/-- **IT-2** Both sides mixed (legs of more than one kind given and received), no money: no split, the whole swap is
a taxable exchange. -/
theorem both_mixed_whole (euro : Mv → Bool) (h : SwapH) (hk : h.keepsCost = false) (ho : h.out ≠ [])
    (hi : h.inn ≠ []) (hs : sameKind h.out h.inn = false) (h1 : oneKind h.inn = false) (h2 : oneKind h.out = false) :
    classify euro h = exchange euro h := by
  by_cases hf : h.fIn = [] <;> by_cases hfo : h.fOut = [] <;>
    simp [classify, hk, ho, hi, hf, hfo, hs, splitMixed, h1, h2]

/-- **IT-2** Case A, everything received of one kind (`y` the first leg received): when the legs given of another kind
(`sell`) are worth `v > 0`, they are realised in one line at `v` (a euro e-money token's only when every one of them
is), and the legs given of the kind received (`keep`) go into what came in as an untaxed swap with `v` paid on top. -/
theorem case_a (euro : Mv → Bool) (h : SwapH) (y : Mv) (ys : List Mv) (v : ℚ) (hk : h.keepsCost = false)
    (ho : h.out ≠ []) (hi : h.inn = y :: ys) (hf : h.fIn = []) (hfo : h.fOut = []) (hs : sameKind h.out h.inn = false)
    (h1 : oneKind h.inn = true) (hkeep : h.out.filter (fun m => kindOf m == kindOf y) ≠ [])
    (hsell : h.out.filter (fun m => kindOf m != kindOf y) ≠ [])
    (hv : sumV ((h.out.filter fun m => kindOf m != kindOf y).map Mv.value) = some v) (hv0 : 0 < v) :
    classify euro h =
      [.dispose (coins (h.out.filter fun m => kindOf m != kindOf y)) v
          ((h.out.filter fun m => kindOf m != kindOf y).all euro),
        .swap (coins (h.out.filter fun m => kindOf m == kindOf y)) (gots h.inn) v] := by
  have hne : v ≠ 0 := ne_of_gt hv0
  have hh : (Option.map kindOf h.inn.head?).getD 0 = kindOf y := by rw [hi]; rfl
  have hi' : h.inn ≠ [] := by rw [hi]; simp
  simp [classify, hk, ho, hi', hf, hfo, hs, splitMixed, h1, hh, hkeep, hsell, hv, hne, hv0]

/-- **IT-2** Case A with the legs of another kind worth nothing: the whole swap carries its cost, no line. -/
theorem case_a_zero (euro : Mv → Bool) (h : SwapH) (y : Mv) (ys : List Mv) (hk : h.keepsCost = false)
    (ho : h.out ≠ []) (hi : h.inn = y :: ys) (hf : h.fIn = []) (hfo : h.fOut = []) (hs : sameKind h.out h.inn = false)
    (h1 : oneKind h.inn = true) (hkeep : h.out.filter (fun m => kindOf m == kindOf y) ≠ [])
    (hsell : h.out.filter (fun m => kindOf m != kindOf y) ≠ [])
    (hv : sumV ((h.out.filter fun m => kindOf m != kindOf y).map Mv.value) = some 0) :
    classify euro h = [.swap (coins h.out) (gots h.inn) 0] := by
  have hh : (Option.map kindOf h.inn.head?).getD 0 = kindOf y := by rw [hi]; rfl
  have hi' : h.inn ≠ [] := by rw [hi]; simp
  simp [classify, hk, ho, hi', hf, hfo, hs, splitMixed, h1, hh, hkeep, hsell, hv]

/-- **IT-2** Case B, everything given of one kind (`y` the first leg given, received legs not all of one kind): with
`vg > 0` the value of the legs received of another kind (`got`) and `va > 0` the value of all received, one part swap
of every coin given realises the share `f = vg ÷ va` of their cost in one line at `vg` and carries the rest to the legs
received of the kind given (`keep`); `got` is bought at `vg`. -/
theorem case_b (euro : Mv → Bool) (h : SwapH) (y : Mv) (ys : List Mv) (vg va : ℚ) (hk : h.keepsCost = false)
    (ho : h.out = y :: ys) (hi : h.inn ≠ []) (hf : h.fIn = []) (hfo : h.fOut = []) (hs : sameKind h.out h.inn = false)
    (h1 : oneKind h.inn = false) (h2 : oneKind h.out = true)
    (hkeep : h.inn.filter (fun m => kindOf m == kindOf y) ≠ []) (hgot : h.inn.filter (fun m => kindOf m != kindOf y) ≠ [])
    (hg : sumV ((h.inn.filter fun m => kindOf m != kindOf y).map Mv.value) = some vg)
    (ha : sumV (h.inn.map Mv.value) = some va) (hg0 : vg ≠ 0) (ha0 : 0 < va) :
    classify euro h =
      .part (coins h.out) (vg / va) vg (h.out.all euro) (gots (h.inn.filter fun m => kindOf m == kindOf y)) ::
        buys (h.inn.filter fun m => kindOf m != kindOf y) vg := by
  have ho' : h.out ≠ [] := by rw [ho]; simp
  have hna : ¬ va ≤ 0 := not_le.mpr ha0
  have hh : (Option.map kindOf h.out.head?).getD 0 = kindOf y := by rw [ho]; rfl
  simp [classify, hk, ho', hi, hf, hfo, hs, splitMixed, h1, h2, hh, hkeep, hgot, hg, ha, hg0, hna]

/-- **IT-2** Case B with the legs received of another kind worth nothing: the whole swap carries its cost, no line. -/
theorem case_b_zero (euro : Mv → Bool) (h : SwapH) (y : Mv) (ys : List Mv) (va : ℚ) (hk : h.keepsCost = false)
    (ho : h.out = y :: ys) (hi : h.inn ≠ []) (hf : h.fIn = []) (hfo : h.fOut = []) (hs : sameKind h.out h.inn = false)
    (h1 : oneKind h.inn = false) (h2 : oneKind h.out = true)
    (hkeep : h.inn.filter (fun m => kindOf m == kindOf y) ≠ []) (hgot : h.inn.filter (fun m => kindOf m != kindOf y) ≠ [])
    (hg : sumV ((h.inn.filter fun m => kindOf m != kindOf y).map Mv.value) = some 0)
    (ha : sumV (h.inn.map Mv.value) = some va) :
    classify euro h = [.swap (coins h.out) (gots h.inn) 0] := by
  have ho' : h.out ≠ [] := by rw [ho]; simp
  have hh : (Option.map kindOf h.out.head?).getD 0 = kindOf y := by rw [ho]; rfl
  simp [classify, hk, ho', hi, hf, hfo, hs, splitMixed, h1, h2, hh, hkeep, hgot, hg, ha]

/-- **IT-2** Quantities in Case A: the coins carried (`keep`) and the coins realised (`sell`) are exactly the coins
given, split by kind. -/
theorem case_a_qty (out : List Mv) (k : ℕ) :
    ((coins (out.filter fun m => kindOf m == k)).map Coin.qty).sum +
      ((coins (out.filter fun m => kindOf m != k)).map Coin.qty).sum = ((coins out).map Coin.qty).sum := by
  induction out with
  | nil => simp [coins]
  | cons m ms ih =>
    by_cases hm : kindOf m = k
    · simp [coins, hm] at ih ⊢; linarith
    · simp [coins, hm] at ih ⊢; linarith

/-- **IT-10** From 2026, euro e-money tokens turned into euros (L. 199/2025 art. 1 c. 28) go with no line, so no gain
or loss and no cost carried; this happens only when every coin given is a euro e-money token in that year and all the
money received is euros, from 2026. Otherwise the coins are sold at the money received. -/
theorem euro_redeem_iff (euro : Mv → Bool) (h : SwapH) (hk : h.keepsCost = false) (ho : h.out ≠ []) (hi : h.inn = [])
    (hf : h.fIn ≠ []) :
    classify euro h = [.drop (coins h.out)] ↔
      (2026 ≤ h.year ∧ (∀ m ∈ h.out, euro m = true) ∧ ∀ x ∈ h.fIn, x.eur = true) := by
  by_cases hr : euroRedeem euro h = true
  · have : 2026 ≤ h.year ∧ (∀ m ∈ h.out, euro m = true) ∧ ∀ x ∈ h.fIn, x.eur = true := by
      simpa [euroRedeem, List.all_eq_true, and_assoc] using hr
    simpa [classify, hk, ho, hi, hf, hr] using this
  · have hr' : ¬ (2026 ≤ h.year ∧ (∀ m ∈ h.out, euro m = true) ∧ ∀ x ∈ h.fIn, x.eur = true) := by
      intro c; apply hr; simp only [euroRedeem, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
      exact ⟨⟨c.1, c.2.1⟩, c.2.2⟩
    simp only [Bool.not_eq_true] at hr
    simp [classify, hk, ho, hi, hf, hr, hr']

/-- **IT-10** The redemption follows the token's day: from 2026, a pending token `t` (EURC, EURI, EURQ) turned into
euros is not realised exactly when a statement for it is dated on that day or before. -/
theorem redeem_days (pend : ℕ → Bool) (st : Statements) (h : SwapH) (t : ℕ) (hk : h.keepsCost = false)
    (ho : h.out ≠ []) (hi : h.inn = []) (hf : h.fIn ≠ []) (ht : ∀ m ∈ h.out, m.tok = some t) (hp : pend t = true)
    (he : ∀ x ∈ h.fIn, x.eur = true) (hy : 2026 ≤ h.year) :
    classify (euroIn pend st h.day) h = [.drop (coins h.out)] ↔ ∃ d0, (t, d0) ∈ st ∧ d0 ≤ h.day := by
  rw [euro_redeem_iff _ h hk ho hi hf]
  constructor
  · rintro ⟨-, hall, -⟩
    obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil _ ho
    by_contra hc; push_neg at hc
    have := pending_before pend st h.day t m (ht m hm) hp (fun s hs hst => hc s.2 (by rw [← hst]; exact hs))
    rw [hall m hm] at this; exact absurd this (by simp)
  · rintro ⟨d0, hs, hd0⟩
    exact ⟨hy, fun m hm => pending_from pend st h.day t d0 m (ht m hm) hs hd0, he⟩

/-- **IT-10** Euros received for a pending token `t` on a day before every statement's day for it are realised: a
sale at the euros received, not marked a euro e-money token's (so at 33% from 2026). -/
theorem redeem_before_day (pend : ℕ → Bool) (st : Statements) (h : SwapH) (t : ℕ) (mon : ℚ)
    (hk : h.keepsCost = false) (ho : h.out ≠ []) (hi : h.inn = []) (hf : h.fIn ≠ [])
    (ht : ∀ m ∈ h.out, m.tok = some t) (hp : pend t = true) (hd : ∀ s ∈ st, s.1 = t → h.day < s.2)
    (hm : sumV (h.fIn.map Money.value) = some mon) :
    classify (euroIn pend st h.day) h = [.dispose (coins h.out) mon false] := by
  obtain ⟨m, hmo⟩ := List.exists_mem_of_ne_nil _ ho
  have hm0 := pending_before pend st h.day t m (ht m hmo) hp hd
  have hall : h.out.all (euroIn pend st h.day) = false := List.all_eq_false.mpr ⟨m, hmo, by simp [hm0]⟩
  have hr : euroRedeem (euroIn pend st h.day) h = false := by simp [euroRedeem, hall]
  rw [sale_for_money _ h mon hk ho hi hf hr hm, hall]

/-- **IT-10** The coins dropped make no line and no lot: over the assets given, the cost taken leaves the cost held. -/
theorem drop_no_line (A : Finset ℕ) (st : Stacks) (gave : List Coin) (h : ∀ c ∈ gave, c.asset ∈ A) :
    (step st (.drop gave)).2 = none ∧ totalCost A (step st (.drop gave)).1 + (takeAll st gave).1 = totalCost A st := by
  refine ⟨rfl, ?_⟩
  have := takeAll_cost A st gave h
  simp only [step]; linarith

/-- **IT-10** Before 2026 the same redemption is a sale at the euros received, marked a euro e-money token's. -/
theorem euro_redeem_2025_taxed (euro : Mv → Bool) (h : SwapH) (m : ℚ) (hk : h.keepsCost = false) (ho : h.out ≠ [])
    (hi : h.inn = []) (hf : h.fIn ≠ []) (hy : h.year ≤ 2025) (hm : sumV (h.fIn.map Money.value) = some m) :
    classify euro h = [.dispose (coins h.out) m (h.out.all euro)] := by
  have : euroRedeem euro h = false := by simp [euroRedeem]; omega
  exact sale_for_money euro h m hk ho hi hf this hm

/-- **IT-10** Euros (or any money) turned into tokens: only buys at the money paid, no line. -/
theorem bought_with_money (euro : Mv → Bool) (h : SwapH) (p : ℚ) (hk : h.keepsCost = false) (ho : h.out = [])
    (hi : h.inn ≠ []) (hf : h.fOut ≠ []) (hp : sumV (h.fOut.map Money.value) = some p) :
    classify euro h = buys h.inn p := by
  simp [classify, hk, ho, hi, hf, hp]

def Op.cost : Op → ℚ
  | .buy _ _ c => c
  | _ => 0

/-- **IT-3** What came in is bought for exactly the total, split by value (equally when a value is missing). -/
theorem buys_total (ins : List Mv) (total : ℚ) (h : ins ≠ []) : ((buys ins total).map Op.cost).sum = total := by
  have := portion_sum total (ins.map Mv.value) (by simpa using h)
  rw [List.map_map] at this
  simpa [buys, Op.cost, Function.comp_def] using this

/-! ### Cost through the split (`itRun` on the ops of one time, in `byKind` order) -/

theorem run_append (st : Stacks) (a b : List Op) :
    run st (a ++ b) = ((run st a).1 ++ (run (run st a).2 b).1, (run (run st a).2 b).2) := by
  induction a generalizing st with
  | nil => simp [run]
  | cons o os ih => simp only [List.cons_append, run, ih, List.append_assoc]

theorem run_buys (A : Finset ℕ) (ins : List Mv) (total : ℚ) (st : Stacks) (hA : ∀ m ∈ ins, m.asset ∈ A)
    (hq : ∀ m ∈ ins, 0 < m.qty) (hne : ins ≠ []) :
    (run st (buys ins total)).1 = [] ∧ totalCost A (run st (buys ins total)).2 = totalCost A st + total := by
  have key : ∀ (c : Mv → ℚ) (ms : List Mv) (st : Stacks), (∀ m ∈ ms, m.asset ∈ A) → (∀ m ∈ ms, 0 < m.qty) →
      (run st (ms.map fun m => Op.buy m.asset m.qty (c m))).1 = [] ∧
        totalCost A (run st (ms.map fun m => Op.buy m.asset m.qty (c m))).2 = totalCost A st + (ms.map c).sum := by
    intro c ms
    induction ms with
    | nil => intro st _ _; simp [run]
    | cons m ms ih =>
      intro st hA hq
      have hm : 0 < m.qty := hq m (by simp)
      obtain ⟨h1, h2⟩ := ih (push st m.asset ⟨m.qty, c m⟩) (fun x hx => hA x (by simp [hx]))
        (fun x hx => hq x (by simp [hx]))
      simp only [List.map_cons, run, step, hm, if_true, Option.toList, List.nil_append]
      refine ⟨h1, ?_⟩
      rw [h2, push, total_update A st m.asset _ (hA m (by simp))]
      simp [sumCost]; ring
  obtain ⟨k1, k2⟩ := key (fun m => portion total (ins.map Mv.value) m.value) ins st hA hq
  unfold buys
  refine ⟨k1, ?_⟩
  rw [k2]
  have := buys_total ins total hne
  simp only [buys, List.map_map, Function.comp_def, Op.cost] at this
  rw [this]

theorem byKind_buys (ins : List Mv) (total : ℚ) (r : ℕ) :
    (buys ins total).filter (rank · == r) = if r = 0 then buys ins total else [] := by
  unfold buys
  split_ifs with h
  · subst h; rw [List.filter_eq_self]; intro x hx; obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx; rfl
  · rw [List.filter_eq_nil_iff]; intro x hx; obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx
    simp [rank]; omega

/-- **IT-2** Case A conserves cost: run in `itRun`'s order (the swap, then the line), the cost held after is the cost
held before less the cost realised plus the value realised `v` (which becomes cost of what came in). So the cost
carried plus the cost realised is the cost given: the split invents no cost and loses none. -/
theorem case_a_cost (A : Finset ℕ) (st : Stacks) (sell keep inn : List Mv) (v : ℚ) (e : Bool)
    (hA : ∀ m ∈ sell ++ keep ++ inn, m.asset ∈ A) (hpos : (gots inn).filter (fun x => decide (0 < x.qty)) ≠ []) :
    ∃ l, (run st (byKind [.dispose (coins sell) v e, .swap (coins keep) (gots inn) v])).1 = [l] ∧ l.proceeds = v ∧
      totalCost A (run st (byKind [.dispose (coins sell) v e, .swap (coins keep) (gots inn) v])).2 =
        totalCost A st - l.cost + l.proceeds := by
  have hb : byKind [.dispose (coins sell) v e, .swap (coins keep) (gots inn) v] =
      [.swap (coins keep) (gots inn) v, .dispose (coins sell) v e] := by simp [byKind, rank]
  rw [hb]
  have hk : ∀ c ∈ coins keep, c.asset ∈ A := by
    intro c hc; obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hc; exact hA m (by simp [hm])
  have hs : ∀ c ∈ coins sell, c.asset ∈ A := by
    intro c hc; obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hc; exact hA m (by simp [hm])
  have hi : ∀ g ∈ gots inn, g.asset ∈ A := by
    intro g hg; obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hg; exact hA m (by simp [hm])
  have h1 := swap_conserves A st (coins keep) (gots inn) v hk hi hpos
  have hn := swap_no_line st (coins keep) (gots inn) v
  set st1 := (step st (.swap (coins keep) (gots inn) v)).1
  have h2 := takeAll_cost A st1 (coins sell) hs
  refine ⟨⟨.sale, v, (takeAll st1 (coins sell)).1, v - (takeAll st1 (coins sell)).1, (takeAll st1 (coins sell)).2.1,
    e⟩, ?_, rfl, ?_⟩
  · simp only [run, hn, Option.toList, List.nil_append, List.append_nil]; rfl
  · show totalCost A (takeAll st1 (coins sell)).2.2 = _
    dsimp only; linarith

/-- **IT-2** Case B conserves cost: run in `itRun`'s order (the buys of `got`, then the part swap), the cost held after
is the cost held before less the cost realised plus `vg` (the cost of `got`). The line's cost is `f` of what the coins
given cost, newest lots first, and the rest of that cost is carried to `keep`. -/
theorem case_b_cost (A : Finset ℕ) (st : Stacks) (out keep got : List Mv) (f vg : ℚ) (e : Bool)
    (hA : ∀ m ∈ out ++ keep ++ got, m.asset ∈ A) (hpos : (gots keep).filter (fun x => decide (0 < x.qty)) ≠ [])
    (hq : ∀ m ∈ got, 0 < m.qty) (hg : got ≠ []) :
    ∃ l, (run st (byKind (.part (coins out) f vg e (gots keep) :: buys got vg))).1 = [l] ∧ l.proceeds = vg ∧
      l.cost = (takeAll (run st (buys got vg)).2 (coins out)).1 * f ∧
      totalCost A (run st (byKind (.part (coins out) f vg e (gots keep) :: buys got vg))).2 =
        totalCost A st - l.cost + l.proceeds := by
  have hb : byKind (.part (coins out) f vg e (gots keep) :: buys got vg) =
      buys got vg ++ [.part (coins out) f vg e (gots keep)] := by
    have := byKind_buys got vg
    simp only [byKind, List.filter_cons, this]
    simp [rank]
  rw [hb, run_append]
  obtain ⟨b1, b2⟩ := run_buys A got vg st (fun m hm => hA m (by simp [hm])) hq hg
  set st0 := (run st (buys got vg)).2
  have hs : ∀ c ∈ coins out, c.asset ∈ A := by
    intro c hc; obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hc; exact hA m (by simp [hm])
  have hi : ∀ g ∈ gots keep, g.asset ∈ A := by
    intro g hg; obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hg; exact hA m (by simp [hm])
  have h1 := part_conserves A st0 (coins out) f vg e (gots keep) hs hi hpos
  refine ⟨⟨.sale, vg, (takeAll st0 (coins out)).1 * f, vg - (takeAll st0 (coins out)).1 * f,
    (takeAll st0 (coins out)).2.1 * f, e⟩, ?_, rfl, rfl, ?_⟩
  · simp only [run, b1, part_line, Option.toList, List.nil_append, List.append_nil]
  · simp only [run]; rw [h1, b2]; ring

/-- The app's test (Case A): 1 ETH (cost €2,000, now €3,000) and 1,000 USDC (cost €1,000) for a pool token worth
€4,000: one line, USDC realised at €1,000 for €1,000 of cost; the pool token costs €3,000 (ETH's €2,000 plus €1,000). -/
theorem lp_case_a :
    let st : Stacks := push (push (fun _ => []) 0 ⟨1, 2000⟩) 1 ⟨1000, 1000⟩
    let h : SwapH :=
      { year := 2025
        out := [⟨0, 1, some 3000, false, false, none⟩, ⟨1, 1000, some 1000, true, false, none⟩]
        inn := [⟨2, 1, some 4000, false, false, none⟩] }
    let r := run st (byKind (classify (fun _ => false) h))
    r.1 = [⟨.sale, 1000, 1000, 0, 0, false⟩] ∧ r.2 2 = [⟨1, 3000⟩] := by
  norm_num [classify, sameKind, oneKind, kindOf, splitMixed, sumV, coins, gots, byKind, rank, run, step, takeAll,
    take, push, pushAll, portion, allPos, wt, Function.update, List.cons_ne_nil, reduceCtorEq]

/-- The app's test (Case B): 1 ETH (cost €2,000) for a pool token worth €2,000 and 1,000 USDC: a third of the ETH is
realised at €1,000 for €666.67 of cost (exactly 2,000/3); the pool token costs €1,333.33 (4,000/3), USDC €1,000. -/
theorem lp_case_b :
    let st : Stacks := push (fun _ => []) 0 ⟨1, 2000⟩
    let h : SwapH :=
      { year := 2025
        out := [⟨0, 1, some 3000, false, false, none⟩]
        inn := [⟨2, 1, some 2000, false, false, none⟩, ⟨1, 1000, some 1000, true, false, none⟩] }
    let r := run st (byKind (classify (fun _ => false) h))
    r.1 = [⟨.sale, 1000, 2000 / 3, 1000 / 3, 0, false⟩] ∧ r.2 2 = [⟨1, 4000 / 3⟩] ∧ r.2 1 = [⟨1000, 1000⟩] := by
  norm_num [classify, sameKind, oneKind, kindOf, splitMixed, sumV, coins, gots, byKind, rank, run, step, takeAll,
    take, push, pushAll, portion, allPos, wt, Function.update, buys, List.cons_ne_nil, reduceCtorEq]

/-- **IT-2** Case B with lots at different costs (the app's round 6 test): ETH held as 0.5 bought for €750 and then 0.5
for €250, all given for a pool token worth €2,000 and 1,000 USDC. The part swap takes both lots (€1,000) and the line
costs a third of that, €333.33 (exactly 1,000/3); the pool token carries €666.67 (2,000/3), whatever lot is newest. -/
theorem case_b_share :
    let st : Stacks := push (push (fun _ => []) 0 ⟨1 / 2, 750⟩) 0 ⟨1 / 2, 250⟩
    let h : SwapH :=
      { year := 2025
        out := [⟨0, 1, some 3000, false, false, none⟩]
        inn := [⟨2, 1, some 2000, false, false, none⟩, ⟨1, 1000, some 1000, true, false, none⟩] }
    let r := run st (byKind (classify (fun _ => false) h))
    r.1 = [⟨.sale, 1000, 1000 / 3, 2000 / 3, 0, false⟩] ∧ r.2 2 = [⟨1, 2000 / 3⟩] := by
  norm_num [classify, sameKind, oneKind, kindOf, splitMixed, sumV, coins, gots, byKind, rank, run, step, takeAll,
    take, push, pushAll, portion, allPos, wt, Function.update, buys, List.cons_ne_nil, reduceCtorEq]
/-! ## The year (`itYearBase`, `itYears`; rules 5-8) -/

/-- Losses on hand: the year a loss came from and what is left of it (whole euros). -/
structure Entry where
  yr : ℕ
  amount : ℤ
  deriving DecidableEq

def amt (l : List Entry) : ℤ := (l.map Entry.amount).sum

@[simp] theorem amt_nil : amt [] = 0 := rfl
@[simp] theorem amt_cons (e : Entry) (l : List Entry) : amt (e :: l) = e.amount + amt l := by simp [amt]
@[simp] theorem amt_append (a b : List Entry) : amt (a ++ b) = amt a + amt b := by simp [amt]

/-- The €2,000 threshold: 2023 and 2024 (art. 67 c-sexies; RT57); none from 2025 (L. 207/2024 art. 1 c. 25). -/
def threshold (year : ℕ) : ℤ := if year ≤ 2024 then 2000 else 0

/-- RT57 col. 2: the part of the year's net (whole euros) over the threshold. -/
def yGain (year : ℕ) (n : ℤ) : ℤ := if threshold year < n then n - threshold year else 0

/-- RT57 col. 1: the part of the year's net loss over the threshold, which carries. -/
def yLoss (year : ℕ) (n : ℤ) : ℤ := if threshold year < -n then -n - threshold year else 0

/-- A loss usable this year: from one of the four years before (TUIR art. 68 c. 5), with something left. -/
abbrev usableIn (year : ℕ) (e : Entry) : Prop := e.yr < year ∧ year ≤ e.yr + 4 ∧ 0 < e.amount

/-- `itYearBase`'s loop: the losses used (oldest first, in the order given), the pool after, and the base left. -/
def use (year : ℕ) : ℤ → List Entry → List Entry × List Entry × ℤ
  | left, [] => ([], [], left)
  | left, e :: es =>
    if left ≤ 0 then ([], e :: es, left)
    else if usableIn year e then
      (⟨e.yr, min e.amount left⟩ :: (use year (left - min e.amount left) es).1,
       ⟨e.yr, e.amount - min e.amount left⟩ :: (use year (left - min e.amount left) es).2.1,
       (use year (left - min e.amount left) es).2.2)
    else ((use year left es).1, e :: (use year left es).2.1, (use year left es).2.2)

/-- `itYears`' residues: what is left and still usable next year (from year − 3 on). -/
def keep (year : ℕ) (e : Entry) : Bool := decide (0 < e.amount) && decide (year ≤ e.yr + 3)

/-- One year of `itYears`. -/
structure YearOut where
  gain : ℤ
  loss : ℤ
  used : List Entry
  base : ℤ
  expired : ℤ
  residues : List Entry

/-- `itYearBase`'s `[...pool].sort((a, b) => a.from - b.from)`: the losses on hand by year, oldest first (a stable
sort, so losses of one year keep their order). -/
def sortPool (pool : List Entry) : List Entry := pool.mergeSort fun a b => decide (a.yr ≤ b.yr)

theorem amt_sortPool (pool : List Entry) : amt (sortPool pool) = amt pool := by
  unfold amt sortPool; exact ((List.mergeSort_perm _ _).map _).sum_eq

/-- A pool already in year order is left as it is. -/
theorem sortPool_of_sorted (pool : List Entry) (h : pool.Pairwise fun a b => a.yr ≤ b.yr) : sortPool pool = pool := by
  unfold sortPool; apply List.mergeSort_of_pairwise; simpa using h

/-- **IT-7** The losses are used oldest first whatever the order they come in: the sorted pool is in year order and
holds the same losses. -/
theorem sortPool_sorted (pool : List Entry) :
    (sortPool pool).Pairwise (fun a b => a.yr ≤ b.yr) ∧ (sortPool pool).Perm pool := by
  refine ⟨?_, List.mergeSort_perm _ _⟩
  have := List.pairwise_mergeSort (le := fun a b : Entry => decide (a.yr ≤ b.yr))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) pool
  simpa [sortPool] using this

/-- One year of `itYears` from its net and the losses on hand: `expired` is what drops out of the pool unused. -/
def yearStep (year : ℕ) (net : ℚ) (pool : List Entry) : YearOut :=
  { gain := yGain year (euros net), loss := yLoss year (euros net),
    used := (use year (yGain year (euros net)) (sortPool pool)).1,
    base := (use year (yGain year (euros net)) (sortPool pool)).2.2,
    expired := amt ((use year (yGain year (euros net)) (sortPool pool)).2.1.filter (fun e => !keep year e)),
    residues := (use year (yGain year (euros net)) (sortPool pool)).2.1.filter (keep year) ++
      (if 0 < yLoss year (euros net) then [⟨year, yLoss year (euros net)⟩] else []) }

/-- `itYears` over (year, net) in year order, from the losses carried in. -/
def runYears : List Entry → List (ℕ × ℚ) → List YearOut
  | _, [] => []
  | pool, y :: ys => yearStep y.1 y.2 pool :: runYears (yearStep y.1 y.2 pool).residues ys

/-- The losses still carried after the last year. -/
def finalPool : List Entry → List (ℕ × ℚ) → List Entry
  | pool, [] => pool
  | pool, y :: ys => finalPool (yearStep y.1 y.2 pool).residues ys

/-- The year's net: the sum of its lines' gains (sales and proventi). -/
def yearNet (ls : List Line) : ℚ := (ls.map Line.gain).sum

/-! ### Rule 5: one figure for the year -/

/-- **IT-5** The year's net is the same whatever the order of its lines. -/
theorem net_any_order (a b : List Line) (h : a.Perm b) : yearNet a = yearNet b := (h.map _).sum_eq

/-- **IT-5** A year has a gain or a loss, never both. -/
theorem gain_or_loss (year : ℕ) (n : ℤ) : yGain year n = 0 ∨ yLoss year n = 0 := by
  unfold yGain yLoss threshold; split_ifs <;> omega

/-! ### Rule 6: the €2,000 threshold in 2023 and 2024 -/

/-- **IT-6** 2023 and 2024: the gain is the part of the net over €2,000, the loss carried the part of the net loss
over €2,000. -/
theorem threshold_2023_24 (year : ℕ) (n : ℤ) (h : year ≤ 2024) :
    yGain year n = max (n - 2000) 0 ∧ yLoss year n = max (-n - 2000) 0 := by
  unfold yGain yLoss threshold; simp only [h, if_true]
  constructor <;> split_ifs <;> omega

/-- **IT-6** From 2025: all of the net gain, and all of the net loss carries. -/
theorem no_threshold_2025 (year : ℕ) (n : ℤ) (h : 2025 ≤ year) :
    yGain year n = max n 0 ∧ yLoss year n = max (-n) 0 := by
  unfold yGain yLoss threshold
  have : ¬ year ≤ 2024 := by omega
  simp only [this, if_false]
  constructor <;> split_ifs <;> omega

/-- The year's base and tax for 2023-2025: 26% of the base, rounded up to the cent. -/
def tax2025 (o : YearOut) : ℚ := centsUp ((o.base : ℚ) * (26 / 100))

/-- **IT-6** Circolare 30/E of 27 October 2023, p. 51: a net loss of €2,500 in 2023 carries €500 (only the part over
€2,000), and nothing is taxed. -/
theorem circolare_p51 :
    (yearStep 2023 (-2500) []).loss = 500 ∧ (yearStep 2023 (-2500) []).residues = [⟨2023, 500⟩] ∧
      (yearStep 2023 (-2500) []).base = 0 := by
  simp [yearStep, yGain, yLoss, threshold, euros, use, keep, sortPool]; norm_num

/-- **IT-6** Agenzia delle Entrate FAQ (the app's test): net gains of €2,500 in 2024 are taxed on the €500 over
€2,000, at 26%: €130. -/
theorem faq_2024 :
    (yearStep 2024 2500 []).gain = 500 ∧ (yearStep 2024 2500 []).base = 500 ∧ tax2025 (yearStep 2024 2500 []) = 130 := by
  simp [yearStep, yGain, yLoss, threshold, euros, use, tax2025, centsUp, sortPool]; norm_num

/-! ### Rule 7: losses carried four years, oldest first, then expire -/

/-- **IT-7** Using losses keeps them whole: what is used plus what is left in the pool is the pool. -/
theorem use_conserves (year : ℕ) (left : ℤ) (pool : List Entry) :
    amt (use year left pool).1 + amt (use year left pool).2.1 = amt pool := by
  induction pool generalizing left with
  | nil => simp [use]
  | cons e es ih =>
    simp only [use]
    split_ifs with h0 h1
    · simp
    · have := ih (left - min e.amount left); simp only [amt_cons]; linarith
    · have := ih left; simp only [amt_cons]; linarith

/-- **IT-8** The base is the gain less the losses used: earlier losses come off before tax. -/
theorem use_base (year : ℕ) (left : ℤ) (pool : List Entry) :
    (use year left pool).2.2 = left - amt (use year left pool).1 := by
  induction pool generalizing left with
  | nil => simp [use]
  | cons e es ih =>
    simp only [use]
    split_ifs with h0 h1
    · simp
    · rw [ih]; simp only [amt_cons]; ring
    · exact ih left

/-- **IT-7** A loss is used only in the four years after its own: every loss used came from a year before and at most
four years back. -/
theorem used_window (year : ℕ) (left : ℤ) (pool : List Entry) :
    ∀ e ∈ (use year left pool).1, e.yr < year ∧ year ≤ e.yr + 4 := by
  induction pool generalizing left with
  | nil => simp [use]
  | cons e es ih =>
    simp only [use]
    split_ifs with h0 h1
    · simp
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨h1.1, h1.2.1⟩
      · exact ih _ x hx
    · exact ih left

/-- **IT-7** Oldest first: when the oldest usable loss covers what is left, only it is used, and every newer loss is
untouched. -/
theorem oldest_first (year : ℕ) (left : ℤ) (e : Entry) (es : List Entry) (hl : 0 < left) (hu : usableIn year e)
    (hc : left ≤ e.amount) :
    use year left (e :: es) = ([⟨e.yr, left⟩], ⟨e.yr, e.amount - left⟩ :: es, 0) := by
  have hm : min e.amount left = left := min_eq_right hc
  cases es with
  | nil => simp [use, not_le.mpr hl, hu, hm]
  | cons f fs => simp [use, not_le.mpr hl, hu, hm]

/-- The losses usable this year, in total. -/
def avail (year : ℕ) (pool : List Entry) : ℤ := amt (pool.filter (fun e => decide (usableIn year e)))

theorem avail_nonneg (year : ℕ) (pool : List Entry) : 0 ≤ avail year pool := by
  induction pool with
  | nil => simp [avail]
  | cons e es ih =>
    unfold avail at ih ⊢
    by_cases h : usableIn year e
    · rw [List.filter_cons_of_pos (by simpa using h)]; simp only [amt_cons]; linarith [h.2.2]
    · rw [List.filter_cons_of_neg (by simpa using h)]; exact ih

/-- **IT-8** Losses come off only down to zero: from a gain `left ≥ 0`, the base is the gain less every usable loss,
never below 0. -/
theorem base_eq (year : ℕ) (left : ℤ) (pool : List Entry) (hl : 0 ≤ left) :
    (use year left pool).2.2 = max (left - avail year pool) 0 := by
  induction pool generalizing left with
  | nil => simp [use, avail, hl]
  | cons e es ih =>
    have ha := avail_nonneg year es
    simp only [use]
    split_ifs with h0 h1
    · have : left = 0 := le_antisymm h0 hl
      subst this
      have := avail_nonneg year (e :: es)
      simp; omega
    · rw [ih _ (by omega)]
      unfold avail
      rw [List.filter_cons_of_pos (by simpa using h1)]
      simp only [amt_cons]
      unfold avail at ha
      rcases le_total e.amount left with h | h
      · rw [min_eq_left h]; congr 1; ring
      · rw [min_eq_right h]; omega
    · rw [ih _ hl]
      unfold avail
      rw [List.filter_cons_of_neg (by simpa using h1)]

theorem filter_split (p : Entry → Bool) (l : List Entry) :
    amt (l.filter p) + amt (l.filter (fun e => !p e)) = amt l := by
  induction l with
  | nil => simp
  | cons e es ih => cases h : p e <;> simp [h] <;> linarith

theorem yLoss_nonneg (year : ℕ) (n : ℤ) : 0 ≤ yLoss year n := by
  unfold yLoss threshold; split_ifs <;> omega

theorem yGain_nonneg (year : ℕ) (n : ℤ) : 0 ≤ yGain year n := by
  unfold yGain threshold; split_ifs <;> omega

/-- **IT-7** One year: the losses on hand plus the year's loss = used + expired + still carried. -/
theorem year_accounts (year : ℕ) (net : ℚ) (pool : List Entry) :
    amt pool + (yearStep year net pool).loss =
      amt (yearStep year net pool).used + (yearStep year net pool).expired + amt (yearStep year net pool).residues := by
  have h1 := use_conserves year (yGain year (euros net)) (sortPool pool)
  have h2 := filter_split (keep year) (use year (yGain year (euros net)) (sortPool pool)).2.1
  have h3 := yLoss_nonneg year (euros net)
  rw [← amt_sortPool pool]
  simp only [yearStep, amt_append]
  split_ifs with h
  · simp; linarith
  · have : yLoss year (euros net) = 0 := by omega
    simp [this]; linarith

/-- **IT-7** Over any run of years, nothing is lost or invented: the losses carried in plus every year's loss = every
loss used + every loss expired + what is still carried. -/
theorem run_accounts (pool : List Entry) (ys : List (ℕ × ℚ)) :
    amt pool + ((runYears pool ys).map YearOut.loss).sum =
      ((runYears pool ys).map fun o => amt o.used + o.expired).sum + amt (finalPool pool ys) := by
  induction ys generalizing pool with
  | nil => simp [runYears, finalPool]
  | cons y ys ih =>
    simp only [runYears, finalPool, List.map_cons, List.sum_cons]
    have := year_accounts y.1 y.2 pool
    have := ih (yearStep y.1 y.2 pool).residues
    linarith

/-- **IT-7** A loss expires only after its fourth year: every loss carried on from the pool is still usable next year,
and every loss dropped with something left could not be used next year. -/
theorem expiry (year : ℕ) (net : ℚ) (pool : List Entry) :
    (∀ e ∈ (use year (yGain year (euros net)) (sortPool pool)).2.1, keep year e = true → year + 1 ≤ e.yr + 4) ∧
    (∀ e ∈ (use year (yGain year (euros net)) (sortPool pool)).2.1, keep year e = false → 0 < e.amount →
      e.yr + 4 < year + 1) := by
  constructor
  · intro e _ h; simp [keep] at h; omega
  · intro e _ h hp; simp [keep, hp] at h; omega

/-- The app's test: a €1,000 loss of 2025 is still carried after 2029 if unused and gone after 2029's return; a 2030
gain of €5,000 is then taxed in full. -/
theorem carry_four_years :
    let ys := runYears [] [(2025, -1000), (2026, 0), (2027, 0), (2028, 0), (2029, 0), (2030, 5000)]
    (ys.map YearOut.residues).take 5 =
        [[⟨2025, 1000⟩], [⟨2025, 1000⟩], [⟨2025, 1000⟩], [⟨2025, 1000⟩], []] ∧
      (ys.map YearOut.base).getLast? = some 5000 := by
  norm_num [runYears, yearStep, yGain, yLoss, threshold, euros, use, keep, sortPool]

/-! ### Rule 8: tax never below 0, more gain never less tax -/

theorem euros_mono (x y : ℚ) (h : x ≤ y) : euros x ≤ euros y := by
  unfold euros
  split_ifs with hx hy hy
  · exact Int.floor_mono (by linarith)
  · linarith
  · have : (0 : ℤ) ≤ ⌊y + 1 / 2⌋ := Int.floor_nonneg.mpr (by linarith)
    have : (0 : ℤ) ≤ ⌊-x + 1 / 2⌋ := Int.floor_nonneg.mpr (by linarith)
    omega
  · have := Int.floor_mono (show -y + 1 / 2 ≤ -x + 1 / 2 by linarith); omega

theorem yGain_mono (year : ℕ) (a b : ℤ) (h : a ≤ b) : yGain year a ≤ yGain year b := by
  unfold yGain; split_ifs <;> omega

theorem centsUp_mono (x y : ℚ) (h : x ≤ y) : centsUp x ≤ centsUp y := by
  unfold centsUp
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact_mod_cast Int.ceil_mono (by linarith)

theorem centsUp_nonneg (x : ℚ) (h : 0 ≤ x) : 0 ≤ centsUp x := by
  unfold centsUp
  apply div_nonneg _ (by norm_num)
  exact_mod_cast Int.ceil_nonneg (by linarith)

/-- **IT-8** The base is never below 0 nor above the year's gain. -/
theorem base_bounds (year : ℕ) (net : ℚ) (pool : List Entry) :
    0 ≤ (yearStep year net pool).base ∧ (yearStep year net pool).base ≤ (yearStep year net pool).gain := by
  simp only [yearStep]
  rw [base_eq _ _ _ (yGain_nonneg _ _)]
  have := avail_nonneg year (sortPool pool)
  have := yGain_nonneg year (euros net)
  constructor <;> omega

/-- **IT-8** The tax (2023-2025) is never below 0. -/
theorem tax_nonneg (year : ℕ) (net : ℚ) (pool : List Entry) : 0 ≤ tax2025 (yearStep year net pool) := by
  unfold tax2025
  apply centsUp_nonneg
  have := (base_bounds year net pool).1
  have : (0 : ℚ) ≤ (yearStep year net pool).base := by exact_mod_cast this
  linarith

/-- **IT-8** More net gain never means less tax, with the same losses on hand. -/
theorem tax_mono (year : ℕ) (a b : ℚ) (pool : List Entry) (h : a ≤ b) :
    tax2025 (yearStep year a pool) ≤ tax2025 (yearStep year b pool) := by
  unfold tax2025
  apply centsUp_mono
  apply mul_le_mul_of_nonneg_right _ (by norm_num)
  simp only [yearStep]
  rw [base_eq _ _ _ (yGain_nonneg _ _), base_eq _ _ _ (yGain_nonneg _ _)]
  have := yGain_mono year _ _ (euros_mono a b h)
  exact_mod_cast (show max (yGain year (euros a) - avail year (sortPool pool)) 0 ≤
      max (yGain year (euros b) - avail year (sortPool pool)) 0
    by omega)

/-! ### Rule 11: rounding -/

/-- **IT-11** `itEuros` is within 50 cents of the exact figure and symmetric about 0. -/
theorem euros_bounds (x : ℚ) : |(euros x : ℚ) - x| ≤ 1 / 2 ∧ euros (-x) = -euros x := by
  unfold euros
  constructor
  · split_ifs with h
    · have h1 := Int.floor_le (x + 1 / 2)
      have h2 := Int.lt_floor_add_one (x + 1 / 2)
      rw [abs_le]; constructor <;> linarith
    · have h1 := Int.floor_le (-x + 1 / 2)
      have h2 := Int.lt_floor_add_one (-x + 1 / 2)
      push_cast
      rw [abs_le]; constructor <;> linarith
  · by_cases h0 : x = 0
    · subst h0; norm_num [Int.floor_eq_iff]
    rcases lt_or_gt_of_ne h0 with h | h
    · rw [if_pos (by linarith), if_neg (by linarith)]; simp
    · rw [if_neg (by linarith), if_pos (by linarith), neg_neg]

/-- **IT-11** 50 cents and over go up: €k.50 is €k + 1 (for k ≥ 0), and €k.49 is €k. -/
theorem euros_half_up (k : ℕ) : euros (k + 1 / 2) = k + 1 ∧ euros (k + 49 / 100) = k := by
  unfold euros
  have h1 : (0 : ℚ) ≤ k + 1 / 2 := by positivity
  have h2 : (0 : ℚ) ≤ k + 49 / 100 := by positivity
  rw [if_pos h1, if_pos h2]
  constructor
  · rw [show (k : ℚ) + 1 / 2 + 1 / 2 = ((k + 1 : ℤ) : ℚ) by push_cast; ring, Int.floor_intCast]
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith

/-- **IT-11** (where the code differs from "tax in whole euros") The net, gain, loss and base are whole euros; the tax
is the base times the rate rounded up to the cent, never below it and less than a cent above. -/
theorem centsUp_bounds (x : ℚ) : x ≤ centsUp x ∧ centsUp x < x + 1 / 100 := by
  unfold centsUp
  have h1 := Int.le_ceil (x * 100)
  have h2 := Int.ceil_lt_add_one (x * 100)
  constructor
  · rw [le_div_iff₀ (by norm_num)]; exact h1
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-! ### Earlier losses (2019-2022; `itEarlierIn`, art. 68 c. 5 TUIR; L. 197/2022 art. 1 c. 127) -/

/-- `itEarlierIn` and the report's filter: the losses the person declared for 2019 to 2022, whole euros, kept only
when above 0 and at most 10^10, in year order. `v y` is the figure given for year `y`. -/
def earlierIn (v : ℕ → ℤ) : List Entry :=
  ([2019, 2020, 2021, 2022].filter fun y => decide (0 < v y ∧ v y ≤ 10 ^ 10)).map fun y => ⟨y, v y⟩

/-- **IT-7** Earlier losses come only from 2019 to 2022, each above 0, in year order (so used oldest first). -/
theorem earlier_years (v : ℕ → ℤ) :
    (∀ e ∈ earlierIn v, 2019 ≤ e.yr ∧ e.yr ≤ 2022 ∧ 0 < e.amount ∧ e.amount = v e.yr) ∧
      (earlierIn v).Pairwise (fun a b => a.yr ≤ b.yr) ∧ sortPool (earlierIn v) = earlierIn v := by
  have hp : (earlierIn v).Pairwise (fun a b => a.yr ≤ b.yr) := by
    unfold earlierIn
    simp only [List.pairwise_map]
    apply List.Pairwise.filter
    decide
  refine ⟨?_, hp, sortPool_of_sorted _ hp⟩
  intro e he
  simp only [earlierIn, List.mem_map, List.mem_filter, decide_eq_true_eq] at he
  obtain ⟨y, ⟨hy, hv, -⟩, rfl⟩ := he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  refine ⟨?_, ?_, hv, rfl⟩ <;> rcases hy with rfl | rfl | rfl | rfl <;> norm_num

/-- **IT-7** The window for an earlier loss: one of year `y` is usable only in the four years after it, so a 2022 loss
up to 2026 at the latest and a 2019 loss only in 2023 (the first year of the regime). -/
theorem earlier_window (e : Entry) (year : ℕ) (h : usableIn year e) : e.yr < year ∧ year ≤ e.yr + 4 :=
  ⟨h.1, h.2.1⟩

/-- The app's tests: in 2023, a net of €8,000 (gain €6,000 over the threshold) with €4,000 of 2019 and €1,000 of 2020
uses both, leaving a base of €1,000 (tax €260); in 2024 a net of €8,000 with €4,000 of 2019 (expired) and €3,000 of
2022 uses only 2022's €3,000. -/
theorem earlier_examples :
    let a := yearStep 2023 8000 (earlierIn fun y => if y = 2019 then 4000 else if y = 2020 then 1000 else 0)
    let b := yearStep 2024 8000 (earlierIn fun y => if y = 2019 then 4000 else if y = 2022 then 3000 else 0)
    a.used = [⟨2019, 4000⟩, ⟨2020, 1000⟩] ∧ a.base = 1000 ∧ tax2025 a = 260 ∧ b.used = [⟨2022, 3000⟩] := by
  have s1 := (earlier_years fun y => if y = 2019 then 4000 else if y = 2020 then 1000 else 0).2.2
  have s2 := (earlier_years fun y => if y = 2019 then 4000 else if y = 2022 then 3000 else 0).2.2
  simp only [yearStep, s1, s2]
  norm_num [earlierIn, yGain, threshold, euros, use, usableIn, tax2025, centsUp]

/-! ### Rule 9: the 2026 rates (L. 207/2024 art. 1 c. 24; euro e-money tokens: L. 199/2025 art. 1 c. 28) -/

/-- The year's net from its euro e-money token lines (`euroEmtNet`). -/
def emtNet (ls : List Line) : ℚ := ((ls.filter Line.euroEmt).map Line.gain).sum

/-- The year's net from its other lines. -/
def otherNet (ls : List Line) : ℚ := ((ls.filter (fun l => !l.euroEmt)).map Line.gain).sum

/-- **IT-9** The euro e-money token part and the rest add up to the year's net. -/
theorem net_split (ls : List Line) : emtNet ls + otherNet ls = yearNet ls := by
  induction ls with
  | nil => simp [emtNet, otherNet, yearNet]
  | cons l ls ih =>
    unfold emtNet otherNet yearNet at *
    cases h : l.euroEmt <;> simp [h] <;> linarith

/-- `itSplit`'s gains (engine/it.ts:373): the euro e-money token net and the other net, each not below 0. -/
def emtPart (e : ℚ) : ℚ := max e 0
def otherPart (net e : ℚ) : ℚ := max (net - e) 0

/-- `itSplit`'s `exactBase` (engine/it.ts:374): the base before the net was rounded, the base plus the net less the
net in whole euros. -/
def exactBase (base : ℤ) (net : ℚ) : ℚ := (base : ℚ) + (net - euros net)

/-- `itSplit`'s `other` (engine/it.ts:375): the part at 33%, `exactBase` shared pro rata to the other gain over all
the gains, never above the base, not rounded; 0 when there is no gain. -/
def other33 (base : ℤ) (net e : ℚ) : ℚ :=
  if emtPart e + otherPart net e ≤ 0 then 0
  else min (base : ℚ) (exactBase base net * otherPart net e / (emtPart e + otherPart net e))

/-- `itSplit`'s exact tax `t` (engine/it.ts:372, 377; rates itRate, engine/it.ts:51-54): to 2025, or with a base not
above 0, 26% of the base; from 2026 26% of the base and 7% (33% less 26%) more on `other33`. -/
def exactTax (year : ℕ) (base : ℤ) (net e : ℚ) : ℚ :=
  if year < 2026 ∨ base ≤ 0 then (base : ℚ) * (26 / 100)
  else (base : ℚ) * (26 / 100) + other33 base net e * (7 / 100)

/-- `itSplit`'s `atOther` (engine/it.ts:378): `other33` in whole euros, never above the base. -/
def atOther (base : ℤ) (net e : ℚ) : ℤ := min (euros (other33 base net e)) base

/-- `itSplit`'s parts as shown, (at 26%, at 33%), whole euros (engine/it.ts:372, 379). To 2025, or with a base not
above 0, all of the base is at 26%. -/
def split (year : ℕ) (base : ℤ) (net e : ℚ) : ℤ × ℤ :=
  if year < 2026 ∨ base ≤ 0 then (base, 0) else (base - atOther base net e, atOther base net e)

/-- `itSplit`'s `tax` (engine/it.ts:372, 379): the exact tax rounded up to the cent (the estimate). -/
def splitTax (year : ℕ) (base : ℤ) (net e : ℚ) : ℚ := centsUp (exactTax year base net e)

/-- `itSplit`'s `form` (engine/it.ts:372, 379): RT89 as filed, the exact tax in whole euros, 50 cents up (`itEuros`,
engine/it.ts:276). -/
def splitForm (year : ℕ) (base : ℤ) (net e : ℚ) : ℤ := euros (exactTax year base net e)

theorem euros_int (n : ℤ) (h : 0 ≤ n) : euros n = n := by
  unfold euros
  rw [if_pos (by exact_mod_cast h), Int.floor_eq_iff]; constructor <;> linarith

@[simp] theorem euros_zero : euros 0 = 0 := by simpa using euros_int 0 le_rfl

theorem euros_nonneg (x : ℚ) (h : 0 ≤ x) : 0 ≤ euros x := by
  have := euros_mono 0 x h; rwa [euros_zero] at this

/-- `euros` moves by whole euros: for `x ≥ 0`, adding `n` euros adds `n`. -/
theorem euros_add_int (x : ℚ) (n : ℤ) (hx : 0 ≤ x) (hn : 0 ≤ n) : euros (x + n) = euros x + n := by
  unfold euros
  have : (0 : ℚ) ≤ n := by exact_mod_cast hn
  rw [if_pos (by linarith), if_pos hx, show x + n + 1 / 2 = (x + 1 / 2) + (n : ℚ) by ring, Int.floor_add_intCast]

/-- `exactBase` is within 50 cents of the base. -/
theorem exactBase_bounds (base : ℤ) (net : ℚ) :
    (base : ℚ) - 1 / 2 ≤ exactBase base net ∧ exactBase base net ≤ (base : ℚ) + 1 / 2 := by
  obtain ⟨h1, h2⟩ := abs_le.mp (euros_bounds net).1
  unfold exactBase; constructor <;> linarith

theorem other33_bounds (base : ℤ) (net e : ℚ) (hb : 0 < base) :
    0 ≤ other33 base net e ∧ other33 base net e ≤ base := by
  have hb' : (1 : ℚ) ≤ base := by exact_mod_cast hb
  have hB := (exactBase_bounds base net).1
  have he : 0 ≤ emtPart e := le_max_right _ _
  have ho : 0 ≤ otherPart net e := le_max_right _ _
  unfold other33
  split_ifs with h
  · exact ⟨le_rfl, by linarith⟩
  · exact ⟨le_min (by linarith) (div_nonneg (mul_nonneg (by linarith) ho) (by linarith)), min_le_left _ _⟩

theorem atOther_bounds (base : ℤ) (net e : ℚ) (hb : 0 < base) : 0 ≤ atOther base net e ∧ atOther base net e ≤ base :=
  ⟨le_min (euros_nonneg _ (other33_bounds base net e hb).1) hb.le, min_le_right _ _⟩

/-- From 2026, with a base above 0, the exact tax is 26% of the base and 7% more on the part at 33%. -/
theorem exactTax_eq (year : ℕ) (base : ℤ) (net e : ℚ) (hy : 2026 ≤ year) (hb : 0 < base) :
    exactTax year base net e = (base : ℚ) * (26 / 100) + other33 base net e * (7 / 100) := by
  unfold exactTax; rw [if_neg (by omega)]

/-- **IT-9** The exact tax is between 26% and 33% of the base. -/
theorem exactTax_between (year : ℕ) (base : ℤ) (net e : ℚ) (hb : 0 ≤ base) :
    (base : ℚ) * (26 / 100) ≤ exactTax year base net e ∧ exactTax year base net e ≤ (base : ℚ) * (33 / 100) := by
  have hb' : (0 : ℚ) ≤ base := by exact_mod_cast hb
  unfold exactTax
  split_ifs with h
  · constructor <;> linarith
  · have := other33_bounds base net e (by omega)
    constructor <;> linarith

/-- **IT-9** The parts add up to the base and, for a base not below 0, neither is below 0. -/
theorem split_parts (year : ℕ) (base : ℤ) (net e : ℚ) (hb : 0 ≤ base) :
    (split year base net e).1 + (split year base net e).2 = base ∧ 0 ≤ (split year base net e).1 ∧
      0 ≤ (split year base net e).2 := by
  unfold split
  split_ifs with h
  · exact ⟨by simp, hb, le_rfl⟩
  · have := atOther_bounds base net e (by omega)
    dsimp only
    exact ⟨by omega, by omega, this.1⟩

/-- **IT-9** To 2025 the tax is 26% of the base: the estimate rounded up to the cent, RT89 in whole euros. -/
theorem split_before_2026 (year : ℕ) (base : ℤ) (net e : ℚ) (h : year ≤ 2025) :
    splitTax year base net e = centsUp ((base : ℚ) * (26 / 100)) ∧
      splitForm year base net e = euros ((base : ℚ) * (26 / 100)) := by
  unfold splitTax splitForm exactTax; rw [if_pos (Or.inl (by omega))]; exact ⟨rfl, rfl⟩

/-- **IT-9** From 2026, with a base above 0 and a gain: the part at 33% is the base before the net was rounded
(`exactBase`) times the other gain over all the gains (each not below 0), never above the base, not rounded; the tax
is 26% of the base and 7% more on that part; the part at 33% shown is that part in whole euros (within 50 cents of
it) and the part at 26% shown is the rest of the base. -/
theorem split_prop (year : ℕ) (base : ℤ) (net e : ℚ) (hy : 2026 ≤ year) (hb : 0 < base)
    (hg : 0 < emtPart e + otherPart net e) :
    other33 base net e = min (base : ℚ) (exactBase base net * otherPart net e / (emtPart e + otherPart net e)) ∧
      exactTax year base net e = (base : ℚ) * (26 / 100) + other33 base net e * (7 / 100) ∧
      (split year base net e).2 = euros (other33 base net e) ∧
      (split year base net e).1 = base - (split year base net e).2 ∧
      |((split year base net e).2 : ℚ) - other33 base net e| ≤ 1 / 2 := by
  have hp : other33 base net e =
      min (base : ℚ) (exactBase base net * otherPart net e / (emtPart e + otherPart net e)) := by
    unfold other33; rw [if_neg (by linarith)]
  have hr : euros (other33 base net e) ≤ base := by
    have := euros_mono _ _ (other33_bounds base net e hb).2; rwa [euros_int base hb.le] at this
  have hn : ¬ (year < 2026 ∨ base ≤ 0) := by omega
  have h2 : (split year base net e).2 = euros (other33 base net e) := by
    simp only [split, if_neg hn, atOther]; exact min_eq_left hr
  refine ⟨hp, exactTax_eq year base net e hy hb, h2, ?_, h2 ▸ (euros_bounds _).1⟩
  simp only [split, if_neg hn]

/-- **IT-9** From 2026, with a base above 0, no euro e-money token gain and a net above 0, the part at 33% is the base
before rounding (never above the base): the tax is within 7% of 50 cents below 33% of the base, and exactly 33% of it
when the net is in whole euros. -/
theorem split_no_emt (year : ℕ) (base : ℤ) (net e : ℚ) (hy : 2026 ≤ year) (hb : 0 < base) (he : e ≤ 0)
    (hn : 0 < net) :
    (base : ℚ) * (33 / 100) - 7 / 200 ≤ exactTax year base net e ∧ exactTax year base net e ≤ (base : ℚ) * (33 / 100) ∧
      ((euros net : ℚ) = net → exactTax year base net e = (base : ℚ) * (33 / 100)) := by
  have h0 : emtPart e = 0 := max_eq_right he
  have ho : otherPart net e = net - e := max_eq_left (by linarith)
  have hpos : 0 < net - e := by linarith
  have hO : other33 base net e = min (base : ℚ) (exactBase base net) := by
    unfold other33; rw [h0, ho, zero_add, if_neg (by linarith), mul_div_assoc, div_self hpos.ne', mul_one]
  have hB := exactBase_bounds base net
  rw [exactTax_eq _ _ _ _ hy hb, hO]
  refine ⟨?_, ?_, fun hw => ?_⟩
  · have : (base : ℚ) - 1 / 2 ≤ min (base : ℚ) (exactBase base net) := le_min (by linarith) hB.1
    linarith
  · have := min_le_left (base : ℚ) (exactBase base net); linarith
  · have : exactBase base net = base := by unfold exactBase; rw [hw]; ring
    rw [this, min_self]; ring

/-- **IT-9** From 2026, when all the gain is the euro e-money token's (a gain, and no other gain), the whole base is
at 26%. -/
theorem split_all_emt (year : ℕ) (base : ℤ) (net e : ℚ) (he : 0 < e) (hn : net ≤ e) :
    exactTax year base net e = (base : ℚ) * (26 / 100) ∧ splitTax year base net e = centsUp ((base : ℚ) * (26 / 100)) := by
  have h2 : otherPart net e = 0 := max_eq_right (by linarith)
  have h : exactTax year base net e = (base : ℚ) * (26 / 100) := by
    unfold exactTax
    split_ifs with hc
    · rfl
    · have hb : (0 : ℚ) ≤ base := by exact_mod_cast (show 0 ≤ base by omega)
      have : other33 base net e = 0 := by
        unfold other33; rw [h2]
        split_ifs
        · rfl
        · rw [mul_zero, zero_div]; exact min_eq_right hb
      rw [this]; ring
  exact ⟨h, by unfold splitTax; rw [h]⟩

/-- **IT-9** The tax is between 26% and 33% of the base (each rounded up to the cent). -/
theorem split_between (year : ℕ) (base : ℤ) (net e : ℚ) (hb : 0 ≤ base) :
    centsUp ((base : ℚ) * (26 / 100)) ≤ splitTax year base net e ∧
      splitTax year base net e ≤ centsUp ((base : ℚ) * (33 / 100)) :=
  ⟨centsUp_mono _ _ (exactTax_between year base net e hb).1, centsUp_mono _ _ (exactTax_between year base net e hb).2⟩

/-- **IT-9** RT89 is the exact tax in whole euros, 50 cents up: ⌊t + 1/2⌋ (the tax is never below 0 for a base not
below 0). -/
theorem form_half_up (year : ℕ) (base : ℤ) (net e : ℚ) (hb : 0 ≤ base) :
    splitForm year base net e = ⌊exactTax year base net e + 1 / 2⌋ := by
  have := (exactTax_between year base net e hb).1
  have hb' : (0 : ℚ) ≤ base := by exact_mod_cast hb
  unfold splitForm euros; rw [if_pos (by linarith)]

theorem other33_base_mono (a b : ℤ) (net e : ℚ) (ha : 0 < a) (hab : a ≤ b) :
    other33 a net e ≤ other33 b net e := by
  have hab' : (a : ℚ) ≤ b := by exact_mod_cast hab
  unfold other33
  split_ifs with h
  · exact le_rfl
  · push_neg at h
    apply min_le_min hab'
    apply div_le_div_of_nonneg_right _ h.le
    apply mul_le_mul_of_nonneg_right _ (le_max_right _ _)
    unfold exactBase; linarith

/-- **IT-9** A bigger base with the same net and euro e-money token net never means less tax: neither the exact tax,
the estimate nor RT89. -/
theorem split_base_mono (year : ℕ) (a b : ℤ) (net e : ℚ) (ha : 0 ≤ a) (hab : a ≤ b) :
    exactTax year a net e ≤ exactTax year b net e ∧ splitTax year a net e ≤ splitTax year b net e ∧
      splitForm year a net e ≤ splitForm year b net e := by
  have hab' : (a : ℚ) ≤ b := by exact_mod_cast hab
  have key : exactTax year a net e ≤ exactTax year b net e := by
    rcases eq_or_lt_of_le ha with h0 | hpos
    · subst h0
      have h1 : exactTax year 0 net e = 0 := by unfold exactTax; rw [if_pos (Or.inr le_rfl)]; simp
      have := (exactTax_between year b net e hab).1
      have hb' : (0 : ℚ) ≤ b := by exact_mod_cast hab
      rw [h1]; linarith
    · by_cases hy : year < 2026
      · unfold exactTax; rw [if_pos (Or.inl hy), if_pos (Or.inl hy)]; linarith
      · rw [exactTax_eq _ _ _ _ (by omega) hpos, exactTax_eq _ _ _ _ (by omega) (by omega)]
        have := other33_base_mono a b net e hpos hab; linarith
  exact ⟨key, centsUp_mono _ _ key, euros_mono _ _ key⟩

/-- **IT-9** A pending token's lines that net to a gain `p ≥ 0`, counted as euro e-money token lines (a statement
dated on or before them), never raise the tax, neither the estimate nor RT89: the same net and base with more of it
at 26%. -/
theorem statement_gain_less_tax (year : ℕ) (base : ℤ) (net e p : ℚ) (hb : 0 ≤ base) (hp : 0 ≤ p) :
    splitTax year base net (e + p) ≤ splitTax year base net e ∧ splitForm year base net (e + p) ≤ splitForm year base net e := by
  have key : exactTax year base net (e + p) ≤ exactTax year base net e := by
    unfold exactTax
    split_ifs with hy
    · exact le_rfl
    · suffices other33 base net (e + p) ≤ other33 base net e by linarith
      have hpos : 0 < base := by omega
      have hb1 : (1 : ℚ) ≤ base := by exact_mod_cast hpos
      have hB : 0 ≤ exactBase base net := by have := (exactBase_bounds base net).1; linarith
      have hE : emtPart e ≤ emtPart (e + p) := max_le_max (by linarith) le_rfl
      have hO : otherPart net (e + p) ≤ otherPart net e := max_le_max (by linarith) le_rfl
      have he : 0 ≤ emtPart e := le_max_right _ _
      have ho : 0 ≤ otherPart net e := le_max_right _ _
      have hO' : 0 ≤ otherPart net (e + p) := le_max_right _ _
      have hE' : 0 ≤ emtPart (e + p) := le_max_right _ _
      unfold other33
      by_cases h2 : emtPart (e + p) + otherPart net (e + p) ≤ 0
      · rw [if_pos h2]
        split_ifs
        · exact le_rfl
        · exact le_min (by linarith) (div_nonneg (mul_nonneg hB ho) (by linarith))
      · rw [if_neg h2]
        by_cases h1 : emtPart e + otherPart net e ≤ 0
        · have h0 : otherPart net (e + p) = 0 := by linarith
          rw [if_pos h1, h0, mul_zero, zero_div]; exact min_le_right _ _
        · rw [if_neg h1]
          push_neg at h1 h2
          apply min_le_min le_rfl
          rw [mul_div_assoc, mul_div_assoc]
          apply mul_le_mul_of_nonneg_left _ hB
          rw [div_le_div_iff₀ h2 h1]
          nlinarith [mul_le_mul hO hE he ho]
  exact ⟨centsUp_mono _ _ key, euros_mono _ _ key⟩

/-! #### A larger gain in either part never gives less tax -/

/-- The other gain's share of all the gains, for an other net `o` and a euro e-money token net `x` (each part's gain
not below 0; 0 when there is no gain). -/
def rat (o x : ℚ) : ℚ := if max x 0 + max o 0 ≤ 0 then 0 else max o 0 / (max x 0 + max o 0)

theorem rat_nonneg (o x : ℚ) : 0 ≤ rat o x := by
  unfold rat
  split_ifs with h
  · exact le_rfl
  · push_neg at h; exact div_nonneg (le_max_right _ _) h.le

/-- `other33` for a net that is the other net `o` plus the euro e-money token net `x`. -/
theorem other33_rat (b : ℤ) (o x : ℚ) (hb : 0 ≤ b) :
    other33 b (o + x) x = min (b : ℚ) (exactBase b (o + x) * rat o x) := by
  have h : otherPart (o + x) x = max o 0 := by unfold otherPart; rw [add_sub_cancel_right]
  unfold other33 rat; rw [h]; unfold emtPart
  split_ifs with hg
  · rw [mul_zero]; exact (min_eq_right (by exact_mod_cast hb)).symm
  · rw [mul_div_assoc]

theorem rat_mono_o (o1 o2 x : ℚ) (ho : o1 ≤ o2) : rat o1 x ≤ rat o2 x := by
  have hm : max o1 0 ≤ max o2 0 := max_le_max ho le_rfl
  have h1 := le_max_right o1 0
  have hx := le_max_right x 0
  unfold rat
  split_ifs with g1 g2 g2
  · exact le_rfl
  · push_neg at g2; exact div_nonneg (le_max_right _ _) g2.le
  · push_neg at g1; linarith
  · push_neg at g1 g2
    rw [div_le_div_iff₀ g1 g2]; nlinarith [mul_le_mul_of_nonneg_left hm hx]

/-- More other gain: the base before rounding less `c`, times the other gain's share, does not fall. -/
theorem share_mono_o (o1 o2 x c : ℚ) (ho : o1 ≤ o2) (hd : 0 ≤ o1 + x - c) :
    (o1 + x - c) * rat o1 x ≤ (o2 + x - c) * rat o2 x :=
  mul_le_mul (by linarith) (rat_mono_o o1 o2 x ho) (rat_nonneg _ _) (by linarith)

/-- More euro e-money token gain: the share falls but the net rises at least as much, so `(o + x − c) × share` does
not fall (for `c ≥ 0`). -/
theorem share_mono_x (o x1 x2 c : ℚ) (hx : x1 ≤ x2) (hc : 0 ≤ c) :
    (o + x1 - c) * rat o x1 ≤ (o + x2 - c) * rat o x2 := by
  by_cases ho : o ≤ 0
  · have h0 : ∀ x, rat o x = 0 := by
      intro x; unfold rat; rw [max_eq_right ho, add_zero]
      split_ifs
      · rfl
      · simp
    rw [h0, h0]; simp
  · push_neg at ho
    have hr : ∀ x, rat o x = o / (max x 0 + o) := by
      intro x; unfold rat; rw [max_eq_left ho.le, if_neg (by linarith [le_max_right x 0])]
    have g1 : 0 < max x1 0 + o := by linarith [le_max_right x1 0]
    have g2 : 0 < max x2 0 + o := by linarith [le_max_right x2 0]
    rw [hr, hr, ← mul_div_assoc, ← mul_div_assoc, div_le_div_iff₀ g1 g2]
    suffices h : (o + x1 - c) * (max x2 0 + o) ≤ (o + x2 - c) * (max x1 0 + o) by
      nlinarith [mul_le_mul_of_nonneg_left h ho.le]
    rcases le_total x2 0 with h2 | h2
    · rw [max_eq_right h2, max_eq_right (le_trans hx h2)]; nlinarith [mul_le_mul_of_nonneg_left hx ho.le]
    · rw [max_eq_left h2]
      rcases le_total x1 0 with h1 | h1
      · rw [max_eq_right h1]
        nlinarith [mul_nonneg (neg_nonneg.mpr h1) (show 0 ≤ x2 + o by linarith), mul_nonneg hc h2]
      · rw [max_eq_left h1]; nlinarith [mul_le_mul_of_nonneg_left hx hc]

/-- From 2026, for bases above 0 that are each net less the same `c ≥ 0` before rounding: no less tax for a larger
other net and a larger euro e-money token net. -/
theorem exact_step (year : ℕ) (b1 b2 : ℤ) (c o1 o2 x1 x2 : ℚ) (hy : 2026 ≤ year) (hp : 0 < b1) (h12 : b1 ≤ b2)
    (hc : 0 ≤ c) (ho : o1 ≤ o2) (hx : x1 ≤ x2)
    (hE1 : exactBase b1 (o1 + x1) = o1 + x1 - c) (hE2 : exactBase b2 (o2 + x2) = o2 + x2 - c) :
    exactTax year b1 (o1 + x1) x1 ≤ exactTax year b2 (o2 + x2) x2 := by
  have hb1 : (1 : ℚ) ≤ b1 := by exact_mod_cast hp
  have h12' : (b1 : ℚ) ≤ b2 := by exact_mod_cast h12
  have hd : 0 ≤ o1 + x1 - c := by have := (exactBase_bounds b1 (o1 + x1)).1; linarith
  rw [exactTax_eq _ _ _ _ hy hp, exactTax_eq _ _ _ _ hy (by omega), other33_rat _ _ _ hp.le,
    other33_rat _ _ _ (by omega), hE1, hE2]
  have s1 := share_mono_o o1 o2 x1 c ho hd
  have s2 := share_mono_x o2 x1 x2 c hx hc
  have := min_le_min h12' (s1.trans s2)
  linarith

/-- The base above 0 from a net and `A` of losses: the net in whole euros less the threshold and `A`, so the base
before rounding is the net less the threshold and `A` (for `A ≥ 0`). -/
theorem exactBase_gbase (year : ℕ) (A : ℤ) (hA : 0 ≤ A) (n : ℚ) (h : 0 < max (yGain year (euros n) - A) 0) :
    exactBase (max (yGain year (euros n) - A) 0) n = n - (threshold year + A) := by
  have : max (yGain year (euros n) - A) 0 = euros n - threshold year - A := by
    rcases max_cases (yGain year (euros n) - A) 0 with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1] at h ⊢; unfold yGain at h ⊢; split_ifs at h ⊢ <;> omega
    · rw [h1] at h; omega
  unfold exactBase; rw [this]; push_cast; ring

/-- **IT-9** With the same losses `A ≥ 0` taken off (the base is the gain over the threshold in whole euros less `A`,
not below 0): a larger other net `o` and a larger euro e-money token net `x` (the net `o + x`) never give a lower exact
tax. -/
theorem exact_gain_mono (year : ℕ) (A : ℤ) (hA : 0 ≤ A) (o1 o2 x1 x2 : ℚ) (ho : o1 ≤ o2) (hx : x1 ≤ x2) :
    exactTax year (max (yGain year (euros (o1 + x1)) - A) 0) (o1 + x1) x1 ≤
      exactTax year (max (yGain year (euros (o2 + x2)) - A) 0) (o2 + x2) x2 := by
  have hn : euros (o1 + x1) ≤ euros (o2 + x2) := euros_mono _ _ (by linarith)
  have hg := yGain_mono year _ _ hn
  have h12 : max (yGain year (euros (o1 + x1)) - A) 0 ≤ max (yGain year (euros (o2 + x2)) - A) 0 :=
    max_le_max (by omega) le_rfl
  have h0 : 0 ≤ max (yGain year (euros (o1 + x1)) - A) 0 := le_max_right _ _
  have h12' : ((max (yGain year (euros (o1 + x1)) - A) 0 : ℤ) : ℚ) ≤ max (yGain year (euros (o2 + x2)) - A) 0 := by
    exact_mod_cast h12
  by_cases hy : year < 2026
  · unfold exactTax; rw [if_pos (Or.inl hy), if_pos (Or.inl hy)]; linarith
  rcases eq_or_lt_of_le h0 with hz | hpos
  · have := (exactTax_between year _ (o2 + x2) x2 (le_trans h0 h12)).1
    have hb2 : (0 : ℚ) ≤ ((max (yGain year (euros (o2 + x2)) - A) 0 : ℤ) : ℚ) := by exact_mod_cast le_trans h0 h12
    have e0 : exactTax year (max (yGain year (euros (o1 + x1)) - A) 0) (o1 + x1) x1 = 0 := by
      unfold exactTax; rw [if_pos (Or.inr hz.symm.le), ← hz]; simp
    rw [e0]; linarith
  · have hT : 0 ≤ threshold year := by unfold threshold; split_ifs <;> norm_num
    exact exact_step year _ _ _ o1 o2 x1 x2 (by omega) hpos h12
      (by exact_mod_cast (show 0 ≤ threshold year + A by omega)) ho hx
      (exactBase_gbase year A hA _ hpos) (exactBase_gbase year A hA _ (lt_of_lt_of_le hpos h12))

/-- The same with the euro e-money token net fixed: a larger net never gives a lower exact tax. -/
theorem exact_net_mono (year : ℕ) (A : ℤ) (hA : 0 ≤ A) (n1 n2 e : ℚ) (h : n1 ≤ n2) :
    exactTax year (max (yGain year (euros n1) - A) 0) n1 e ≤ exactTax year (max (yGain year (euros n2) - A) 0) n2 e := by
  have := exact_gain_mono year A hA (n1 - e) (n2 - e) e e (by linarith) le_rfl
  rwa [sub_add_cancel, sub_add_cancel] at this

/-- The app's tests (2026, with a €10,000 loss of 2025 carried): €10,000 of gain on BTC and €10,000 on EURCV, base
€10,000, €5,000 at 26% and €5,000 at 33%: €2,950. BTC +€10,000 and EURCV −€2,000: base €8,000, all at 33%: €2,640.
BTC €3,000 and EURCV €1,000 with €2,000 of 2024 losses: base €2,000, €500 at 26%, €1,500 at 33%: €625. RT89 shows
the same in whole euros. -/
theorem split_examples :
    split 2026 10000 20000 10000 = (5000, 5000) ∧ splitTax 2026 10000 20000 10000 = 2950 ∧
      splitForm 2026 10000 20000 10000 = 2950 ∧
      split 2026 8000 8000 (-2000) = (0, 8000) ∧ splitTax 2026 8000 8000 (-2000) = 2640 ∧
      split 2026 2000 4000 1000 = (500, 1500) ∧ splitTax 2026 2000 4000 1000 = 625 ∧
      splitForm 2026 2000 4000 1000 = 625 := by
  norm_num [split, splitTax, splitForm, exactTax, other33, exactBase, atOther, emtPart, otherPart, euros, centsUp,
    Int.floor_eq_iff, Int.ceil_eq_iff]

/-- **IT-9** RT89 rounds 50 cents up: a base of €25 to 2025 is €6.50 of tax, €7 on RT89; €6.49 would be €6. -/
theorem form_examples :
    splitTax 2025 25 25 0 = 13 / 2 ∧ splitForm 2025 25 25 0 = 7 ∧ euros (649 / 100) = 6 := by
  norm_num [splitTax, splitForm, exactTax, euros, centsUp, Int.floor_eq_iff, Int.ceil_eq_iff]

/-- Finding (where a statement raises the tax): €10,000 of gain on EURCV, €2,000 on BTC and a €2,000 loss on EURC, a
base of €10,000 in 2026. With a statement for EURC dated after the loss, the euro e-money token net is €10,000 and
the other net €0: €2,600. With one dated before it, the EURC loss joins the euro e-money token net (€8,000), the BTC
gain stays (€2,000): €8,000 at 26% and €2,000 at 33%, €2,740. So a later statement date can lower the tax. -/
theorem later_statement_can_lower_tax :
    splitTax 2026 10000 10000 10000 = 2600 ∧ splitTax 2026 10000 10000 8000 = 2740 := by
  norm_num [splitTax, exactTax, other33, exactBase, emtPart, otherPart, euros, centsUp, Int.floor_eq_iff,
    Int.ceil_eq_iff]
/-! ## Rule 15: tax if sold today (`itYearTax`, `itTaxOnSale`) -/

/-- `itYearTax` (engine/it.ts:386-390): the year's tax from its net so far, the losses carried in (as one loss of last year) and the euro
e-money token net so far, shared as `itSplit` does. -/
def yearTax (year : ℕ) (net : ℚ) (carried : ℤ) (e : ℚ) : ℚ :=
  splitTax year (use year (yGain year (euros net)) (if 0 < carried then [⟨year - 1, carried⟩] else [])).2.2 net e

/-- `itTaxOnSale` (engine/it.ts:396-398): the rise in the year's tax from one more sale (its gain, and its part that is a euro e-money
token's), never below 0. -/
def taxOnSale (year : ℕ) (gain sofar : ℚ) (carried : ℤ) (eSo eGain : ℚ) : ℚ :=
  max (yearTax year (sofar + gain) carried (eSo + eGain) - yearTax year sofar carried eSo) 0

theorem avail_sortPool (year : ℕ) (pool : List Entry) : avail year (sortPool pool) = avail year pool := by
  unfold avail amt sortPool
  exact (((List.mergeSort_perm pool _).filter _).map _).sum_eq

/-- **IT-9** With the same losses carried in (any pool): a larger other net `o` and a larger euro e-money token net `x`
(the year's net `o + x`) never give less tax: neither the exact tax, the estimate nor RT89. -/
theorem gain_mono (year : ℕ) (pool : List Entry) (o1 o2 x1 x2 : ℚ) (ho : o1 ≤ o2) (hx : x1 ≤ x2) :
    exactTax year (yearStep year (o1 + x1) pool).base (o1 + x1) x1 ≤
        exactTax year (yearStep year (o2 + x2) pool).base (o2 + x2) x2 ∧
      splitTax year (yearStep year (o1 + x1) pool).base (o1 + x1) x1 ≤
        splitTax year (yearStep year (o2 + x2) pool).base (o2 + x2) x2 ∧
      splitForm year (yearStep year (o1 + x1) pool).base (o1 + x1) x1 ≤
        splitForm year (yearStep year (o2 + x2) pool).base (o2 + x2) x2 := by
  have key : exactTax year (yearStep year (o1 + x1) pool).base (o1 + x1) x1 ≤
      exactTax year (yearStep year (o2 + x2) pool).base (o2 + x2) x2 := by
    simp only [yearStep]
    rw [base_eq _ _ _ (yGain_nonneg _ _), base_eq _ _ _ (yGain_nonneg _ _), avail_sortPool]
    exact exact_gain_mono year _ (avail_nonneg _ _) o1 o2 x1 x2 ho hx
  exact ⟨key, centsUp_mono _ _ key, euros_mono _ _ key⟩

/-- **IT-15** With the same losses carried in: a larger other net and a larger euro e-money token net never give a
lower `itYearTax`. -/
theorem yearTax_gain_mono (year : ℕ) (carried : ℤ) (o1 o2 x1 x2 : ℚ) (ho : o1 ≤ o2) (hx : x1 ≤ x2) :
    yearTax year (o1 + x1) carried x1 ≤ yearTax year (o2 + x2) carried x2 := by
  unfold yearTax splitTax
  rw [base_eq _ _ _ (yGain_nonneg _ _), base_eq _ _ _ (yGain_nonneg _ _)]
  exact centsUp_mono _ _ (exact_gain_mono year _ (avail_nonneg _ _) o1 o2 x1 x2 ho hx)

theorem yearTax_mono (year : ℕ) (a b : ℚ) (carried : ℤ) (e : ℚ) (h : a ≤ b) :
    yearTax year a carried e ≤ yearTax year b carried e := by
  have := yearTax_gain_mono year carried (a - e) (b - e) e e (by linarith) le_rfl
  rwa [sub_add_cancel, sub_add_cancel] at this

/-- The base of `itYearTax`'s year with `c ≥ 0` carried in as one loss of last year. -/
theorem yearTax_base (year : ℕ) (g c : ℤ) (hy : 1 ≤ year) (hg : 0 ≤ g) (hc : 0 ≤ c) :
    (use year g (if 0 < c then [⟨year - 1, c⟩] else [])).2.2 = max (g - c) 0 := by
  rw [base_eq year g _ hg]
  by_cases h : 0 < c
  · rw [if_pos h]
    have : avail year [⟨year - 1, c⟩] = c := by
      simp only [avail, List.filter_cons, List.filter_nil]
      rw [if_pos (by simp only [decide_eq_true_eq]; exact ⟨show year - 1 < year by omega, show year ≤ year - 1 + 4 by omega, h⟩)]; simp
    rw [this]
  · rw [if_neg h, show c = 0 by omega]; simp [avail]

/-- **IT-15** More losses carried in never mean more tax: the year's tax is antitone in what is carried. -/
theorem yearTax_carried (year : ℕ) (net : ℚ) (c1 c2 : ℤ) (e : ℚ) (hy : 1 ≤ year) (h1 : 0 ≤ c1) (h12 : c1 ≤ c2) :
    yearTax year net c2 e ≤ yearTax year net c1 e := by
  unfold yearTax
  have hg := yGain_nonneg year (euros net)
  rw [yearTax_base year _ c2 hy hg (by omega), yearTax_base year _ c1 hy hg h1]
  exact (split_base_mono year _ _ net e (le_max_right _ _) (max_le_max (by omega) le_rfl)).2.1

/-- **IT-15** Tax if sold today is the year's tax with the sale less without it, never below 0: for a sale that is not
a euro e-money token's, exactly that rise for a sale at a gain (or break-even), and 0 for a sale at a loss. -/
theorem tax_on_sale (year : ℕ) (gain sofar : ℚ) (carried : ℤ) (eSo : ℚ) :
    0 ≤ taxOnSale year gain sofar carried eSo 0 ∧
      (0 ≤ gain → taxOnSale year gain sofar carried eSo 0 =
        yearTax year (sofar + gain) carried eSo - yearTax year sofar carried eSo) ∧
      (gain ≤ 0 → taxOnSale year gain sofar carried eSo 0 = 0) := by
  refine ⟨le_max_right _ _, fun h => ?_, fun h => ?_⟩
  · have := yearTax_mono year sofar (sofar + gain) carried eSo (by linarith)
    unfold taxOnSale; rw [add_zero]; exact max_eq_left (by linarith)
  · have := yearTax_mono year (sofar + gain) sofar carried eSo (by linarith)
    unfold taxOnSale; rw [add_zero]; exact max_eq_right (by linarith)

/-- The app's tests: in 2024, €1,500 of net gains so far and a sale at €1,000 more: €130 (26% of €500 over €2,000).
In 2026, a €1,000 gain on a euro e-money token: €260 (the year's tax with it alone is €260 too); a €1,000 gain on BTC
after €600 on a euro e-money token: €330. With €10,000 of 2025 losses, €20,000 of gains half on EURCV: €2,950. -/
theorem tax_on_sale_examples :
    taxOnSale 2024 1000 1500 0 0 0 = 130 ∧ taxOnSale 2026 1000 0 0 0 1000 = 260 ∧ yearTax 2026 1000 0 1000 = 260 ∧
      taxOnSale 2026 1000 600 0 600 0 = 330 ∧ yearTax 2026 20000 10000 10000 = 2950 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [taxOnSale, yearTax, yGain, threshold, euros, use, usableIn, splitTax, exactTax, other33, exactBase,
      emtPart, otherPart, centsUp, Int.floor_eq_iff, Int.ceil_eq_iff]

/-- The app's tests (2026, no losses) for a larger gain in either part: €1,000 of other gain and €547.50 on a euro
e-money token make a base of €1,548, an estimate of €472.48 and €472 on RT89; €548 on the token, the same base and
€472. €9 of other gain and €1.50 on the token (base €11), RT89 €3; €2 on the token, €3. €499.50 of other gain and
€500.25 on the token, an estimate of €294.97; €500.75 on the token, €294.97. -/
theorem split_rounding_examples :
    (yearStep 2026 (3095 / 2) []).base = 1548 ∧ (yearStep 2026 1548 []).base = 1548 ∧
      splitTax 2026 1548 (3095 / 2) (1095 / 2) = 11812 / 25 ∧
      splitForm 2026 1548 (3095 / 2) (1095 / 2) = 472 ∧ splitForm 2026 1548 1548 548 = 472 ∧
      (yearStep 2026 (21 / 2) []).base = 11 ∧ (yearStep 2026 11 []).base = 11 ∧
      splitForm 2026 11 (21 / 2) (3 / 2) = 3 ∧ splitForm 2026 11 11 2 = 3 ∧
      yearTax 2026 (3999 / 4) 0 (2001 / 4) = 29497 / 100 ∧ yearTax 2026 (4001 / 4) 0 (2003 / 4) = 29497 / 100 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [yearStep, yearTax, sortPool, yGain, threshold, euros, use, splitTax, splitForm, exactTax, other33,
      exactBase, emtPart, otherPart, centsUp, Int.floor_eq_iff, Int.ceil_eq_iff]

/-! ## Rule 16: the readings of the pending euro tokens and the years as shown (report/it.ts:212-229, 499-536) -/

/-- **IT-16** A reading that takes token `t` as a euro e-money token (report/it.ts:221-222: a statement dated
2024-06-30, `d0` here, in place of the person's own for `t`): from `d0` on every movement of `t` is a euro e-money
token's, and every other token is as the person's statements make it. -/
theorem assumed_every_day (pend : ℕ → Bool) (st : Statements) (t d0 day : ℕ) (m : Mv) (hd : d0 ≤ day) :
    (m.tok = some t → euroIn pend ((t, d0) :: st.filter (fun s => s.1 != t)) day m = true) ∧
      (m.tok ≠ some t → euroIn pend ((t, d0) :: st.filter (fun s => s.1 != t)) day m = euroIn pend st day m) := by
  refine ⟨fun ht => pending_from pend _ day t d0 m ht List.mem_cons_self hd, fun ht => ?_⟩
  simp only [euroIn, isEuro]
  rcases h : m.tok with _ | u
  · rfl
  · have hu : u ≠ t := fun e => ht (h.trans (by rw [e]))
    have this : (t == u) = false := by simp [Ne.symm hu]
    have key : ∀ l : Statements, ((l.filter (fun s => s.1 != t)).any fun s => s.1 == u && decide (s.2 ≤ day)) =
        l.any fun s => s.1 == u && decide (s.2 ≤ day) := by
      intro l
      induction l with
      | nil => rfl
      | cons s ss ih =>
        rw [List.filter_cons]
        by_cases hs : s.1 = t
        · simp [hs, ih, this]
        · simp [hs, ih]
    simp only [confirmed, List.any_cons, this, Bool.false_and, Bool.false_or, key]

/-! ### Losses by the year they came from -/

/-- The losses on hand from year `f`. -/
def byYr (l : List Entry) (f : ℕ) : ℤ := amt (l.filter fun e => decide (e.yr = f))

theorem byYr_cons (e : Entry) (l : List Entry) (f : ℕ) :
    byYr (e :: l) f = (if e.yr = f then e.amount else 0) + byYr l f := by
  unfold byYr; rw [List.filter_cons]; split_ifs with h1 h2 h2 <;> simp_all

theorem byYr_nonneg (l : List Entry) (f : ℕ) (h : ∀ e ∈ l, 0 < e.amount) : 0 ≤ byYr l f := by
  induction l with
  | nil => simp [byYr]
  | cons e es ih =>
    rw [byYr_cons]
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have := h e List.mem_cons_self
    split_ifs <;> omega

theorem byYr_none (l : List Entry) (f : ℕ) (h : ∀ e ∈ l, e.yr ≠ f) : byYr l f = 0 := by
  unfold byYr; rw [List.filter_eq_nil_iff.mpr (by simpa using h)]; rfl

/-- Positive losses usable in `year` are those of the four years before it: what is usable is the sum, over those
years, of the losses from each. -/
theorem avail_eq (year : ℕ) (pool : List Entry) (h : ∀ e ∈ pool, 0 < e.amount) :
    avail year pool = ∑ f ∈ Finset.Ico (year - 4) year, byYr pool f := by
  induction pool with
  | nil => simp [avail, byYr]
  | cons e es ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have he := h e List.mem_cons_self
    have hsum : (∑ x ∈ Finset.Ico (year - 4) year, if e.yr = x then e.amount else 0) =
        if usableIn year e then e.amount else 0 := by
      rw [Finset.sum_ite_eq]
      by_cases hu : usableIn year e
      · rw [if_pos hu, if_pos (Finset.mem_Ico.mpr (by obtain ⟨a, b, -⟩ := hu; omega))]
      · rw [if_neg hu, if_neg]; intro hm; rw [Finset.mem_Ico] at hm; exact hu ⟨hm.2, by omega, he⟩
    simp only [byYr_cons, Finset.sum_add_distrib]
    rw [hsum, ← ih']
    unfold avail
    by_cases hu : usableIn year e
    · rw [List.filter_cons_of_pos (by simpa using hu), if_pos hu]; simp
    · rw [List.filter_cons_of_neg (by simpa using hu), if_neg hu]; simp

/-- **IT-16** Fewer losses from each year (all of them positive) never mean less tax for a reading's year. -/
theorem avail_le (year : ℕ) (p q : List Entry) (hp : ∀ e ∈ p, 0 < e.amount) (hq : ∀ e ∈ q, 0 < e.amount)
    (h : ∀ f, byYr p f ≤ byYr q f) : avail year p ≤ avail year q := by
  rw [avail_eq year p hp, avail_eq year q hq]; exact Finset.sum_le_sum fun f _ => h f

theorem use_mem (year : ℕ) (left : ℤ) (pool : List Entry) (e : Entry) (h : e ∈ (use year left pool).2.1) :
    ∃ e' ∈ pool, e'.yr = e.yr := by
  induction pool generalizing left with
  | nil => simp [use] at h
  | cons x xs ih =>
    simp only [use] at h
    split_ifs at h with h0 h1
    · exact ⟨e, h, rfl⟩
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨x, List.mem_cons_self, rfl⟩
      · obtain ⟨e', h1, h2⟩ := ih _ h; exact ⟨e', List.mem_cons_of_mem _ h1, h2⟩
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨e, List.mem_cons_self, rfl⟩
      · obtain ⟨e', h1, h2⟩ := ih _ h; exact ⟨e', List.mem_cons_of_mem _ h1, h2⟩

/-- **IT-8** What a year carries on (`residues`) is positive and from the last four years, this one included, when
the losses it had came from before it. -/
theorem residues_window (year : ℕ) (net : ℚ) (pool : List Entry) (h : ∀ e ∈ pool, e.yr < year) :
    ∀ e ∈ (yearStep year net pool).residues, e.yr ≤ year ∧ year ≤ e.yr + 3 ∧ 0 < e.amount := by
  intro e he
  simp only [yearStep, List.mem_append, List.mem_filter] at he
  rcases he with ⟨hu, hk⟩ | he
  · simp only [keep, Bool.and_eq_true, decide_eq_true_eq] at hk
    obtain ⟨e', h1, h2⟩ := use_mem _ _ _ e hu
    have := h e' ((List.mergeSort_perm pool _).mem_iff.mp h1)
    exact ⟨by omega, hk.2, hk.1⟩
  · split_ifs at he with hl
    · rw [List.mem_singleton.mp he]; exact ⟨le_rfl, Nat.le_add_right _ _, hl⟩
    · simp at he

theorem residues_pos (year : ℕ) (net : ℚ) (pool : List Entry) :
    ∀ e ∈ (yearStep year net pool).residues, 0 < e.amount := by
  intro e he
  simp only [yearStep, List.mem_append, List.mem_filter] at he
  rcases he with ⟨-, hk⟩ | he
  · simp only [keep, Bool.and_eq_true, decide_eq_true_eq] at hk; exact hk.1
  · split_ifs at he with hl
    · rw [List.mem_singleton.mp he]; exact hl
    · simp at he

/-! ### The common start (report/it.ts:518-520) -/

/-- `Math.min(...)` over the pools carried in of the losses each has from year `f` (the app never passes none). -/
def lowest (f : ℕ) : List (List Entry) → ℤ
  | [] => 0
  | [l] => byYr l f
  | l :: m :: ls => min (byYr l f) (lowest f (m :: ls))

theorem lowest_le (f : ℕ) : ∀ (ins : List (List Entry)) (l : List Entry), l ∈ ins → lowest f ins ≤ byYr l f
  | [], _, h => absurd h List.not_mem_nil
  | [a], l, h => by rw [List.mem_singleton.mp h]; simp [lowest]
  | a :: b :: ls, l, h => by
    simp only [lowest]
    rcases List.mem_cons.mp h with rfl | h
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (lowest_le f (b :: ls) l h)

theorem lowest_zero (f : ℕ) : ∀ (ins : List (List Entry)), (∀ l ∈ ins, byYr l f = 0) → lowest f ins = 0
  | [], _ => rfl
  | [a], h => by simp [lowest, h a List.mem_cons_self]
  | a :: b :: ls, h => by
    simp only [lowest, h a List.mem_cons_self, lowest_zero f (b :: ls) (fun l hl => h l (List.mem_cons_of_mem _ hl)),
      min_self]

/-- The years the losses carried in came from, each once, in order (`origins`, report/it.ts:519). -/
def origins (ins : List (List Entry)) : List ℕ :=
  ((ins.flatten.map Entry.yr).dedup).mergeSort fun a b => decide (a ≤ b)

/-- The pool a year starts from (report/it.ts:520): for each year the losses came from, the least any pool carried
in has from it, kept when above 0. -/
def common (ins : List (List Entry)) : List Entry :=
  ((origins ins).map fun f => (⟨f, lowest f ins⟩ : Entry)).filter fun e => decide (0 < e.amount)

theorem byYr_map (h : ℕ → ℤ) (f : ℕ) :
    ∀ L : List ℕ, L.Nodup →
      byYr ((L.map fun x => (⟨x, h x⟩ : Entry)).filter fun e => decide (0 < e.amount)) f =
        if f ∈ L then max (h f) 0 else 0
  | [], _ => by simp [byYr]
  | x :: xs, hn => by
    rw [List.nodup_cons] at hn
    have ih := byYr_map h f xs hn.2
    simp only [List.map_cons, List.filter_cons, List.mem_cons]
    by_cases hx : x = f
    · subst hx
      rw [if_neg hn.1] at ih
      by_cases hp : 0 < h x
      · simp only [hp, decide_true, if_true, byYr_cons, ih, true_or]; simp; omega
      · simp only [hp, decide_false]; simp [ih]; omega
    · have : (f = x) ↔ False := ⟨fun e => hx e.symm, False.elim⟩
      simp only [this, false_or]
      split_ifs <;> simp_all [byYr_cons]

/-- **IT-16** What the common start has from year `f` is the least any pool carried in has from it (not below 0). -/
theorem byYr_common (ins : List (List Entry)) (f : ℕ) : byYr (common ins) f = max (lowest f ins) 0 := by
  have hn : (origins ins).Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.mpr (List.nodup_dedup _)
  unfold common; rw [byYr_map _ f _ hn]
  split_ifs with hf
  · rfl
  · rw [lowest_zero f ins]; · simp
    intro l hl; apply byYr_none; intro e he hef
    apply hf
    simp only [origins]
    rw [(List.mergeSort_perm _ _).mem_iff, List.mem_dedup, List.mem_map]
    exact ⟨e, List.mem_flatten.mpr ⟨l, hl, he⟩, hef⟩

theorem common_mem (ins : List (List Entry)) (e : Entry) (h : e ∈ common ins) :
    0 < e.amount ∧ ∃ l ∈ ins, ∃ e' ∈ l, e'.yr = e.yr := by
  simp only [common, List.mem_filter, List.mem_map, decide_eq_true_eq] at h
  obtain ⟨⟨f, hf, rfl⟩, hp⟩ := h
  refine ⟨hp, ?_⟩
  simp only [origins] at hf
  rw [(List.mergeSort_perm _ _).mem_iff, List.mem_dedup, List.mem_map] at hf
  obtain ⟨e', he', rfl⟩ := hf
  obtain ⟨l, hl, he⟩ := List.mem_flatten.mp he'
  exact ⟨l, hl, e', he, rfl⟩

/-! ### The readings and the pick (report/it.ts:497-526) -/

/-- A reading (one choice of which pending tokens are euro e-money tokens) by its years: each year's net and its euro
e-money token net, from that reading's own lines (`r.counted`). -/
structure Reading where
  net : ℕ → ℚ
  emt : ℕ → ℚ

/-- A reading's tax for `year` from the losses `pool` (`itYears(r.counted, [year], pool)`, its `tax`). -/
def rTax (r : Reading) (year : ℕ) (pool : List Entry) : ℚ :=
  splitTax year (yearStep year (r.net year) pool).base (r.net year) (r.emt year)

/-- The losses a reading carries on from `year` (`left`, report/it.ts:522). -/
def rLeft (r : Reading) (year : ℕ) (pool : List Entry) : ℤ := amt (yearStep year (r.net year) pool).residues

/-- A reading on its own (`yss`, `own`, report/it.ts:507-508): the losses it carries into year `first + n`. -/
def ownIn (r : Reading) (pre : List Entry) (first : ℕ) : ℕ → List Entry
  | 0 => pre
  | n + 1 => (yearStep (first + n) (r.net (first + n)) (ownIn r pre first n)).residues

/-- The reduce's test (report/it.ts:524): `a` (tax, left) beats `b` with a higher tax, or the same tax and fewer losses
left. -/
def beats (a b : ℚ × ℤ) : Bool := decide (b.1 < a.1) || (decide (a.1 = b.1) && decide (a.2 < b.2))

/-- `taxes.reduce(…, 0)` over the first `n` readings: the one picked. -/
def pickN (key : ℕ → ℚ × ℤ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if beats (key n) (key (pickN key n)) then n else pickN key n

/-- Reading `i`'s (tax, left) for `year` from `pool`. -/
def key (rs : ℕ → Reading) (year : ℕ) (pool : List Entry) (i : ℕ) : ℚ × ℤ :=
  (rTax (rs i) year pool, rLeft (rs i) year pool)

/-- A year as shown: the pool it starts from, the reading picked and what it carries on (`prev`). -/
structure Shown where
  pool : List Entry
  pick : ℕ
  res : List Entry

/-- `itReport`'s loop over the years (report/it.ts:516-527), `m` readings `rs 0 … rs (m-1)` (reading 0 assumes none),
the year `first + n`: the first year starts from the losses declared before (`pre`); each later one from the common
start of every reading's own pool and last year as shown. -/
def shownAt (rs : ℕ → Reading) (m : ℕ) (pre : List Entry) (first : ℕ) : ℕ → Shown
  | 0 =>
    let p := common [pre]
    let a := pickN (key rs first p) m
    ⟨p, a, (yearStep first ((rs a).net first) p).residues⟩
  | n + 1 =>
    let p := common ((List.range m).map (fun i => ownIn (rs i) pre first (n + 1)) ++
      [(shownAt rs m pre first n).res])
    let a := pickN (key rs (first + (n + 1)) p) m
    ⟨p, a, (yearStep (first + (n + 1)) ((rs a).net (first + (n + 1))) p).residues⟩

/-- The tax shown for year `first + n`. -/
def shownTax (rs : ℕ → Reading) (m : ℕ) (pre : List Entry) (first n : ℕ) : ℚ :=
  rTax (rs (shownAt rs m pre first n).pick) (first + n) (shownAt rs m pre first n).pool

theorem shown_pick (rs : ℕ → Reading) (m : ℕ) (pre : List Entry) (first n : ℕ) :
    (shownAt rs m pre first n).pick = pickN (key rs (first + n) (shownAt rs m pre first n).pool) m := by
  cases n <;> rfl

theorem shown_res (rs : ℕ → Reading) (m : ℕ) (pre : List Entry) (first n : ℕ) :
    (shownAt rs m pre first n).res = (yearStep (first + n) ((rs (shownAt rs m pre first n).pick).net (first + n))
      (shownAt rs m pre first n).pool).residues := by
  cases n <;> rfl

/-- **IT-16** The test is a strict order, total on distinct (tax, left): never a pair against itself, transitive, one
way only, and of two different pairs one beats the other. -/
theorem beats_order (a b c : ℚ × ℤ) :
    beats a a = false ∧ (beats a b = true → beats b c = true → beats a c = true) ∧
      (beats a b = true → beats b a = false) ∧ (a ≠ b → beats a b = true ∨ beats b a = true) := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; obtain ⟨c1, c2⟩ := c
  simp only [beats, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff,
    Bool.and_eq_false_iff, decide_eq_false_iff_not, ne_eq, Prod.mk.injEq]
  refine ⟨by simp, ?_, ?_, ?_⟩
  · rintro (h1 | ⟨h1, h2⟩) (h3 | ⟨h3, h4⟩)
    · left; linarith
    · left; linarith
    · left; linarith
    · right; exact ⟨h1.trans h3, h2.trans h4⟩
  · rintro (h1 | ⟨h1, h2⟩)
    · exact ⟨by linarith, Or.inl (by intro h; linarith)⟩
    · exact ⟨by linarith, Or.inr (by omega)⟩
  · intro h
    rcases lt_trichotomy a1 b1 with h1 | h1 | h1
    · right; left; exact h1
    · rcases lt_trichotomy a2 b2 with h2 | h2 | h2
      · left; right; exact ⟨h1, h2⟩
      · exact absurd ⟨h1, h2⟩ h
      · right; right; exact ⟨h1.symm, h2⟩
    · left; left; exact h1

/-- **IT-16** The pick among the first `n ≥ 1` readings is one of them that none beats, and it beats every reading
before it: the highest tax, then the fewest losses left, then the first. -/
theorem pickN_spec (key : ℕ → ℚ × ℤ) (n : ℕ) (hn : 0 < n) :
    pickN key n < n ∧ (∀ j < n, beats (key j) (key (pickN key n)) = false) ∧
      (∀ j < pickN key n, beats (key (pickN key n)) (key j) = true) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · refine ⟨by simp [pickN], fun j hj => ?_, fun j hj => ?_⟩
      · have : j = 0 := by omega
        subst this; simp [pickN, (beats_order (key 0) (key 0) (key 0)).1]
      · simp [pickN] at hj
    obtain ⟨h1, h2, h3⟩ := ih hn'
    simp only [pickN]
    split_ifs with hb
    · refine ⟨by omega, fun j hj => ?_, fun j hj => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · by_contra hc
          rw [Bool.not_eq_false] at hc
          have := (beats_order _ _ (key (pickN key n))).2.1 hc hb
          rw [h2 j hj] at this; exact absurd this (by simp)
        · exact (beats_order _ (key j) (key j)).1
      · have hj2 := h2 j hj
        by_cases he : key j = key (pickN key n)
        · rw [he]; exact hb
        · rcases (beats_order (key j) (key (pickN key n)) (key j)).2.2.2 he with h | h
          · rw [hj2] at h; exact absurd h (by simp)
          · exact (beats_order _ _ _).2.1 hb h
    · refine ⟨by omega, fun j hj => ?_, h3⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact h2 j hj
      · simpa using hb

/-- **IT-16** The pick is the only reading with that property: the order decides it. -/
theorem pick_unique (key : ℕ → ℚ × ℤ) (n q : ℕ) (hq : q < n) (h1 : ∀ j < n, beats (key j) (key q) = false)
    (h2 : ∀ j < q, beats (key q) (key j) = true) : q = pickN key n := by
  obtain ⟨p1, p2, p3⟩ := pickN_spec key n (by omega)
  rcases lt_trichotomy q (pickN key n) with h | h | h
  · have := p3 q h; rw [h1 _ p1] at this; exact absurd this (by simp)
  · exact h
  · have := h2 _ h; rw [p2 q hq] at this; exact absurd this (by simp)

/-- The pick's tax is not below any reading's, from the same pool. -/
theorem pick_max (rs : ℕ → Reading) (m year : ℕ) (pool : List Entry) (hm : 0 < m) (i : ℕ) (hi : i < m) :
    rTax (rs i) year pool ≤ rTax (rs (pickN (key rs year pool) m)) year pool := by
  have := (pickN_spec (key rs year pool) m hm).2.1 i hi
  simp only [beats, key, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at this
  exact this.1

/-- **IT-16** Never too little, from the common start: the tax shown for a year is not below any reading's tax for it
from the same losses carried in. -/
theorem shown_max (rs : ℕ → Reading) (m : ℕ) (pre : List Entry) (first n : ℕ) (hm : 0 < m) (i : ℕ) (hi : i < m) :
    rTax (rs i) (first + n) (shownAt rs m pre first n).pool ≤ shownTax rs m pre first n := by
  unfold shownTax; rw [shown_pick]; exact pick_max rs m _ _ hm i hi

/-- Fewer losses from each year carried in (all positive) never mean less tax for a reading. -/
theorem rTax_pool (r : Reading) (year : ℕ) (p q : List Entry) (hp : ∀ e ∈ p, 0 < e.amount)
    (hq : ∀ e ∈ q, 0 < e.amount) (h : ∀ f, byYr p f ≤ byYr q f) : rTax r year q ≤ rTax r year p := by
  unfold rTax yearStep
  simp only
  have hg := yGain_nonneg year (euros (r.net year))
  rw [base_eq _ _ _ hg, base_eq _ _ _ hg, avail_sortPool, avail_sortPool]
  have := avail_le year p q hp hq h
  exact (split_base_mono year _ _ _ _ (le_max_right _ _) (max_le_max (by omega) le_rfl)).2.1

theorem ownIn_pos (r : Reading) (pre : List Entry) (first : ℕ) (hpre : ∀ e ∈ pre, 0 < e.amount) :
    ∀ n, ∀ e ∈ ownIn r pre first n, 0 < e.amount
  | 0 => hpre
  | n + 1 => residues_pos _ _ _

theorem ownIn_lt (r : Reading) (pre : List Entry) (first : ℕ) (hpre : ∀ e ∈ pre, e.yr < first) :
    ∀ n, ∀ e ∈ ownIn r pre first n, e.yr < first + n
  | 0 => hpre
  | n + 1 => fun e he => by
    have := residues_window _ _ _ (ownIn_lt r pre first hpre n) e he; omega

/-- **IT-16** The common start of each year, by the year the losses came from: the first year has from each year
what was declared before; each later year no more than any reading carries in on its own and no more than last year
as shown carries on. -/
theorem carry_le (rs : ℕ → Reading) (m : ℕ) (pre : List Entry) (first : ℕ) (hpre : ∀ e ∈ pre, 0 < e.amount) (f : ℕ) :
    byYr (shownAt rs m pre first 0).pool f = byYr pre f ∧
      ∀ n, (∀ i < m, byYr (shownAt rs m pre first (n + 1)).pool f ≤ byYr (ownIn (rs i) pre first (n + 1)) f) ∧
        byYr (shownAt rs m pre first (n + 1)).pool f ≤ byYr (shownAt rs m pre first n).res f := by
  refine ⟨?_, fun n => ⟨fun i hi => ?_, ?_⟩⟩
  · show byYr (common [pre]) f = _
    rw [byYr_common]; simp only [lowest]; exact max_eq_left (byYr_nonneg _ _ hpre)
  · show byYr (common _) f ≤ _
    rw [byYr_common]
    exact max_le (lowest_le _ _ _ (List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)))
      (byYr_nonneg _ _ (ownIn_pos _ _ _ hpre _))
  · show byYr (common _) f ≤ _
    rw [byYr_common, shown_res]
    exact max_le (by rw [← shown_res]; exact lowest_le _ _ _ (List.mem_append_right _ List.mem_cons_self))
      (byYr_nonneg _ _ (residues_pos _ _ _))

/-- **IT-16** The pool a year starts from holds positive losses of earlier years; from the second year on, only of
the four years before it. -/
theorem carry_window (rs : ℕ → Reading) (m : ℕ) (pre : List Entry) (first : ℕ) (hpre : ∀ e ∈ pre, e.yr < first) :
    ∀ n, ∀ e ∈ (shownAt rs m pre first n).pool, e.yr < first + n ∧ (0 < n → first + n ≤ e.yr + 4) ∧ 0 < e.amount
  | 0 => fun e he => by
    obtain ⟨hp, l, hl, e', he', hy⟩ := common_mem _ e he
    rw [List.mem_singleton.mp hl] at he'
    exact ⟨by have := hpre e' he'; omega, by omega, hp⟩
  | n + 1 => fun e he => by
    obtain ⟨hp, l, hl, e', he', hy⟩ := common_mem _ e he
    have hw : e'.yr ≤ first + n ∧ first + n ≤ e'.yr + 3 := by
      rcases List.mem_append.mp hl with hl | hl
      · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hl
        have := residues_window _ _ _ (ownIn_lt (rs i) pre first hpre n) e' he'; exact ⟨this.1, this.2.1⟩
      · rw [List.mem_singleton.mp hl, shown_res] at he'
        have := residues_window _ _ _ (fun x hx => (carry_window rs m pre first hpre n x hx).1) e' he'
        exact ⟨this.1, this.2.1⟩
    exact ⟨by omega, fun _ => by omega, hp⟩

/-- **IT-16** Never too little, on each reading's own history: the tax shown for a year is not below the tax any
reading has for it on its own, from the losses it alone carries in. -/
theorem own_le_shown (rs : ℕ → Reading) (m : ℕ) (pre : List Entry) (first n : ℕ) (hm : 0 < m)
    (hpre : ∀ e ∈ pre, 0 < e.amount) (i : ℕ) (hi : i < m) :
    rTax (rs i) (first + n) (ownIn (rs i) pre first n) ≤ shownTax rs m pre first n := by
  refine le_trans ?_ (shown_max rs m pre first n hm i hi)
  refine rTax_pool _ _ _ _ ?_ (ownIn_pos _ _ _ hpre n) ?_
  · intro e he
    cases n with
    | zero => exact (common_mem _ e he).1
    | succ n => exact (common_mem _ e he).1
  · intro f
    cases n with
    | zero => rw [(carry_le rs m pre first hpre f).1]; rfl
    | succ n => exact ((carry_le rs m pre first hpre f).2 n).1 i hi

/-! ### This year so far (`now`, report/it.ts:529-535) -/

/-- The highest net any reading has for `year` (`nets.reduce(max)`). -/
def maxNet (rs : ℕ → Reading) (m year : ℕ) : ℚ :=
  ((List.range (m - 1)).map fun i => (rs (i + 1)).net year).foldl max ((rs 0).net year)

theorem foldl_max (l : List ℚ) (a : ℚ) : a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons, List.mem_cons]
    obtain ⟨h1, h2⟩ := ih (max a y)
    refine ⟨(le_max_left _ _).trans h1, fun x hx => ?_⟩
    rcases hx with rfl | hx
    · exact (le_max_right _ _).trans h1
    · exact h2 x hx

theorem le_maxNet (rs : ℕ → Reading) (m year i : ℕ) (hi : i < m) : (rs i).net year ≤ maxNet rs m year := by
  unfold maxNet
  rcases i with _ | i
  · exact (foldl_max _ _).1
  · exact (foldl_max _ _).2 _ (List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩)

/-- `now.carried` for year `first + n`: the year's pool as shown, the losses from the four years before it. -/
def nowCarried (rs : ℕ → Reading) (m : ℕ) (pre : List Entry) (first n : ℕ) : ℤ :=
  amt ((shownAt rs m pre first n).pool.filter fun e => decide (first + n - 4 ≤ e.yr))

/-- What the planners count this year so far (`itYearTax(now.year, now.net, now.carried, now.euroEmtNet)`): the
highest net, the losses carried in as shown, and the euro e-money token net of the reading shown. -/
def nowTax (rs : ℕ → Reading) (m : ℕ) (pre : List Entry) (first n : ℕ) : ℚ :=
  yearTax (first + n) (maxNet rs m (first + n)) (nowCarried rs m pre first n)
    ((rs (shownAt rs m pre first n).pick).emt (first + n))

/-- **IT-16** This year so far never counts less tax than the year as shown. -/
theorem now_ge (rs : ℕ → Reading) (m : ℕ) (pre : List Entry) (first n : ℕ) (hm : 0 < m) (h1 : 1 ≤ first)
    (hpre : ∀ e ∈ pre, e.yr < first) : shownTax rs m pre first n ≤ nowTax rs m pre first n := by
  set Y := first + n
  set S := shownAt rs m pre first n
  have hw := carry_window rs m pre first hpre n
  have hc : nowCarried rs m pre first n = avail Y S.pool := by
    unfold nowCarried avail
    congr 1
    apply List.filter_congr
    intro e he
    obtain ⟨a, -, c⟩ := hw e he
    simp only [usableIn, decide_eq_decide]
    constructor
    · intro h; exact ⟨a, by omega, c⟩
    · intro h; omega
  have hpos : ∀ e ∈ S.pool, 0 < e.amount := fun e he => (hw e he).2.2
  have hpk := (pickN_spec (key rs Y S.pool) m hm).1
  rw [← shown_pick] at hpk
  unfold shownTax nowTax rTax yearTax
  simp only [yearStep]
  have hg := yGain_nonneg Y (euros ((rs S.pick).net Y))
  have hg2 := yGain_nonneg Y (euros (maxNet rs m Y))
  rw [hc, base_eq _ _ _ hg, avail_sortPool, yearTax_base Y _ _ (by omega) hg2 (avail_nonneg _ _)]
  have hn := le_maxNet rs m Y _ hpk
  exact centsUp_mono _ _ (exact_net_mono Y _ (avail_nonneg _ _) _ _ _ hn)
/-! ## Rule 12: IVCA (DL 201/2011 art. 19 c. 18-bis; Modello Redditi PF, RW col. 33 and RW8) -/

/-- `itIvca`: 0.2% of the value, times the share owned, for the days held (a full year at most) over the days in the
year. -/
def ivca (value : ℚ) (days diy : ℕ) (share : ℚ := 1) : ℚ := value * (2 / 1000) * share * (min days diy : ℕ) / diy

/-- An RW line (an account): each coin's IVCA on its end value for its own days held, added and rounded to euros. -/
def accountIvca (cs : List (ℚ × ℕ)) (diy : ℕ) : ℤ := euros ((cs.map fun c => ivca c.1 c.2 diy).sum)

/-- RW8 col. 1: the sum of the accounts' whole-euro figures. -/
def rwTotal (accounts : List (List (ℚ × ℕ))) (diy : ℕ) : ℤ := (accounts.map (accountIvca · diy)).sum

/-- `itIvcaDue`: RW col. 5 for the year, the IVCA in euros (col. 1) less the foreign tax credit (col. 2) plus the
credit used to offset (col. 3) less the instalments paid (col. 4); nothing when €12 or less. -/
def ivcaDue (col1 : ℚ) (credit used inst : ℤ) : ℤ :=
  if 12 < euros col1 - credit + used - inst then euros col1 - credit + used - inst else 0

/-- **IT-12** A full year (or more days than the year has) is 0.2% of the value times the share. -/
theorem ivca_full_year (v share : ℚ) (days diy : ℕ) (hd : diy ≤ days) (hy : 0 < diy) :
    ivca v days diy share = v * (2 / 1000) * share := by
  unfold ivca
  rw [min_eq_right hd]
  have : (diy : ℚ) ≠ 0 := by positivity
  field_simp

/-- **IT-12** For a value and a share (at most 1) not below 0, the IVCA is between 0 and 0.2% of the value. -/
theorem ivca_bounds (v share : ℚ) (days diy : ℕ) (hv : 0 ≤ v) (hs : 0 ≤ share) (hs1 : share ≤ 1) (hy : 0 < diy) :
    0 ≤ ivca v days diy share ∧ ivca v days diy share ≤ v * (2 / 1000) := by
  unfold ivca
  have hd : ((min days diy : ℕ) : ℚ) ≤ diy := by exact_mod_cast min_le_right days diy
  have hy' : (0 : ℚ) < diy := by exact_mod_cast hy
  have h0 : (0 : ℚ) ≤ ((min days diy : ℕ) : ℚ) := by positivity
  constructor
  · positivity
  · rw [div_le_iff₀ hy']
    have : v * (2 / 1000) * share ≤ v * (2 / 1000) := by nlinarith
    calc v * (2 / 1000) * share * ((min days diy : ℕ) : ℚ) ≤ v * (2 / 1000) * ((min days diy : ℕ) : ℚ) :=
          mul_le_mul_of_nonneg_right this h0
      _ ≤ v * (2 / 1000) * diy := mul_le_mul_of_nonneg_left hd (by positivity)

/-- **IT-12** Each account's figure is within 50 cents of its exact IVCA. -/
theorem account_close (cs : List (ℚ × ℕ)) (diy : ℕ) :
    |(accountIvca cs diy : ℚ) - (cs.map fun c => ivca c.1 c.2 diy).sum| ≤ 1 / 2 :=
  (euros_bounds _).1

/-- **IT-12** Nothing is due when col. 5 is €12 or less; over €12 all of it is. -/
theorem ivca_due (col1 : ℚ) (credit used inst : ℤ) :
    (euros col1 - credit + used - inst ≤ 12 → ivcaDue col1 credit used inst = 0) ∧
      (12 < euros col1 - credit + used - inst → ivcaDue col1 credit used inst = euros col1 - credit + used - inst) := by
  unfold ivcaDue
  constructor
  · intro h; rw [if_neg (by omega)]
  · intro h; rw [if_pos h]

/-- The app's tests: €10,000 for 73 days of 365 is €4; €12.40 → nothing, €12.50 → €13, €20 → €20; €20 less €10 of
instalments → nothing, less €5 → €15; €20 less a €30 credit plus €25 used → €15; less a €40 credit → nothing. -/
theorem ivca_examples :
    ivca 10000 73 365 = 4 ∧ ivcaDue (124 / 10) 0 0 0 = 0 ∧ ivcaDue (125 / 10) 0 0 0 = 13 ∧ ivcaDue 20 0 0 0 = 20 ∧
      ivcaDue 20 0 0 10 = 0 ∧ ivcaDue 20 0 0 5 = 15 ∧ ivcaDue 20 30 25 0 = 15 ∧ ivcaDue 20 40 0 0 = 0 := by
  simp [ivca, ivcaDue, euros]; norm_num

/-! ## Rule 13: next year's IVCA instalments (the report's note; not computed by the app) -/

/-- The note: from €52, next year's instalments equal this year's tax: from €257.52, 40% by 30 June and 60% by
30 November; below that, all by 30 November. (by 30 June, by 30 November), exact. -/
def instalments (t : ℚ) : ℚ × ℚ :=
  if t < 52 then (0, 0) else if 25752 / 100 ≤ t then (t * 40 / 100, t - t * 40 / 100) else (0, t)

/-- **IT-13** Below €52 no instalment; from €52 the instalments add up to the tax; from €257.52 the first is 40% and
the second 60%; between, all in the second. -/
theorem instalments_spec (t : ℚ) :
    (t < 52 → instalments t = (0, 0)) ∧
    (52 ≤ t → (instalments t).1 + (instalments t).2 = t) ∧
    (25752 / 100 ≤ t → instalments t = (t * 40 / 100, t * 60 / 100)) ∧
    (52 ≤ t → t < 25752 / 100 → instalments t = (0, t)) := by
  unfold instalments
  refine ⟨fun h => by rw [if_pos h], fun h => ?_, fun h => ?_, fun h h' => ?_⟩
  · rw [if_neg (by linarith)]; split_ifs <;> simp
  · rw [if_neg (by linarith), if_pos h]; congr 1; ring
  · rw [if_neg (by linarith), if_neg (by linarith)]

/-! ## Rule 14: payment and filing dates (`itWorkingDay`, `itDeadlines`) -/

/-- Days from 1 January 1970 of a date in the proleptic Gregorian calendar (as JavaScript's `Date.UTC`). -/
def dayNum (y m d : ℤ) : ℤ :=
  let y' := if m ≤ 2 then y - 1 else y
  let era := y' / 400
  let yoe := y' - era * 400
  let mp := if 2 < m then m - 3 else m + 9
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- The date (year, month, day) of a day number: the inverse of `dayNum`. -/
def civil (z : ℤ) : ℤ × ℤ × ℤ :=
  let z' := z + 719468
  let era := z' / 146097
  let doe := z' - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (if m ≤ 2 then yoe + era * 400 + 1 else yoe + era * 400, m, d)

/-- 0 Sunday … 6 Saturday (1 January 1970 was a Thursday). -/
def weekday (z : ℤ) : ℤ := (z + 4) % 7

/-- A Saturday, a Sunday or a holiday. -/
def off (hol : ℤ → Bool) (z : ℤ) : Bool := decide (weekday z = 0) || decide (weekday z = 6) || hol z

/-- `itWorkingDay`: the day itself or the next working day, looking at most `fuel` days on. -/
def work (hol : ℤ → Bool) : ℕ → ℤ → ℤ
  | 0, z => z
  | f + 1, z => if off hol z then work hol f (z + 1) else z

/-- The app's fixed public holidays (L. 260/1949, L. 54/1977, L. 792/1985). -/
def appHol (z : ℤ) : Bool :=
  [((1 : ℤ), (1 : ℤ)), (1, 6), (4, 25), (5, 1), (6, 2), (8, 15), (11, 1), (12, 8), (12, 25), (12, 26)].contains
    ((civil z).2.1, (civil z).2.2)

def fuel : ℕ := 30

/-- From 1 to 20 August (DL 16/2012 art. 3-quater). -/
def inAug (z : ℤ) : Bool := decide ((civil z).2.1 = 8) && decide (1 ≤ (civil z).2.2) && decide ((civil z).2.2 ≤ 20)

/-- `itDeadlines`: (pay by, pay late by, file by) for a year's income, none before 2023. -/
def deadlines (hol : ℤ → Bool) (y : ℤ) : Option (ℤ × ℤ × ℤ) :=
  if y < 2023 then none else
    let pay := work hol fuel (dayNum (y + 1) 6 30)
    let late := work hol fuel (pay + 30)
    some (pay, if inAug late then work hol fuel (dayNum (civil late).1 8 20) else late,
      work hol fuel (dayNum (y + 1) 10 31))

/-- **IT-14** The working day found is never before the day asked and every day before it is a weekend or holiday. -/
theorem work_spec (hol : ℤ → Bool) (f : ℕ) (z : ℤ) :
    z ≤ work hol f z ∧ ∀ x, z ≤ x → x < work hol f z → off hol x = true := by
  induction f generalizing z with
  | zero => simp [work]; intro x h1 h2; omega
  | succ f ih =>
    simp only [work]
    split_ifs with h
    · obtain ⟨a, b⟩ := ih (z + 1)
      refine ⟨by omega, fun x h1 h2 => ?_⟩
      rcases eq_or_lt_of_le h1 with rfl | h1
      · exact h
      · exact b x (by omega) h2
    · exact ⟨le_refl _, fun x h1 h2 => by omega⟩

/-- **IT-14** When a working day lies within the days looked at, the day found is a working day (so the first one). -/
theorem work_on (hol : ℤ → Bool) (f : ℕ) (z : ℤ) (h : ∃ k : ℕ, k < f ∧ off hol (z + k) = false) :
    off hol (work hol f z) = false := by
  induction f generalizing z with
  | zero => obtain ⟨k, hk, _⟩ := h; omega
  | succ f ih =>
    simp only [work]
    split_ifs with ho
    · apply ih
      obtain ⟨k, hk, hk'⟩ := h
      cases k with
      | zero => simp [ho] at hk'
      | succ k => exact ⟨k, by omega, by rw [← hk']; congr 1; push_cast; ring⟩
    · simpa using ho

/-- **IT-14** The dates by rule: the payment on 30 June (or the next working day); the late payment 30 days after it
(next working day), moved to 20 August (or the next working day) when it falls from 1 to 20 August; the filing on
31 October (or the next working day). None before 2023. -/
theorem deadlines_rule (hol : ℤ → Bool) (y : ℤ) :
    (y < 2023 → deadlines hol y = none) ∧
    (2023 ≤ y → ∃ pay late file, deadlines hol y = some (pay, late, file) ∧
      pay = work hol fuel (dayNum (y + 1) 6 30) ∧
      late = (if inAug (work hol fuel (pay + 30)) then work hol fuel (dayNum (civil (work hol fuel (pay + 30))).1 8 20)
        else work hol fuel (pay + 30)) ∧
      file = work hol fuel (dayNum (y + 1) 10 31)) := by
  unfold deadlines
  refine ⟨fun h => by rw [if_pos h], fun h => ?_⟩
  rw [if_neg (by omega)]
  exact ⟨_, _, _, rfl, rfl, rfl, rfl⟩

/-- **IT-14** Never early: pay on or after 30 June, filing on or after 31 October; the late payment is the working day
on or after 30 days from the payment date, or, when that falls from 1 to 20 August, the working day on or after 20
August of that year. -/
theorem deadlines_never_early (hol : ℤ → Bool) (y : ℤ) (pay late file : ℤ)
    (h : deadlines hol y = some (pay, late, file)) :
    dayNum (y + 1) 6 30 ≤ pay ∧ dayNum (y + 1) 10 31 ≤ file ∧
      (inAug (work hol fuel (pay + 30)) = false → pay + 30 ≤ late) ∧
      (inAug (work hol fuel (pay + 30)) = true → dayNum (civil (work hol fuel (pay + 30))).1 8 20 ≤ late) := by
  unfold deadlines at h
  split_ifs at h with hy
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  refine ⟨(work_spec _ _ _).1, (work_spec _ _ _).1, fun ha => ?_, fun ha => ?_⟩
  · rw [if_neg (by simp [ha])]; exact (work_spec _ _ _).1
  · rw [if_pos ha]; exact (work_spec _ _ _).1

/-- Every year from 2023 to 2100 with the app's holidays: the three dates are working days, the late date is at least
30 days after the payment date and at most 53 (20 August a Saturday), and no date is moved more than 3 days past its rule date. -/
def checkYear (y : ℤ) : Bool :=
  match deadlines appHol y with
  | some (pay, late, file) =>
    !off appHol pay && !off appHol late && !off appHol file && decide (pay + 30 ≤ late) &&
      decide (late ≤ pay + 53) && decide (pay ≤ dayNum (y + 1) 6 30 + 3) && decide (file ≤ dayNum (y + 1) 10 31 + 3)
  | none => false

/-- **IT-14** The 0.4% for paying in the 30 days after (only said in the app's text). -/
def withLateInterest (t : ℚ) : ℚ := t + t * 4 / 1000

/-- The app's tests, by rule with the app's holidays: income 2023 → pay 1 July 2024 (30 June a Sunday), late 31 July,
file 31 October 2024; 2025 → 30 June, 30 July, 2 November 2026; 2026 → 30 June, 30 July, 2 November 2027 (31 October a
Sunday, 1 November a holiday); 2027 → 30 June, 31 July (30 July a Sunday), 31 October 2028; 2028 → 2 July 2029 (30 June a
Saturday), and 30 days on is 1 August, moved to 20 August; 2032: 20 August 2033 is a Saturday, so 22 August. -/
theorem deadlines_examples :
    deadlines appHol 2023 = some (dayNum 2024 7 1, dayNum 2024 7 31, dayNum 2024 10 31) ∧
    deadlines appHol 2024 = some (dayNum 2025 6 30, dayNum 2025 7 30, dayNum 2025 10 31) ∧
    deadlines appHol 2025 = some (dayNum 2026 6 30, dayNum 2026 7 30, dayNum 2026 11 2) ∧
    deadlines appHol 2026 = some (dayNum 2027 6 30, dayNum 2027 7 30, dayNum 2027 11 2) ∧
    deadlines appHol 2027 = some (dayNum 2028 6 30, dayNum 2028 7 31, dayNum 2028 10 31) ∧
    (deadlines appHol 2028).map (·.2.1) = some (dayNum 2029 8 20) ∧
    (deadlines appHol 2032).map (·.2.1) = some (dayNum 2033 8 22) ∧
    deadlines appHol 2022 = none := by
  decide

/-- **IT-14** `checkYear` holds for every year of income from 2023 to 2100 with the app's holidays. -/
theorem deadlines_2023_2100 : ((List.range 78).map (fun i : ℕ => (2023 + i : ℤ))).all checkYear = true := by
  decide

end Kanon.Italy
