import Mathlib.Tactic

/-!
# Italy: crypto gains of a private person, TUIR art. 67 c. 1 c-sexies and 68 c. 9-bis (quadro RT, quadro RW)

The app's engine `src/lib/engine/it.ts` (`itRun`, `itYears`, `itYearBase`, `itYearTax`, `itTaxOnSale`, `itEuros`,
`itIvca`, `itIvcaDue`, `itWorkingDay`, `itDeadlines`), the swap branch of the classifier `itBook` and the IVCA sum of
`itRw` in `src/lib/report/it.ts`, at kanon-app commit 2ec8fce (branch claude/italy-32). Sources: TUIR art. 67 c. 1
c-sexies and 68 cc. 5 and 9-bis (L. 197/2022 art. 1 c. 126); L. 207/2024 art. 1 c. 25 (no €2,000 threshold from 2025);
Agenzia delle Entrate, Circolare 30/E of 27 October 2023 (§§ 3.2.1, 3.3-3.4, p. 51 and p. 55); DL 201/2011 art. 19
c. 18-bis (IVCA, 0.2%); Modello Redditi PF (RT57, RT88-89, RW col. 33, RW8); DPR 435/2001 art. 17; DPR 322/1998
art. 2; DL 70/2011 art. 7 c. 2 l; DL 16/2012 art. 3-quater.

Modelled, in exact fractions where the app uses decimal.js:

* `itRun` (rules 1-4): `take` is its last-in-first-out `take` (the newest lot at the head of the list here, at the end
  of the app's array), `takeAll` its loop over the coins given, `step` its handling of one operation (buy, provento,
  drop, sale or exchange, untaxed swap with the cost split by value or equally), `run` the loop. Ops are taken in the
  order given (the app first sorts them by time and kind; that sort is not modelled).
* `itBook` for a swap happening (`classify`, rules 2-3): bought with money, sold for money, untaxed swap of the same
  kind, taxable exchange between kinds (crypto and e-money tokens). Its other happenings (fees merged one line a day,
  bridges, proventi, answers, futures) are not modelled; a provento's line and lot are `step`'s.
* `itYearBase` and `itYears` (rules 5-8): the net in whole euros, the €2,000 threshold to 2024, losses used oldest first
  within four years (`use`), the residues kept and the losses that expire. `itYearTax` and `itTaxOnSale` (rule 15).
  The tax of `itYears` (`yearTaxSplit`): to 2025 26% of the base; from 2026 the euro e-money token part at 26% and the
  rest at 33% (`split`), rounded up to the cent. Years before 2023 (no rate) are not modelled.
* `itEuros` (half away from zero, decimal.js ROUND_HALF_UP) and `centsUp` (rule 11).
* `itIvca`, the per-account rounding and sum in `itRw`, and `itIvcaDue` (rule 12), with every price known (the app
  shows no total when a price is missing).
* The IVCA instalments (rule 13) are not computed by the app: they are only said in the report's note (`ReportPdf.tsx`,
  quadro RW). `instalments` models that sentence.
* `itWorkingDay` and `itDeadlines` (rule 14) on day numbers (days from 1 January 1970, the proleptic Gregorian
  calendar), with the holidays as a parameter (`appHol` is the app's fixed list) and the search for a working day
  bounded by 30 days (the app's loop has no bound). The 0.4% for paying late is only said in the app's text.

Out of scope: the sort of `itRun`'s ops, the euro conversion and prices, `itHoldings` (days held, start and end
quantities), `itLotsFor`, how answers and other happenings become ops, and decimal.js precision (40 significant digits:
a division such as cost × left ÷ qty is rounded there and exact here). Years are natural numbers.

Rules 9 and 10 (income from 2026): 33% (L. 207/2024 art. 1 c. 24), 26% for euro e-money tokens, and a euro e-money
token turned into euros is no gain or loss (L. 199/2025 art. 1 c. 28); D.Lgs. 117/2026 re-enacts both from 2027
(art. 304 c. 7, same text). A token is a euro e-money token when it is in the app's euro set (`Mv.euroEmt`), however the
app recognises it. Earlier losses come off the 33% part first: a KANON choice, no source settles it (`split`). The
"sold" answer for a euro e-money token from 2026 (also a drop in `itBook`) is not modelled.
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
tax effect, a taxable sale or exchange at `proceeds`, an untaxed swap with money paid on top. `euroEmt`: the line is a
euro e-money token's (taxed at 26% from 2026, rule 9). -/
inductive Op
  | buy (asset : ℕ) (qty cost : ℚ)
  | income (asset : ℕ) (qty value : ℚ) (euroEmt : Bool)
  | drop (gave : List Coin)
  | dispose (gave : List Coin) (proceeds : ℚ) (euroEmt : Bool)
  | swap (gave : List Coin) (got : List Got) (paid : ℚ)

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

/-! ## The classifier `itBook` for a swap happening (rules 2-3; Circolare 30/E §§ 3.3-3.4) -/

/-- A crypto movement: asset, quantity, value in euros (none: no price), whether it is an e-money token (a stablecoin
tied to one official currency, MiCA art. 3 c. 1 n. 7) and whether it is in the app's euro e-money token set (however
the app recognises them: by symbol at 2ec8fce, by contract address later; every euro one is also an e-money token). -/
structure Mv where
  asset : ℕ
  qty : ℚ
  value : Option ℚ
  emt : Bool := false
  euroEmt : Bool := false

/-- Money moved: its value in euros (none: no rate) and whether it is euros. -/
structure Money where
  value : Option ℚ
  eur : Bool := true

/-- A swap happening: the year (Rome), crypto out and in, money out and in, and `keepsCost` (a coin put into an app
for its receipt coin). -/
structure SwapH where
  year : ℕ
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

/-- Every coin on both sides an e-money token, or none. -/
def sameKind (a b : List Mv) : Bool := (a ++ b).all Mv.emt || (a ++ b).all (fun m => !m.emt)

/-- The money paid on top of an untaxed swap (`paid`, kept only when known and above 0). -/
def paidOf (fOut : List Money) : ℚ :=
  if fOut = [] then 0 else match sumV (fOut.map Money.value) with
    | some p => if 0 < p then p else 0
    | none => 0

/-- From 2026, euro e-money tokens only, turned into euros (L. 199/2025 art. 1 c. 28): no gain or loss. -/
def euroRedeem (h : SwapH) : Bool := decide (2026 ≤ h.year) && h.out.all Mv.euroEmt && h.fIn.all Money.eur

/-- `itBook` for one swap happening (the euroEmt flags of lines not modelled). -/
def classify (h : SwapH) : List Op :=
  if h.keepsCost then (if h.out ≠ [] ∧ h.inn ≠ [] then [.swap (coins h.out) (gots h.inn) 0] else [])
  else if h.out = [] then
    (if h.inn ≠ [] then
      buys h.inn (((if h.fOut ≠ [] then sumV (h.fOut.map Money.value) else none).or
        (sumV (h.inn.map Mv.value))).getD 0)
     else [])
  else if h.inn = [] then
    (if h.fIn = [] then [.drop (coins h.out)]
     else if euroRedeem h then [.drop (coins h.out)]
     else [.dispose (coins h.out) (((sumV (h.fIn.map Money.value)).or (sumV (h.out.map Mv.value))).getD 0)
       (h.out.all Mv.euroEmt)])
  else if h.fIn = [] ∧ sameKind h.out h.inn = true then [.swap (coins h.out) (gots h.inn) (paidOf h.fOut)]
  else
    let vin := sumV (h.inn.map Mv.value)
    let mIn := if h.fIn ≠ [] then sumV (h.fIn.map Money.value) else some 0
    let mOut := if h.fOut ≠ [] then sumV (h.fOut.map Money.value) else some 0
    let proceeds : Option ℚ := match vin, mIn, mOut with
      | some a, some b, some c => some (max (a + b - c) 0)
      | _, _, _ => none
    .dispose (coins h.out) ((proceeds.or (sumV (h.out.map Mv.value))).getD 0) (h.out.all Mv.euroEmt) ::
      buys h.inn ((vin.or (sumV (h.out.map Mv.value))).getD 0)

/-- **IT-2** Crypto for crypto of the same kind (both sides coins, or both e-money tokens) with no money received: one
untaxed swap, with the money paid on top (when known and above 0) added to the cost carried. -/
theorem same_kind_untaxed (h : SwapH) (hk : h.keepsCost = false) (ho : h.out ≠ []) (hi : h.inn ≠ [])
    (hf : h.fIn = []) (hs : sameKind h.out h.inn = true) :
    classify h = [.swap (coins h.out) (gots h.inn) (paidOf h.fOut)] := by
  simp [classify, hk, ho, hi, hf, hs]

/-- **IT-3** A coin swapped into or out of an e-money token (one side tokens, the other coins), with no money: a taxable
exchange at the value of what came in (never below 0), and what came in is bought at that value. -/
theorem emt_exchange_taxed (h : SwapH) (v : ℚ) (hk : h.keepsCost = false) (ho : h.out ≠ []) (hi : h.inn ≠ [])
    (hf : h.fIn = []) (hfo : h.fOut = []) (hs : sameKind h.out h.inn = false)
    (hv : sumV (h.inn.map Mv.value) = some v) :
    classify h = .dispose (coins h.out) (max v 0) (h.out.all Mv.euroEmt) :: buys h.inn v := by
  simp [classify, hk, ho, hi, hf, hfo, hs, hv]

/-- **IT-3** Crypto sold for money (outside the 2026 euro e-money token rule): a sale at the money received. -/
theorem sale_for_money (h : SwapH) (m : ℚ) (hk : h.keepsCost = false) (ho : h.out ≠ []) (hi : h.inn = [])
    (hf : h.fIn ≠ []) (hr : euroRedeem h = false) (hm : sumV (h.fIn.map Money.value) = some m) :
    classify h = [.dispose (coins h.out) m (h.out.all Mv.euroEmt)] := by
  simp [classify, hk, ho, hi, hf, hr, hm]

/-- **IT-2** (where the code differs from "money paid on top") Money received with a swap of the same kind makes the
whole swap a taxable exchange: the first op is a sale of the coins given. -/
theorem money_in_taxed (h : SwapH) (hk : h.keepsCost = false) (ho : h.out ≠ []) (hi : h.inn ≠ [])
    (hf : h.fIn ≠ []) : ∃ p e rest, classify h = .dispose (coins h.out) p e :: rest := by
  simp only [classify, hk, ho, hi, hf, Bool.false_eq_true, if_false, ne_eq, not_false_eq_true, false_and]
  exact ⟨_, _, _, rfl⟩

/-- **IT-10** From 2026, euro e-money tokens turned into euros (L. 199/2025 art. 1 c. 28): the coins go with no line, so
no gain or loss. -/
theorem euro_redeem_no_gain (h : SwapH) (hk : h.keepsCost = false) (ho : h.out ≠ []) (hi : h.inn = [])
    (hf : h.fIn ≠ []) (hy : 2026 ≤ h.year) (he : h.out.all Mv.euroEmt = true) (hr : h.fIn.all Money.eur = true) :
    classify h = [.drop (coins h.out)] := by
  have : euroRedeem h = true := by simp [euroRedeem, hy, he, hr]
  simp [classify, hk, ho, hi, hf, this]

/-- **IT-10** The coins dropped make no line (and leave the stacks as a sale would). -/
theorem drop_no_line (st : Stacks) (gave : List Coin) : (step st (.drop gave)).2 = none := rfl

/-- **IT-10** Before 2026 the same redemption is a sale at the euros received, marked a euro e-money token's. -/
theorem euro_redeem_2025_taxed (h : SwapH) (m : ℚ) (hk : h.keepsCost = false) (ho : h.out ≠ []) (hi : h.inn = [])
    (hf : h.fIn ≠ []) (hy : h.year ≤ 2025) (hm : sumV (h.fIn.map Money.value) = some m) :
    classify h = [.dispose (coins h.out) m (h.out.all Mv.euroEmt)] := by
  have : euroRedeem h = false := by simp [euroRedeem]; omega
  exact sale_for_money h m hk ho hi hf this hm

/-- **IT-10** Euros (or any money) turned into tokens: only buys at the money paid, no line. -/
theorem bought_with_money (h : SwapH) (p : ℚ) (hk : h.keepsCost = false) (ho : h.out = []) (hi : h.inn ≠ [])
    (hf : h.fOut ≠ []) (hp : sumV (h.fOut.map Money.value) = some p) :
    classify h = buys h.inn p := by
  simp [classify, hk, ho, hi, hf, hp]

def Op.cost : Op → ℚ
  | .buy _ _ c => c
  | _ => 0

/-- **IT-3** What came in is bought for exactly the total, split by value (equally when a value is missing). -/
theorem buys_total (ins : List Mv) (total : ℚ) (h : ins ≠ []) : ((buys ins total).map Op.cost).sum = total := by
  have := portion_sum total (ins.map Mv.value) (by simpa using h)
  rw [List.map_map] at this
  simpa [buys, Op.cost, Function.comp_def] using this

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

/-- One year of `itYears` from its net and the losses on hand: `expired` is what drops out of the pool unused. -/
def yearStep (year : ℕ) (net : ℚ) (pool : List Entry) : YearOut :=
  { gain := yGain year (euros net), loss := yLoss year (euros net),
    used := (use year (yGain year (euros net)) pool).1,
    base := (use year (yGain year (euros net)) pool).2.2,
    expired := amt ((use year (yGain year (euros net)) pool).2.1.filter (fun e => !keep year e)),
    residues := (use year (yGain year (euros net)) pool).2.1.filter (keep year) ++
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
  simp [yearStep, yGain, yLoss, threshold, euros, use, keep]; norm_num

/-- **IT-6** Agenzia delle Entrate FAQ (the app's test): net gains of €2,500 in 2024 are taxed on the €500 over
€2,000, at 26%: €130. -/
theorem faq_2024 :
    (yearStep 2024 2500 []).gain = 500 ∧ (yearStep 2024 2500 []).base = 500 ∧ tax2025 (yearStep 2024 2500 []) = 130 := by
  simp [yearStep, yGain, yLoss, threshold, euros, use, tax2025, centsUp]; norm_num

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
  have h1 := use_conserves year (yGain year (euros net)) pool
  have h2 := filter_split (keep year) (use year (yGain year (euros net)) pool).2.1
  have h3 := yLoss_nonneg year (euros net)
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
    (∀ e ∈ (use year (yGain year (euros net)) pool).2.1, keep year e = true → year + 1 ≤ e.yr + 4) ∧
    (∀ e ∈ (use year (yGain year (euros net)) pool).2.1, keep year e = false → 0 < e.amount → e.yr + 4 < year + 1) := by
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
  norm_num [runYears, yearStep, yGain, yLoss, threshold, euros, use, keep]

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
  have := avail_nonneg year pool
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
  exact_mod_cast (show max (yGain year (euros a) - avail year pool) 0 ≤ max (yGain year (euros b) - avail year pool) 0
    by omega)

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

/-- `itYears`' split of the base from 2026: (at 26%, at 33%). The euro e-money token net (whole euros, not below 0)
is taxed at 26% up to the base; the rest of the base at 33%. Earlier losses so come off the 33% part first: a KANON
choice the report states, which no source settles. Before 2026 all of the base is at 26%. -/
def split (year : ℕ) (base : ℤ) (emt : ℚ) : ℤ × ℤ :=
  if 2026 ≤ year then (min (max (euros emt) 0) base, base - min (max (euros emt) 0) base) else (base, 0)

/-- `itYears`' tax (years from 2023): 26% of the first part plus 33% of the second, rounded up to the cent. -/
def yearTaxSplit (year : ℕ) (base : ℤ) (emt : ℚ) : ℚ :=
  centsUp (((split year base emt).1 : ℚ) * (26 / 100) + ((split year base emt).2 : ℚ) * (33 / 100))

/-- **IT-9** The parts add up to the base and, for a base not below 0, neither is below 0; the 26% part is the euro
e-money token net up to the base (losses off the 33% part first). -/
theorem split_spec (year : ℕ) (base : ℤ) (emt : ℚ) (hb : 0 ≤ base) :
    (split year base emt).1 + (split year base emt).2 = base ∧ 0 ≤ (split year base emt).1 ∧
      0 ≤ (split year base emt).2 ∧
      (2026 ≤ year → (split year base emt).1 = min (max (euros emt) 0) base) := by
  unfold split
  split_ifs with h
  · refine ⟨by ring, by omega, by omega, fun _ => rfl⟩
  · exact ⟨by ring, hb, le_refl _, fun h' => absurd h' h⟩

/-- **IT-9** To 2025 the tax is 26% of the base, as `tax2025`. -/
theorem split_before_2026 (year : ℕ) (net : ℚ) (pool : List Entry) (emt : ℚ) (h : year ≤ 2025) :
    yearTaxSplit year (yearStep year net pool).base emt = tax2025 (yearStep year net pool) := by
  unfold yearTaxSplit split tax2025
  rw [if_neg (by omega)]; simp

/-- **IT-9** From 2026, with no euro e-money token gain the whole base is at 33%. -/
theorem split_no_emt (year : ℕ) (base : ℤ) (emt : ℚ) (hy : 2026 ≤ year) (hb : 0 ≤ base) (he : euros emt ≤ 0) :
    yearTaxSplit year base emt = centsUp ((base : ℚ) * (33 / 100)) := by
  unfold yearTaxSplit split
  rw [if_pos hy, max_eq_right he, min_eq_left hb]; simp

/-- **IT-9** From 2026, when the euro e-money token net covers the base, the whole base is at 26%. -/
theorem split_all_emt (year : ℕ) (base : ℤ) (emt : ℚ) (hy : 2026 ≤ year) (hb : 0 ≤ base) (he : base ≤ euros emt) :
    yearTaxSplit year base emt = centsUp ((base : ℚ) * (26 / 100)) := by
  unfold yearTaxSplit split
  rw [if_pos hy, max_eq_left (by omega), min_eq_right he]; simp

/-- **IT-9** The tax is between 26% and 33% of the base (each rounded up to the cent). -/
theorem split_between (year : ℕ) (base : ℤ) (emt : ℚ) (hb : 0 ≤ base) :
    centsUp ((base : ℚ) * (26 / 100)) ≤ yearTaxSplit year base emt ∧
      yearTaxSplit year base emt ≤ centsUp ((base : ℚ) * (33 / 100)) := by
  obtain ⟨hs, h1, h2, -⟩ := split_spec year base emt hb
  have hs' : ((split year base emt).1 : ℚ) + (split year base emt).2 = base := by exact_mod_cast hs
  have h1' : (0 : ℚ) ≤ (split year base emt).1 := by exact_mod_cast h1
  have h2' : (0 : ℚ) ≤ (split year base emt).2 := by exact_mod_cast h2
  unfold yearTaxSplit
  constructor <;> apply centsUp_mono <;> rw [← hs'] <;> nlinarith

/-- **IT-9** Never below 0, and a bigger base never means less tax (same euro e-money token net). -/
theorem split_mono (year : ℕ) (a b : ℤ) (emt : ℚ) (ha : 0 ≤ a) (h : a ≤ b) :
    0 ≤ yearTaxSplit year a emt ∧ yearTaxSplit year a emt ≤ yearTaxSplit year b emt := by
  have ha' : (0 : ℚ) ≤ a := by exact_mod_cast ha
  constructor
  · exact le_trans (centsUp_nonneg _ (by linarith)) (split_between year a emt ha).1
  · unfold yearTaxSplit
    apply centsUp_mono
    unfold split
    split_ifs with hy
    · have key : (min (max (euros emt) 0) b : ℤ) - min (max (euros emt) 0) a ≤ b - a := by omega
      have k2 : (min (max (euros emt) 0) a : ℤ) ≤ min (max (euros emt) 0) b := by omega
      have key' : ((min (max (euros emt) 0) b : ℤ) : ℚ) - ((min (max (euros emt) 0) a : ℤ) : ℚ) ≤ (b : ℚ) - a := by
        exact_mod_cast key
      have k2' : ((min (max (euros emt) 0) a : ℤ) : ℚ) ≤ ((min (max (euros emt) 0) b : ℤ) : ℚ) := by
        exact_mod_cast k2
      push_cast at key' k2' ⊢
      linarith
    · push_cast
      have : (a : ℚ) ≤ b := by exact_mod_cast h
      nlinarith

/-- A 2026 example: a base of €1,000 of which €400 is euro e-money token net: €104 + €198 = €302. -/
theorem split_2026_example : split 2026 1000 400 = (400, 600) ∧ yearTaxSplit 2026 1000 400 = 302 := by
  simp [split, yearTaxSplit, euros, centsUp]; norm_num

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

/-! ## Rule 15: tax if sold today (`itYearTax`, `itTaxOnSale`) -/

/-- `itRate` for a line not a euro e-money token's: 26% to 2025, 33% from 2026. `itYearTax` (tax if sold today) uses
it for every gain: it does not tell euro e-money tokens apart. -/
def rate (year : ℕ) : ℚ := if year ≤ 2025 then 26 / 100 else 33 / 100

/-- `itYearTax`: the year's tax from its net so far and the losses carried in (as one loss of last year). -/
def yearTax (year : ℕ) (net : ℚ) (carried : ℤ) : ℚ :=
  centsUp (((use year (yGain year (euros net)) (if 0 < carried then [⟨year - 1, carried⟩] else [])).2.2 : ℚ) *
    rate year)

/-- `itTaxOnSale`: the rise in the year's tax from one more sale, never below 0. -/
def taxOnSale (year : ℕ) (gain sofar : ℚ) (carried : ℤ) : ℚ :=
  max (yearTax year (sofar + gain) carried - yearTax year sofar carried) 0

theorem yearTax_mono (year : ℕ) (a b : ℚ) (carried : ℤ) (h : a ≤ b) : yearTax year a carried ≤ yearTax year b carried := by
  unfold yearTax
  apply centsUp_mono
  apply mul_le_mul_of_nonneg_right _ (by unfold rate; split_ifs <;> norm_num)
  rw [base_eq _ _ _ (yGain_nonneg _ _), base_eq _ _ _ (yGain_nonneg _ _)]
  have := yGain_mono year _ _ (euros_mono a b h)
  exact_mod_cast (show max (yGain year (euros a) - avail year _) 0 ≤ max (yGain year (euros b) - avail year _) 0
    by omega)

/-- **IT-15** Tax if sold today is the year's tax with the sale less without it, never below 0: exactly that rise for
a sale at a gain (or break-even), and 0 for a sale at a loss. -/
theorem tax_on_sale (year : ℕ) (gain sofar : ℚ) (carried : ℤ) :
    0 ≤ taxOnSale year gain sofar carried ∧
      (0 ≤ gain → taxOnSale year gain sofar carried = yearTax year (sofar + gain) carried - yearTax year sofar carried) ∧
      (gain ≤ 0 → taxOnSale year gain sofar carried = 0) := by
  refine ⟨le_max_right _ _, fun h => ?_, fun h => ?_⟩
  · have := yearTax_mono year sofar (sofar + gain) carried (by linarith)
    exact max_eq_left (by linarith)
  · have := yearTax_mono year (sofar + gain) sofar carried (by linarith)
    exact max_eq_right (by linarith)

/-- The app's test: in 2024, €1,500 of net gains so far and a sale at €1,000 more: €130 (26% of €500 over €2,000). -/
theorem tax_on_sale_2024 : taxOnSale 2024 1000 1500 0 = 130 := by
  simp [taxOnSale, yearTax, yGain, threshold, euros, use, rate, centsUp]; norm_num

/-! ## Rule 12: IVCA (DL 201/2011 art. 19 c. 18-bis; Modello Redditi PF, RW col. 33 and RW8) -/

/-- `itIvca`: 0.2% of the value, times the share owned, for the days held (a full year at most) over the days in the
year. -/
def ivca (value : ℚ) (days diy : ℕ) (share : ℚ := 1) : ℚ := value * (2 / 1000) * share * (min days diy : ℕ) / diy

/-- An RW line (an account): each coin's IVCA on its end value for its own days held, added and rounded to euros. -/
def accountIvca (cs : List (ℚ × ℕ)) (diy : ℕ) : ℤ := euros ((cs.map fun c => ivca c.1 c.2 diy).sum)

/-- RW8 col. 1: the sum of the accounts' whole-euro figures. -/
def rwTotal (accounts : List (List (ℚ × ℕ))) (diy : ℕ) : ℤ := (accounts.map (accountIvca · diy)).sum

/-- `itIvcaDue`: the year's IVCA in euros, nothing when €12 or less. -/
def ivcaDue (total : ℚ) : ℤ := if 12 < euros total then euros total else 0

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

/-- **IT-12** Nothing is due when the year's IVCA is €12 or less; over €12 all of it is. -/
theorem ivca_due (total : ℚ) :
    (euros total ≤ 12 → ivcaDue total = 0) ∧ (12 < euros total → ivcaDue total = euros total) := by
  unfold ivcaDue
  constructor
  · intro h; rw [if_neg (by omega)]
  · intro h; rw [if_pos h]

/-- The app's tests: €10,000 for 73 days of 365 is €4; €12.40 → nothing, €12.50 → €13, €20 → €20. -/
theorem ivca_examples :
    ivca 10000 73 365 = 4 ∧ ivcaDue (124 / 10) = 0 ∧ ivcaDue (125 / 10) = 13 ∧ ivcaDue 20 = 20 := by
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
