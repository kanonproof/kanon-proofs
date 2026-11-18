import KanonProofs.Spain

/-!
# Spain: one token is one crypto, and every change of token is a permuta (art. 37.1.h LIRPF; DGT V0612-26, V0525-25)

The app (kanon-app branch `claude/spain-34` at 5148f18, diff bf3c84f..5148f18): `src/lib/money-map/map.ts`
(`esKey`, lines 106-121; `toEvents(hs, fees, true)`, lines 536-700, its permuta branch lines 607-620 and its
same-token move lines 621-629; the swap's price, line 575), `src/lib/engine/lots.ts` (`runLedger(events, "FIFO",
"universal")`, line 147), `src/lib/report/es.ts` (each disposal is a sale of its lot for art. 33.5.e, line 135) and
`src/lib/engine/es.ts` (`esWash`, lines 213-260). Tests: `src/lib/report/es.test.ts`, lines 295-425.

Rules modelled, in exact fractions:

* PER-1: a move between two different `esKey`s (a wrap, a liquid staking deposit, a bridge that delivers another
  token, a vault's or a pool's token) is a disposal of the full quantity given, valued at `V` = the higher of the two
  values that day (one known: that one; neither: 0), and an acquisition of what came in at cost `V`. The network fee of
  its transaction comes off the proceeds up to `V`; what is left of it goes on the new token's cost.
* PER-2: a move within one `esKey` (between the person's own wallets, or the same issuer's coin on two networks, the
  `ES_SAME` list) is no sale: the pool keeps every coin, every cent of cost and every lot's day and place.
* PER-3: first in first out stays per `esKey` (art. 37.2): a permuta reads and changes only the two tokens' pools.
* PER-4: art. 33.5.e: a loss is put off only by a purchase of the same `esKey` (within the year after the sale); a
  permuta out of coins bought again counts the loss put off in proportion to the coins FIFO takes from them, and
  what is counted plus what still waits is what was put off.
* PER-5: a chain of permutas, each giving the whole holding (ETH → rETH → ETH): the gains are `V − cost` per step, the
  cost of each step the `V` of the one before, and the last token costs the last `V`.
* PER-6: the cases of `es.test.ts`: the ETH → WETH wrap realising 2,000; the vault 1,007 for 1,000; the round trip
  (2,000 and 680, the ETH at 3,680); the price on one side; the 1.5 ETH partial wrap counting 500 with 500 waiting.
* PER-7: a higher `V` never lowers the step's gain, nor the new token's cost.

Where the model departs from the code:

* a token's `esKey` is a number; which tokens share one (`ES_SAME`, the aliases, a position's `standsFor`) is the
  app's data and is not modelled;
* a value (`value(m)`, amount × price) is an `Option ℚ`, `none` for no price; values are taken as ≥ 0;
* the swap branch (map.ts:566-605) with one coin on each side and no money is the same disposal and acquisition
  (`total = max(inValue, outValue)` at line 575, each side's one coin taking all of it); the money cases, swaps of
  several coins and the pool token minted for coins put in (`minted`) are not modelled here;
* the fee: `fee` is `feeOn.get(tx)` when the country allows fees and the transaction's fee is not used yet, else 0
  (a `network-move` has none); `share` is `fees.share` (1 for Spain's euro rule, `feeRuleFor`, map.ts:315);
* the same-token move with a gap (a bridge delivering less) gives up the gap as a fee at the coin's price, an "f"
  disposal; this file proves it is not a sale ("s");
* the ledger, the sale with missing coins at cost 0 (`sale`), the move (`move`) and `esWash`'s release
  (`release`) are `Kanon.Spain`'s, with the departures listed there; `seq` and ids are parameters.
-/

namespace Kanon.Spain.Permuta

open Kanon.Spain

/-! ## 1. The value of a permuta and the fee (map.ts:613-620) -/

/-- `worth` (map.ts:613): neither value known, 0; else the higher of the two, an unknown one read as 0. -/
def worth (vf vt : Option ℚ) : ℚ :=
  if vf = none ∧ vt = none then 0 else max (vf.getD 0) (vt.getD 0)

/-- A value is not below 0 when known. -/
def Nonneg (v : Option ℚ) : Prop := ∀ a, v = some a → 0 ≤ a

/-- `offSale` (map.ts:617): the fee's share, `fee × share`, never more than `worth`. -/
def offSale (share fee V : ℚ) : ℚ := min (fee * share) V

/-- The disposal's proceeds, `worth − offSale` (map.ts:618). -/
def proceeds (share fee V : ℚ) : ℚ := V - offSale share fee V

/-- The new token's cost, `worth + onCost`, `onCost = fee − offSale` (map.ts:617, 620). -/
def newCost (share fee V : ℚ) : ℚ := V + (fee - offSale share fee V)

/-- **PER-1** (map.ts:613, LIRPF 37.1.h, DGT V0612-26) Both values known: the higher of the two. -/
theorem worth_both (a b : ℚ) : worth (some a) (some b) = max a b := by simp [worth]

/-- **PER-1** (map.ts:613) Only the value of the coins given is known: that one. -/
theorem worth_from_only (a : ℚ) (h : 0 ≤ a) : worth (some a) none = a := by simp [worth, h]

/-- **PER-1** (map.ts:613) Only the value of the coins received is known: that one. -/
theorem worth_to_only (b : ℚ) (h : 0 ≤ b) : worth none (some b) = b := by simp [worth, h]

/-- **PER-1** (map.ts:613, 618) Neither value known: the coins given are sold for nothing, whatever the fee. -/
theorem worth_none (share fee : ℚ) (h : 0 ≤ fee * share) :
    worth none none = 0 ∧ proceeds share fee (worth none none) = 0 := by
  simp [worth, proceeds, offSale, h]

theorem getD_nonneg (v : Option ℚ) (h : Nonneg v) : 0 ≤ v.getD 0 := by
  cases v with
  | none => simp
  | some a => exact h a rfl

/-- **PER-1** (map.ts:613) With values not below 0, `V` is the higher of the two, an unknown one read as 0. -/
theorem worth_eq (vf vt : Option ℚ) (hf : Nonneg vf) (ht : Nonneg vt) :
    worth vf vt = max (vf.getD 0) (vt.getD 0) := by
  unfold worth; split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rfl

/-- **PER-1** (map.ts:613) `V` is not below 0 nor below either known value. -/
theorem worth_ge (vf vt : Option ℚ) (hf : Nonneg vf) (ht : Nonneg vt) :
    0 ≤ worth vf vt ∧ (∀ a, vf = some a → a ≤ worth vf vt) ∧ ∀ b, vt = some b → b ≤ worth vf vt := by
  rw [worth_eq vf vt hf ht]
  refine ⟨le_max_of_le_left (getD_nonneg vf hf), fun a ha => ?_, fun b hb => ?_⟩
  · subst ha; exact le_max_left _ _
  · subst hb; exact le_max_right _ _

/-- **PER-1** (map.ts:617-620) The fee, `0 ≤ share ≤ 1`: the proceeds are between 0 and `V`, the new cost is at
least `V`, and the fee is used once, part off the proceeds and the rest on the cost. -/
theorem fee_split (share fee V : ℚ) (hf : 0 ≤ fee) (hs0 : 0 ≤ share) (hs1 : share ≤ 1) (hV : 0 ≤ V) :
    0 ≤ proceeds share fee V ∧ proceeds share fee V ≤ V ∧ V ≤ newCost share fee V ∧
      (V - proceeds share fee V) + (newCost share fee V - V) = fee := by
  unfold proceeds newCost offSale
  have h1 : 0 ≤ fee * share := mul_nonneg hf hs0
  have h2 : fee * share ≤ fee := by nlinarith
  refine ⟨by linarith [min_le_right (fee * share) V], by linarith [le_min h1 hV],
    by linarith [min_le_left (fee * share) V], by ring⟩

/-- **PER-1** (map.ts:617-620) Spain's rule (`share` 1): a fee up to `V` comes off the proceeds and the new token
costs `V`; a larger fee leaves proceeds of 0 and the new token costs the fee. No fee: proceeds `V`, cost `V`. -/
theorem fee_spain (fee V : ℚ) (hV : 0 ≤ V) :
    (fee ≤ V → proceeds 1 fee V = V - fee ∧ newCost 1 fee V = V) ∧
      (V < fee → proceeds 1 fee V = 0 ∧ newCost 1 fee V = fee) ∧
      proceeds 1 0 V = V ∧ newCost 1 0 V = V := by
  unfold proceeds newCost offSale
  refine ⟨fun h => ?_, fun h => ?_, ?_, ?_⟩
  · rw [mul_one, min_eq_left h]; constructor <;> ring
  · rw [mul_one, min_eq_right h.le]; constructor <;> ring
  · simp [hV]
  · simp [hV]

/-- **PER-7** (map.ts:613-620) A higher `V` never lowers the proceeds, and never lowers the new token's cost. -/
theorem proceeds_mono (share fee V V' : ℚ) (h : V ≤ V') :
    proceeds share fee V ≤ proceeds share fee V' ∧ newCost share fee V ≤ newCost share fee V' := by
  have key : ∀ x, x - min (fee * share) x = max (x - fee * share) 0 := by
    intro x; rcases le_total (fee * share) x with h1 | h1
    · rw [min_eq_left h1, max_eq_left (by linarith)]
    · rw [min_eq_right h1, max_eq_right (by linarith)]; ring
  have m : max (V - fee * share) 0 ≤ max (V' - fee * share) 0 := max_le_max (by linarith) le_rfl
  unfold proceeds newCost offSale
  constructor
  · rw [key, key]; exact m
  · have := key V; have := key V'; linarith

/-- **PER-7** (map.ts:613) A higher value on either side (a value where there was none, or a higher one) never
lowers `V`. -/
theorem worth_mono (vf vf' vt vt' : Option ℚ) (hf : Nonneg vf) (ht : Nonneg vt) (hf2 : Nonneg vf') (ht2 : Nonneg vt')
    (hf' : ∀ a, vf = some a → ∃ a', vf' = some a' ∧ a ≤ a') (ht' : ∀ b, vt = some b → ∃ b', vt' = some b' ∧ b ≤ b') :
    worth vf vt ≤ worth vf' vt' := by
  have g : ∀ v v' : Option ℚ, Nonneg v' → (∀ a, v = some a → ∃ a', v' = some a' ∧ a ≤ a') → v.getD 0 ≤ v'.getD 0 := by
    intro v v' hv' hm; cases v with
    | none => exact getD_nonneg v' hv'
    | some a => obtain ⟨a', e, ha⟩ := hm a rfl; rw [e]; exact ha
  rw [worth_eq _ _ hf ht, worth_eq _ _ hf2 ht2]
  exact max_le_max (g _ _ hf2 hf') (g _ _ ht2 ht')

/-! ## 2. The events of a move, and Spain's ledger over them -/

/-- One coin out and one coin in (an `own-move` or a `network-move`, or a swap of one coin for one coin): the
tokens' `esKey`s (`key(h.from)`, `key(h.to)`), the coins given and received, the two values that day (`value`,
`none` for no price), the fee of its transaction, the wallets, the day, and the ids and places the ledger gives the
events. -/
structure Change where
  src : ℕ
  dst : ℕ
  qty : ℚ
  toQty : ℚ
  vf : Option ℚ
  vt : Option ℚ
  fee : ℚ
  wallet : ℕ
  toWallet : ℕ
  date : ℕ
  saleId : ℕ
  saleSeq : ℕ
  buyId : ℕ
  buySeq : ℕ

/-- A disposal's kind: a sale ("s", on the Renta's boxes and art. 33.5.e) or a fee given up ("f"). -/
inductive Tag
  | sale
  | fee
  deriving DecidableEq

/-- The ledger's events: a disposal (from the pool, missing coins at cost 0), an acquisition of a lot, a move
between the person's own wallets within one pool. -/
inductive Ev
  | dispose (tag : Tag) (asset : ℕ) (qty proceeds : ℚ) (id wallet date seq : ℕ)
  | acquire (asset : ℕ) (lot : Lot)
  | transfer (asset : ℕ) (qty : ℚ) (id dest date seq : ℕ)

/-- The new token's lot (map.ts:620): the coins received, at `V` plus what of the fee is left. -/
def newLot (share : ℚ) (c : Change) : Lot :=
  ⟨c.buyId, c.toWallet, c.date, c.toQty, newCost share c.fee (worth c.vf c.vt), (c.buySeq, 0)⟩

/-- `toEvents(hs, fees, true)` for one change: another token, a permuta (map.ts:607-620); the same token, a move when
the wallets differ and the gap given up as a fee at the coin's price (map.ts:621-629). -/
def toEvents (share : ℚ) (c : Change) : List Ev :=
  if c.src ≠ c.dst then
    [.dispose .sale c.src c.qty (proceeds share c.fee (worth c.vf c.vt)) c.saleId c.wallet c.date c.saleSeq,
      .acquire c.dst (newLot share c)]
  else
    (if c.wallet ≠ c.toWallet then [.transfer c.src (min c.toQty c.qty) c.saleId c.toWallet c.date c.saleSeq]
      else []) ++
    (if 0 < c.qty - c.toQty then
      [.dispose .fee c.src (c.qty - c.toQty) (c.vf.getD 0 / c.qty * (c.qty - c.toQty)) c.buyId c.wallet c.date c.buySeq]
      else [])

/-- Spain's ledger: one pool per `esKey`. -/
abbrev Book := ℕ → List Lot

/-- `runLedger(events, "FIFO", "universal")` on one event: the book after it, and each disposal's kind and gain
(proceeds less the FIFO cost of the coins it took). -/
def apply (B : Book) : Ev → Book × List (Tag × ℚ)
  | .dispose t k q p id w d s =>
    (Function.update B k (sale (B k) q id w d s).2, [(t, p - ((sale (B k) q id w d s).1.map Pick.basis).sum)])
  | .acquire k l => (Function.update B k (add l (B k)), [])
  | .transfer k q id dest d s => (Function.update B k (move (B k) q id dest d s), [])

def run (B : Book) : List Ev → Book × List (Tag × ℚ)
  | [] => (B, [])
  | e :: es => ((run (apply B e).1 es).1, (apply B e).2 ++ (run (apply B e).1 es).2)

theorem run_append (B : Book) (es fs : List Ev) :
    run B (es ++ fs) = ((run (run B es).1 fs).1, (run B es).2 ++ (run (run B es).1 fs).2) := by
  induction es generalizing B with
  | nil => simp [run]
  | cons e es ih => simp [run, ih]

/-- The FIFO cost of a permuta's coins: the cost of the lots the sale takes (missing coins at 0). -/
def fifoCost (B : Book) (c : Change) : ℚ :=
  ((sale (B c.src) c.qty c.saleId c.wallet c.date c.saleSeq).1.map Pick.basis).sum

/-- The permuta's gain: `V` less what of the fee comes off, less the FIFO cost of the coins given. -/
def gain (share : ℚ) (B : Book) (c : Change) : ℚ := proceeds share c.fee (worth c.vf c.vt) - fifoCost B c

/-- A sale with missing coins at cost 0 takes exactly the coins given. -/
theorem sale_takes (ls : List Lot) (q : ℚ) (id w date seq : ℕ) (hq : 0 ≤ q) :
    ((sale ls q id w date seq).1.map Pick.take).sum = q := by
  unfold sale; split_ifs with h
  · exact sell_exact _ _ hq (by rw [held_add]; simp)
  · exact sell_exact _ _ hq (not_lt.mp h)

/-- **PER-1, PER-3** (map.ts:607-620; lots.ts:147) A change of token is a disposal of all the coins given, oldest first
in the given token's pool (missing coins at cost 0), with gain `V − offSale − FIFO cost`, and an acquisition of the
coins received at `V + onCost` in the received token's pool; every other token's pool is untouched. -/
theorem permuta_spec (share : ℚ) (B : Book) (c : Change) (hne : c.src ≠ c.dst) (hq : 0 ≤ c.qty) :
    (run B (toEvents share c)).2 = [(.sale, gain share B c)] ∧
      ((sale (B c.src) c.qty c.saleId c.wallet c.date c.saleSeq).1.map Pick.take).sum = c.qty ∧
      (run B (toEvents share c)).1 c.src = (sale (B c.src) c.qty c.saleId c.wallet c.date c.saleSeq).2 ∧
      (run B (toEvents share c)).1 c.dst = add (newLot share c) (B c.dst) ∧
      (newLot share c).qty = c.toQty ∧ (newLot share c).cost = newCost share c.fee (worth c.vf c.vt) ∧
      ∀ j, j ≠ c.src → j ≠ c.dst → (run B (toEvents share c)).1 j = B j := by
  have hne' : c.dst ≠ c.src := fun h => hne h.symm
  refine ⟨?_, sale_takes _ _ _ _ _ _ hq, ?_, ?_, rfl, rfl, fun j h1 h2 => ?_⟩
  · simp [toEvents, hne, run, apply, gain, fifoCost]
  · simp [toEvents, hne, run, apply]
  · simp [toEvents, hne, run, apply, Function.update_of_ne hne']
  · simp [toEvents, hne, run, apply, Function.update_of_ne h1, Function.update_of_ne h2]

/-- **PER-1** (map.ts:613-620) With no fee: the coins given are sold for `V`, the gain is `V` less their FIFO cost,
and the coins received cost `V`. -/
theorem permuta_no_fee (share : ℚ) (B : Book) (c : Change) (hf : c.fee = 0) (hvf : Nonneg c.vf)
    (hvt : Nonneg c.vt) :
    gain share B c = worth c.vf c.vt - fifoCost B c ∧ (newLot share c).cost = worth c.vf c.vt := by
  have hV := (worth_ge _ _ hvf hvt).1
  simp [gain, newLot, newCost, proceeds, offSale, hf, hV]

/-- **PER-3** (lots.ts:147, 285-308) A permuta keeps both pools oldest first. -/
theorem permuta_sorted (share : ℚ) (B : Book) (c : Change) (hne : c.src ≠ c.dst) (h1 : Sorted (B c.src))
    (h2 : Sorted (B c.dst)) :
    Sorted ((run B (toEvents share c)).1 c.src) ∧ Sorted ((run B (toEvents share c)).1 c.dst) := by
  have hne' : c.dst ≠ c.src := fun h => hne h.symm
  refine ⟨?_, ?_⟩
  · simp only [toEvents, hne, ne_eq, not_false_eq_true, if_true, run, apply, Function.update_self,
      Function.update_of_ne hne]
    unfold sale; split_ifs
    · exact sell_sorted _ _ (add_sorted _ _ h1)
    · exact sell_sorted _ _ h1
  · simp only [toEvents, hne, ne_eq, not_false_eq_true, if_true, run, apply, Function.update_self,
      Function.update_of_ne hne']
    exact add_sorted _ _ h2

/-- **PER-7** (map.ts:613-620) The same permuta at a higher `V` (higher values that day, same coins and fee): its
gain is not lower, nor is the new token's cost. -/
theorem gain_mono (share : ℚ) (B : Book) (c : Change) (vf' vt' : Option ℚ)
    (h : worth c.vf c.vt ≤ worth vf' vt') :
    gain share B c ≤ gain share B { c with vf := vf', vt := vt' } ∧
      (newLot share c).cost ≤ (newLot share { c with vf := vf', vt := vt' }).cost := by
  have := proceeds_mono share c.fee _ _ h
  simp only [gain, fifoCost, newLot]
  exact ⟨by linarith [this.1], this.2⟩

/-- **PER-2** (map.ts:621-629) A move within one token makes no sale: none of its events is a sale. -/
theorem same_key_no_sale (share : ℚ) (c : Change) (h : c.src = c.dst) :
    ∀ e ∈ toEvents share c, ∀ k q p id w d s, e ≠ .dispose .sale k q p id w d s := by
  intro e he k q p id w d s
  simp only [toEvents, h, ne_eq, not_true_eq_false, if_false] at he
  rcases List.mem_append.mp he with he | he
  · split_ifs at he <;> simp at he; subst he; simp
  · split_ifs at he <;> simp at he; subst he; simp

/-- **PER-2** (map.ts:621-629; DGT V0648-24) A move within one token, with no coins lost on the way and no more than
the pool holds: no disposal, the pool keeps every coin and every cent of cost, a later sale of any amount takes the
same coins at the same cost from the same lots (each lot keeping its day), and every other pool is untouched. -/
theorem same_key_keeps (share : ℚ) (B : Book) (c : Change) (h : c.src = c.dst) (hgap : c.qty ≤ c.toQty)
    (hle : c.qty ≤ held (B c.src)) (hR : Reach (B c.src)) :
    (run B (toEvents share c)).2 = [] ∧
      held ((run B (toEvents share c)).1 c.src) = held (B c.src) ∧
      totalCost ((run B (toEvents share c)).1 c.src) = totalCost (B c.src) ∧
      (∀ r, ((sell ((run B (toEvents share c)).1 c.src) r).1.map Pick.basis).sum = ((sell (B c.src) r).1.map Pick.basis).sum ∧
        ∀ k, takeAt k (sell ((run B (toEvents share c)).1 c.src) r).1 = takeAt k (sell (B c.src) r).1 ∧
          basisAt k (sell ((run B (toEvents share c)).1 c.src) r).1 = basisAt k (sell (B c.src) r).1) ∧
      ∀ j, j ≠ c.src → (run B (toEvents share c)).1 j = B j := by
  have g := good_of_reach hR
  have hng : ¬ (0 < c.qty - c.toQty) := by linarith
  have hmin : min c.toQty c.qty = c.qty := min_eq_right hgap
  have hT : toEvents share c = (if c.wallet ≠ c.toWallet then
      [Ev.transfer c.src (min c.toQty c.qty) c.saleId c.toWallet c.date c.saleSeq] else []) := by
    unfold toEvents; rw [if_neg (not_not.mpr h), if_neg hng, List.append_nil]
  rw [hT, hmin]
  by_cases hw : c.wallet = c.toWallet
  · rw [if_neg (not_not.mpr hw)]
    simp [run]
  · rw [if_pos hw]
    simp only [run, apply, List.append_nil, Function.update_self]
    have hk := move_keeps (B c.src) c.qty c.saleId c.toWallet c.date c.saleSeq g.2.1 g.1
    exact ⟨trivial, by rw [hk.1, max_eq_left hle], hk.2.1,
      fun r => move_same_sale _ _ r _ _ _ _ hR hle, fun j hj => Function.update_of_ne hj _ _⟩

/-! ## 3. Art. 33.5.e: a loss put off only by the same token; a permuta counts it (es.ts:135; engine/es.ts:213-260) -/

/-- **PER-4** (engine/es.ts:221-227) A purchase can put a loss off only when it is of the same token (`esKey`), from
the sale's day to the same day a year later. -/
theorem eligible_same_key (l : Loss) (b : Buy) (h : eligible l b = true) :
    b.asset = l.asset ∧ l.date ≤ b.date ∧ b.date ≤ yearAfter l.date := by
  simp [eligible] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩

theorem matchLoss_other (l : Loss) (need : ℚ) (fs : List (Buy × ℚ)) (h : ∀ x ∈ fs, x.1.asset ≠ l.asset) :
    (matchLoss l need fs).2 = [] := by
  induction fs generalizing need with
  | nil => simp [matchLoss]
  | cons bf rest ih =>
    obtain ⟨b, free⟩ := bf
    have hb : eligible l b = false := by
      have := h (b, free) (by simp); simp [eligible, this]
    have ih' := fun need => ih need (fun x hx => h x (List.mem_cons_of_mem _ hx))
    unfold matchLoss; split_ifs with h0 h1
    · rfl
    · rw [hb] at h1; exact absurd h1.1 (by simp)
    · exact ih' need

/-- **PER-4** (engine/es.ts:221-232; es.test.ts:401-412) Purchases of other tokens only (WETH after a loss on ETH)
put nothing off: the loss counts in full in its year, and no part waits on any purchase. -/
theorem other_key_defers_nothing (st : W1) (l : Loss) (h : ∀ x ∈ st.free, x.1.asset ≠ l.asset) :
    (washLoss st l).deferred = st.deferred ∧ (washLoss st l).parts = st.parts := by
  have hm := matchLoss_other l l.qty st.free h
  unfold washLoss
  simp only [hm, List.map_nil, List.sum_nil, le_refl, ite_true]
  split_ifs <;> exact ⟨rfl, rfl⟩

/-- The rows a permuta's disposal adds to `esWash`'s sales (es.ts:135): one per lot FIFO took, its coins. -/
def rowsOf (date : ℕ) (ps : List Pick) : List SaleOfLot := ps.map fun p => ⟨p.lot.id, date, p.take⟩

/-- `esWash`'s second loop over a permuta's rows (engine/es.ts:242-260), the counting by year left aside. -/
def releaseAll : List SaleOfLot → List Part → List Part × List (ℕ × ℕ × ℚ)
  | [], ps => (ps, [])
  | s :: ss, ps => ((releaseAll ss (release s.lot s.qty ps).1).1,
      (release s.lot s.qty ps).2 ++ (releaseAll ss (release s.lot s.qty ps).1).2)

/-- **PER-4** (engine/es.ts:242-260) A permuta's rows count the loss put off and leave the rest waiting: for each
loss, what is counted plus what still waits is what waited before, nothing counted is below 0, and the parts stay
as they should be. -/
theorem permuta_release_conserves (ss : List SaleOfLot) (ps : List Part) (hg : ∀ p ∈ ps, Good p) :
    (∀ L, waiting L (releaseAll ss ps).1 + evSum L (releaseAll ss ps).2 = waiting L ps) ∧
      (∀ p ∈ (releaseAll ss ps).1, Good p) ∧ ∀ e ∈ (releaseAll ss ps).2, 0 ≤ e.2.2 := by
  induction ss generalizing ps with
  | nil => exact ⟨fun L => by simp [releaseAll, evSum], by simpa [releaseAll] using hg, by simp [releaseAll]⟩
  | cons s ss ih =>
    obtain ⟨a1, b1, c1⟩ := release_spec s.lot s.qty ps hg
    obtain ⟨a2, b2, c2⟩ := ih _ b1
    refine ⟨fun L => ?_, b2, fun e he => ?_⟩
    · have e1 := a1 L; have e2 := a2 L
      simp only [releaseAll]
      have : evSum L ((release s.lot s.qty ps).2 ++ (releaseAll ss (release s.lot s.qty ps).1).2) =
          evSum L (release s.lot s.qty ps).2 + evSum L (releaseAll ss (release s.lot s.qty ps).1).2 := by
        simp [evSum]
      rw [this]; linarith
    · simp only [releaseAll, List.mem_append] at he
      rcases he with he | he
      · exact c1 e he
      · exact c2 e he

/-- **PER-4** (engine/es.ts:250-255) A permuta taking `t` of the `qty` coins bought again that carry a part of a loss
(none of them sold before, `0 < t < qty`) counts `amount × t ÷ qty` of it and leaves the rest waiting. Coins from any
other lot count nothing of it. -/
theorem permuta_release_share (p : Part) (t : ℚ) (hg : Good p) (hl : p.left = p.amount) (hq : p.qLeft = p.qty)
    (ht0 : 0 < t) (ht : t < p.qty) :
    release p.buy t [p] = ([{ p with qLeft := p.qty - t, left := p.amount - p.amount * t / p.qty }],
      [(p.loss, p.year, p.amount * t / p.qty)]) ∧
      ∀ lot, lot ≠ p.buy → release lot t [p] = ([p], []) := by
  obtain ⟨_, ha, hpos⟩ := hg
  have hle : p.amount * t / p.qty ≤ p.amount := by
    rw [div_le_iff₀ hpos]; nlinarith
  refine ⟨?_, fun lot hlot => ?_⟩
  · have h1 : ¬ t ≤ 0 := not_le.mpr ht0
    have h2 : ¬ p.qLeft ≤ 0 := by rw [hq]; linarith
    have h3 : min t p.qLeft = t := by rw [hq]; exact min_eq_left ht.le
    have h4 : ¬ p.qLeft - t ≤ 0 := by rw [hq]; linarith
    simp only [release, ne_eq, not_true_eq_false, if_false, h1, h2, h3, h4, hl, min_eq_right hle]
    simp [hq]
  · simp [release, Ne.symm hlot]

/-! ## 4. A chain of permutas, each giving the whole holding (ETH → rETH → ETH) -/

/-- The gains of a chain: `V − cost` per step, each step's cost the `V` of the one before. -/
def chainGains (c0 : ℚ) : List ℚ → List ℚ
  | [] => []
  | V :: Vs => (V - c0) :: chainGains V Vs

/-- The last token's cost: the last `V`. -/
def lastCost (c0 : ℚ) : List ℚ → ℚ
  | [] => c0
  | V :: Vs => lastCost V Vs

/-- Each step gives all the coins of the token held (one lot), for another token, with no fee. -/
def Whole : ℕ → ℚ → List Change → Prop
  | _, _, [] => True
  | k, q, c :: cs => c.src = k ∧ c.dst ≠ k ∧ c.qty = q ∧ 0 < c.toQty ∧ c.fee = 0 ∧ Nonneg c.vf ∧ Nonneg c.vt ∧
      Whole c.dst c.toQty cs

/-- The book holds one lot, of token `k`, and nothing else. -/
def Only (B : Book) (k : ℕ) (l : Lot) : Prop := B k = [l] ∧ ∀ j, j ≠ k → B j = []

theorem whole_step (share : ℚ) (B : Book) (k : ℕ) (l : Lot) (c : Change) (hB : Only B k l) (hl : 0 < l.qty)
    (hs : c.src = k) (hd : c.dst ≠ k) (hq : c.qty = l.qty) (hf : c.fee = 0) (hvf : Nonneg c.vf) (hvt : Nonneg c.vt) :
    (run B (toEvents share c)).2 = [(.sale, worth c.vf c.vt - l.cost)] ∧
      Only (run B (toEvents share c)).1 c.dst (newLot share c) ∧ (newLot share c).cost = worth c.vf c.vt := by
  have hne : c.src ≠ c.dst := by rw [hs]; exact Ne.symm hd
  obtain ⟨h1, _, h3, h4, _, _, h7⟩ := permuta_spec share B c hne (by rw [hq]; exact hl.le)
  have hnf := permuta_no_fee share B c hf hvf hvt
  have hcost : fifoCost B c = l.cost := by
    have hh : ¬ held [l] < l.qty := by simp [held]
    simp [fifoCost, hs, hB.1, hq, sale, sell, held, not_le.mpr hl, hl.ne']
  refine ⟨by rw [h1, hnf.1, hcost], ⟨?_, fun j hj => ?_⟩, hnf.2⟩
  · rw [h4, hB.2 _ hd]; rfl
  · by_cases hjk : j = c.src
    · rw [hjk, h3, hs, hB.1]; simp [sale, held, sell, hq, not_le.mpr hl]
    · rw [h7 j hjk hj]; exact hB.2 j (by rw [← hs]; exact hjk)

/-- **PER-5** (map.ts:607-620; es.test.ts:313-326) A chain of permutas, each giving all the coins of the token held
for another token, with no fee: the gains are `V − cost` step by step, each step's cost the `V` before it, and in
the end the book holds one lot, of the last token received, at the last `V`. -/
theorem chain_gains (share : ℚ) (cs : List Change) :
    ∀ (B : Book) (k : ℕ) (l : Lot), Only B k l → 0 < l.qty → Whole k l.qty cs →
      ((run B (cs.flatMap (toEvents share))).2.map Prod.snd = chainGains l.cost (cs.map fun c => worth c.vf c.vt) ∧
        (∀ x ∈ (run B (cs.flatMap (toEvents share))).2, x.1 = .sale)) ∧
      ∃ k' l', Only (run B (cs.flatMap (toEvents share))).1 k' l' ∧
        l'.cost = lastCost l.cost (cs.map fun c => worth c.vf c.vt) := by
  induction cs with
  | nil => intro B k l hB _ _; exact ⟨by simp [run, chainGains], k, l, by simpa [run] using hB, rfl⟩
  | cons c cs ih =>
    intro B k l hB hl hw
    obtain ⟨hs, hd, hq, ht, hf, hvf, hvt, hw'⟩ := hw
    obtain ⟨e1, e2, e3⟩ := whole_step share B k l c hB hl hs hd hq hf hvf hvt
    have hl' : 0 < (newLot share c).qty := ht
    obtain ⟨⟨i1, i2⟩, k', l', i3, i4⟩ := ih _ _ _ e2 hl' hw'
    rw [List.flatMap_cons, run_append, e1]
    refine ⟨⟨?_, fun x hx => ?_⟩, k', l', i3, ?_⟩
    · simp only [List.map_cons, List.cons_append, List.nil_append, List.map, chainGains]
      rw [i1, e3]
    · simp only [List.cons_append, List.nil_append, List.mem_cons] at hx
      rcases hx with rfl | hx
      · rfl
      · exact i2 x hx
    · rw [i4, e3]; rfl

/-- **PER-5** Summed: the gains of the chain add up to the last `V` less the first cost. -/
theorem chainGains_sum (c0 : ℚ) (Vs : List ℚ) : (chainGains c0 Vs).sum = lastCost c0 Vs - c0 := by
  induction Vs generalizing c0 with
  | nil => simp [chainGains, lastCost]
  | cons V Vs ih => simp [chainGains, lastCost, ih]

/-! ## 5. The cases of `es.test.ts` -/

/-- ETH (`esKey` 0) earned for 1,000 on base; WETH is `esKey` 1. -/
def ethBook : Book := Function.update (fun _ => []) 0 [⟨1, 0, 20250101, 1, 1000, (1, 0)⟩]

/-- **PER-6** (es.test.ts:328-340) ETH wrapped 1:1 into WETH, both worth 3,000: a permuta realising 2,000, the WETH
costing 3,000. -/
theorem eth_weth_wrap :
    let c : Change := ⟨0, 1, 1, 1, some 3000, some 3000, 0, 0, 0, 20250301, 2, 2, 3, 3⟩
    (run ethBook (toEvents 1 c)).2 = [(.sale, 2000)] ∧
      (run ethBook (toEvents 1 c)).1 1 = [⟨3, 0, 20250301, 1, 3000, (3, 0)⟩] ∧ (run ethBook (toEvents 1 c)).1 0 = [] := by
  norm_num [ethBook, toEvents, run, apply, sale, held, sell, add, newLot, newCost, proceeds, offSale, worth_both, worth_from_only, (worth_none 1 0 (by norm_num)).1, max_def,
    Function.update]

/-- **PER-6** (es.test.ts:342-354) A vault deposit: 1,000 USDC (cost 1,000, worth 1,000) for 950 shares worth 1.06
each (1,007): sold for 1,007, a gain of 7, and the shares cost 1,007. -/
theorem vault_deposit :
    let B : Book := Function.update (fun _ => []) 5 [⟨1, 0, 20250101, 1000, 1000, (1, 0)⟩]
    let c : Change := ⟨5, 6, 1000, 950, some (1000 * 1), some (950 * (106 / 100)), 0, 0, 0, 20250301, 2, 2, 3, 3⟩
    worth c.vf c.vt = 1007 ∧ (run B (toEvents 1 c)).2 = [(.sale, 7)] ∧
      (run B (toEvents 1 c)).1 6 = [⟨3, 0, 20250301, 950, 1007, (3, 0)⟩] := by
  norm_num [toEvents, run, apply, sale, held, sell, add, newLot, newCost, proceeds, offSale, worth_both, worth_from_only, (worth_none 1 0 (by norm_num)).1, max_def, Function.update]

/-- **PER-6** (es.test.ts:313-326) ETH (cost 1,000) for 0.9 rETH: 1 ETH worth 3,000, the rETH 2,970, sold for 3,000;
then the 0.9 rETH (worth 3,600) for 1.15 ETH (3,680), sold for 3,680. Gains 2,000 and 680; the ETH costs 3,680. -/
theorem eth_reth_round_trip :
    let c1 : Change := ⟨0, 2, 1, 9 / 10, some 3000, some (9 / 10 * 3300), 0, 0, 0, 20250301, 2, 2, 3, 3⟩
    let c2 : Change := ⟨2, 0, 9 / 10, 115 / 100, some (9 / 10 * 4000), some (115 / 100 * 3200), 0, 0, 0, 20250601,
      4, 4, 5, 5⟩
    (run ethBook ([c1, c2].flatMap (toEvents 1))).2 = [(.sale, 2000), (.sale, 680)] ∧
      (run ethBook ([c1, c2].flatMap (toEvents 1))).1 0 = [⟨5, 0, 20250601, 115 / 100, 3680, (5, 0)⟩] ∧
      (run ethBook ([c1, c2].flatMap (toEvents 1))).1 2 = [] := by
  norm_num [ethBook, toEvents, run, apply, sale, held, sell, add, newLot, newCost, proceeds, offSale, worth_both, worth_from_only, (worth_none 1 0 (by norm_num)).1, max_def,
    Function.update]

/-- **PER-6** (es.test.ts:375-399) A price on one side only: 1 ETH worth 3,100 wrapped into WETH with no price is
sold for 3,100; on neither side, 1 ETH (cost 1,000) is sold for nothing, a loss of 1,000. -/
theorem one_side_priced :
    let c1 : Change := ⟨0, 1, 1, 1, some 3100, none, 0, 0, 0, 20250302, 2, 2, 3, 3⟩
    let c0 : Change := ⟨0, 1, 1, 5, none, none, 0, 0, 0, 20250301, 2, 2, 3, 3⟩
    (run ethBook (toEvents 1 c1)).2 = [(.sale, 2100)] ∧ (run ethBook (toEvents 1 c0)).2 = [(.sale, -1000)] := by
  norm_num [ethBook, toEvents, run, apply, sale, held, sell, add, newLot, newCost, proceeds, offSale, worth_both, worth_from_only, (worth_none 1 0 (by norm_num)).1, max_def,
    Function.update]

/-- **PER-6** (es.test.ts:414-425) The partial wrap: ETH lots of 1 coin from 2023-02-01 (cost 500) and 1 coin bought
again on 2024-07-01 (cost 2,000) after a loss of 1,000 on 2024-06-01 (all of it put off on that purchase). 1.5 ETH
wrapped at 2,100 each takes the 2023 coin (500) and half the coin bought again (1,000): the rows are the two lots'
coins, the loss counted is 500 and 500 still waits. -/
theorem partial_wrap :
    let B : Book := Function.update (fun _ => []) 0
      [⟨1, 0, 20230201, 1, 500, (2, 0)⟩, ⟨2, 0, 20240701, 1, 2000, (4, 0)⟩]
    let c : Change := ⟨0, 1, 3 / 2, 3 / 2, some (3 / 2 * 2100), some (3 / 2 * 2100), 0, 0, 0, 20250201, 6, 6, 7, 7⟩
    let picks := (sale (B c.src) c.qty c.saleId c.wallet c.date c.saleSeq).1
    let part : Part := ⟨9, 2024, 2, 1000, 1000, 1, 1⟩
    (run B (toEvents 1 c)).2 = [(.sale, 1650)] ∧
      (rowsOf c.date picks).map (fun s => (s.lot, s.qty)) = [(1, 1), (2, 1 / 2)] ∧
      evSum 9 (releaseAll (rowsOf c.date picks) [part]).2 = 500 ∧
      waiting 9 (releaseAll (rowsOf c.date picks) [part]).1 = 500 := by
  norm_num [toEvents, run, apply, sale, held, sell, add, newLot, newCost, proceeds, offSale, worth_both, worth_from_only, (worth_none 1 0 (by norm_num)).1, max_def,
    Function.update, rowsOf, releaseAll, release, evSum, waiting]

end Kanon.Spain.Permuta
