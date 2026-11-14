import Mathlib.Tactic

/-!
# France: crypto gains of a private person, art. 150 VH bis CGI (form 2086, 2042-C)

The app's engine `src/lib/engine/fr.ts` (`frRun`, `frYear`, `frYearTax`, `frDeadlines`), the classifier in
`src/lib/report/fr.ts` (`frBook`) and the next filing date in `src/lib/findings/upcoming.ts`. Sources: art. 150 VH bis
CGI; BOFiP BOI-RPPM-PVBMC-30-20-20190902 (base, worked examples §§ 110 and 120) and BOI-RPPM-PVBMC-30-30-20240423
(taxation, filing); the 2086 notice (revenus 2025, 16043*07, worked example under lines 221, 261 and 321); art. 200 C
CGI (12.8%); LFSS 2026 (loi n° 2025-1403 art. 12: CSG on capital income 10.6%, levies 18.6% from 2025's income);
art. 1657 CGI (whole euros); Service-public.fr A15597 (filing dates, revenus 2025).

`frRun` and `frYear` are modelled line for line, in exact fractions:

* a cession (l.213 price, l.214 fees, l.216 soulte, l.212 portfolio value) gives l.217 = l.213 + l.216 and
  l.218 = l.213 − l.214 + l.216; with l.223 = max(l.220 − l.221 − l.222, 0) the acquisition price left, the part of it
  used is `fraction` = l.223 × l.217 ÷ l.212 (0 when l.217 ≤ 0) and the gain l.224 = l.218 − fraction;
* the portfolio value is usable only when known, above 0 and not below l.217; from the first one that is not, every
  later line has no l.220-l.224 and the cost left is unknown;
* an exchange with a soulte (`cryptoIn`) then adds l.213 plus any soulte received to l.220, and that soulte to l.222;
* the year: l.51 = Σ l.218, l.52 = Σ l.224 (unknown if any is); when a sale's price couldn't be known (`unpriced`,
  estimated, or 0, in l.51) and l.51 ≤ 305, nothing is settled (not exempt, no l.52, no box, no tax); else exempt when
  l.51 ≤ 305; else the net gain in whole euros (half away from zero, Decimal's ROUND_HALF_UP) goes to 3AN, a net loss
  to 3BN, and the tax is 12.8% plus the year's social rate of the positive part, each rounded up to the cent.

`frBook` is modelled for swaps and fees only (its other happenings, the exchanges seen for 3916-bis and the price carried
in from 2018 are not), and the `frDeadlines` dates with the choice `upcoming.ts` makes among them. The 3916-bis note
(`frNotes` in `ReportPdf.tsx`) is not modelled: it is text, checked against art. 1736 X CGI by review, not a theorem.

Out of scope (the app's and its tests'): how `frReport` turns `frBook`'s drafts and acquisitions into `frRun`'s
operations, the time order of operations (the model takes them in the engine's order), building the portfolio value
from prices (`frHeld`, `frPortfolio`), coins held on 1 January 2019, the Paris day of a sale, the conversion to euros,
and decimal.js itself: the app computes with decimal.js at 40 significant digits (`Decimal.set({ precision: 40 })` in
`money.ts`), so a division such as l.223 × l.217 ÷ l.212 is rounded there, while the model uses exact fractions. Dates
are modelled as the number yyyymmdd, which orders like the app's ISO strings.
-/

namespace Kanon.France

/-! ## One cession's 2086 lines -/

/-- A taxable cession: l.213 `price`, l.216 `soulte` (+ received, − paid), l.214 `fees`, l.212 `portfolio`
(none: not known). `cryptoIn`: an exchange for other crypto with a soulte. -/
structure Cession where
  price : ℚ
  soulte : ℚ := 0
  fees : ℚ := 0
  portfolio : Option ℚ
  cryptoIn : Bool := false

inductive Op
  | acquire (paid : ℚ)
  | cession (c : Cession)

/-- l.217: the price with the soulte. -/
def l217 (c : Cession) : ℚ := c.price + c.soulte

/-- l.218: the price less fees, with the soulte. -/
def l218 (c : Cession) : ℚ := c.price - c.fees + c.soulte

/-- l.212 as the engine uses it: known, above 0 and not below the sale itself; else unknown. -/
def usable (c : Cession) : Option ℚ :=
  match c.portfolio with
  | some p => if p ≤ 0 ∨ p < l217 c then none else some p
  | none => none

/-- The acquisition price a sale uses up: l.223 × l.217 ÷ l.212 (0 when l.217 is not above 0). -/
def fraction (cost : ℚ) (c : Cession) (p : ℚ) : ℚ := if 0 < l217 c then cost * l217 c / p else 0

/-- l.224: l.218 less the acquisition price used up. -/
def gain (cost : ℚ) (c : Cession) (p : ℚ) : ℚ := l218 c - fraction cost c p

/-- The running totals: l.220 `pta`, l.221 `fractions`, l.222 `soultes`, and whether every value so far was usable. -/
structure State where
  pta : ℚ
  fractions : ℚ
  soultes : ℚ
  known : Bool

/-- l.223: the total acquisition price left, l.220 − l.221 − l.222, never below 0. -/
def net (s : State) : ℚ := max (s.pta - s.fractions - s.soultes) 0

/-- One cession's line: l.218, and l.223, l.224 and the fraction used (none when unknown). -/
structure Line where
  l218 : ℚ
  l223 : Option ℚ
  l224 : Option ℚ
  fraction : Option ℚ

/-- After an exchange with a soulte, what came in is acquired: l.220 takes l.213 and any soulte received, l.222 that soulte. -/
def exchangeIn (c : Cession) (s : State) : State :=
  if c.cryptoIn then { s with pta := s.pta + c.price + max c.soulte 0, soultes := s.soultes + max c.soulte 0 } else s

/-- One operation of `frRun`. -/
def step (s : State) : Op → State × Option Line
  | .acquire paid => ({ s with pta := s.pta + paid }, none)
  | .cession c =>
    match (if s.known then usable c else none) with
    | some p =>
      (exchangeIn c { s with fractions := s.fractions + fraction (net s) c p },
       some ⟨l218 c, some (net s), some (gain (net s) c p), some (fraction (net s) c p)⟩)
    | none => (exchangeIn c { s with known := false }, some ⟨l218 c, none, none, none⟩)

/-- `frRun`: the cessions' lines and the state after the last operation. -/
def run : State → List Op → List Line × State
  | s, [] => ([], s)
  | s, op :: ops => ((step s op).2.toList ++ (run (step s op).1 ops).1, (run (step s op).1 ops).2)

/-- The start: the acquisition price carried in, nothing used yet. -/
def start (carried : ℚ) : State := ⟨carried, 0, 0, true⟩

/-- `left`: the acquisition price left after the last operation, none once a value was unknown. -/
def left (s : State) : Option ℚ := if s.known then some (net s) else none

/-! ### Rule 1: the whole-portfolio gain (art. 150 VH bis III; BOFiP 30-20 §§ 100-110) -/

/-- **FR-1** With every portfolio value so far usable, a cession's line is l.218, l.223 = the acquisition price
left, l.224 = l.218 − fraction and the fraction used. -/
theorem cession_line (s : State) (c : Cession) (p : ℚ) (hk : s.known = true) (hp : usable c = some p) :
    (step s (.cession c)).2 =
      some ⟨l218 c, some (net s), some (l218 c - fraction (net s) c p), some (fraction (net s) c p)⟩ := by
  simp [step, hk, hp, gain]

/-- **FR-1** The formula: l.224 = (price − fees + soulte) − cost × (price + soulte) ÷ portfolio value, whenever
l.217 is not below 0. -/
theorem gain_formula (cost p : ℚ) (c : Cession) (h : 0 ≤ l217 c) :
    gain cost c p = (c.price - c.fees + c.soulte) - cost * (c.price + c.soulte) / p := by
  unfold gain fraction l218
  split_ifs with h0
  · rfl
  · have : l217 c = 0 := le_antisymm (not_lt.mp h0) h
    simp only [l217] at this; rw [this]; simp

/-- **FR-1** A plain sale (no fees, no soulte) for `x`: gain = x − cost × x ÷ portfolio value. -/
theorem gain_plain (cost x p : ℚ) (hx : 0 ≤ x) :
    gain cost { price := x, portfolio := some p } p = x - cost * x / p := by
  rw [gain_formula _ _ _ (by simpa [l217] using hx)]; simp

/-- **FR-1** The gain never exceeds the net price l.218 (for a cost not below 0 and a portfolio value above 0). -/
theorem gain_le_price (cost p : ℚ) (c : Cession) (hc : 0 ≤ cost) (hp : 0 < p) : gain cost c p ≤ l218 c := by
  unfold gain fraction
  split_ifs with h
  · have : 0 ≤ cost * l217 c / p := div_nonneg (mul_nonneg hc h.le) hp.le
    linarith
  · simp

/-- **FR-1** The gain is 0 exactly when the net price equals the share of the cost the sale uses. -/
theorem gain_zero_iff (cost p : ℚ) (c : Cession) : gain cost c p = 0 ↔ l218 c = fraction cost c p := by
  unfold gain; exact sub_eq_zero

/-- **FR-1** A plain sale for `x > 0` from a portfolio worth `p > 0`: no gain exactly when the acquisition price
left equals the portfolio's value. -/
theorem gain_plain_zero_iff (cost x p : ℚ) (hx : 0 < x) (hp : 0 < p) :
    gain cost { price := x, portfolio := some p } p = 0 ↔ cost = p := by
  rw [gain_plain _ _ _ hx.le]
  constructor
  · intro h
    have : x * (p - cost) = 0 := by field_simp at h; linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · linarith
  · intro h; subst h; field_simp; ring

/-- **FR-1** With a usable value and a cost not below 0, the fraction used is between 0 and the cost left. -/
theorem fraction_bounds (cost p : ℚ) (c : Cession) (hc : 0 ≤ cost) (hp : usable c = some p) :
    0 ≤ fraction cost c p ∧ fraction cost c p ≤ cost := by
  unfold usable at hp
  cases hpo : c.portfolio with
  | none => simp [hpo] at hp
  | some q =>
    simp only [hpo] at hp
    split_ifs at hp with hq
    cases hp
    push_neg at hq
    unfold fraction
    split_ifs with h
    · refine ⟨div_nonneg (mul_nonneg hc h.le) (by linarith), ?_⟩
      rw [div_le_iff₀ (by linarith)]
      exact mul_le_mul_of_nonneg_left hq.2 hc
    · exact ⟨le_refl _, hc⟩

/-! ### Rule 2: the acquisition price left after a sale (BOFiP 30-20 §§ 90-120) -/

/-- l.220 − l.221 − l.222 is not below 0 (then `net` never clips it). -/
def Inv (s : State) : Prop := 0 ≤ s.pta - s.fractions - s.soultes

/-- **FR-2** l.223 is never below 0. -/
theorem net_nonneg (s : State) : 0 ≤ net s := le_max_right _ _

/-- **FR-2** A sale for money (not an exchange) with a usable value: the acquisition price left falls by exactly
the fraction used, cost × l.217 ÷ portfolio value, and the value stays known. -/
theorem cost_falls (s : State) (c : Cession) (p : ℚ) (hk : s.known = true) (hp : usable c = some p)
    (hx : c.cryptoIn = false) (hi : Inv s) :
    net (step s (.cession c)).1 = net s - fraction (net s) c p ∧ (step s (.cession c)).1.known = true := by
  have hb := fraction_bounds (net s) p c (net_nonneg s) hp
  have hn : net s = s.pta - s.fractions - s.soultes := max_eq_left hi
  have hs : (step s (.cession c)).1 = { s with fractions := s.fractions + fraction (net s) c p } := by
    simp [step, hk, hp, exchangeIn, hx]
  rw [hs]
  refine ⟨?_, hk⟩
  generalize fraction (net s) c p = f at hb ⊢
  show max (s.pta - (s.fractions + f) - s.soultes) 0 = net s - f
  rw [max_eq_left (by linarith)]; linarith

/-- **FR-2** An exchange with a soulte, usable value: the acquisition price left falls by the fraction used and
rises by l.213, the value of what came in (BOFiP § 120). -/
theorem exchange_cost (s : State) (c : Cession) (p : ℚ) (hk : s.known = true) (hp : usable c = some p)
    (hx : c.cryptoIn = true) (hi : Inv s) (hpr : 0 ≤ c.price) :
    net (step s (.cession c)).1 = net s - fraction (net s) c p + c.price := by
  have hb := fraction_bounds (net s) p c (net_nonneg s) hp
  have hn : net s = s.pta - s.fractions - s.soultes := max_eq_left hi
  have hs : (step s (.cession c)).1 = ⟨s.pta + c.price + max c.soulte 0, s.fractions + fraction (net s) c p,
      s.soultes + max c.soulte 0, s.known⟩ := by
    simp [step, hk, hp, exchangeIn, hx]
  rw [hs]
  generalize fraction (net s) c p = f at hb ⊢
  show max (s.pta + c.price + max c.soulte 0 - (s.fractions + f) - (s.soultes + max c.soulte 0)) 0 = net s - f + c.price
  rw [max_eq_left (by linarith)]; linarith

/-- Amounts not below 0: a price paid, or a cession's price. -/
def Op.Ok : Op → Prop
  | .acquire paid => 0 ≤ paid
  | .cession c => 0 ≤ c.price

/-- **FR-2** With amounts not below 0, every step keeps l.220 − l.221 − l.222 from going below 0. -/
theorem inv_step (s : State) (op : Op) (hi : Inv s) (ho : op.Ok) : Inv (step s op).1 := by
  cases op with
  | acquire paid => simp only [Op.Ok] at ho; simp only [step, Inv] at hi ⊢; linarith
  | cession c =>
    simp only [Op.Ok] at ho
    have hx : ∀ t : State, Inv t → Inv (exchangeIn c t) := by
      intro t ht; unfold exchangeIn; split_ifs
      · simp only [Inv] at ht ⊢; linarith
      · exact ht
    simp only [step]
    split
    · next p hp =>
      apply hx
      have hu : usable c = some p := by split_ifs at hp; exact hp
      have hb := fraction_bounds (net s) p c (net_nonneg s) hu
      have hn : net s = s.pta - s.fractions - s.soultes := max_eq_left hi
      show 0 ≤ s.pta - (s.fractions + fraction (net s) c p) - s.soultes
      linarith [hb.2]
    · exact hx _ hi

/-- **FR-2** From a carried-in price not below 0, with amounts not below 0, l.220 − l.221 − l.222 never goes below 0
over a whole run, so the `max … 0` in l.223 never changes it. -/
theorem never_clipped (carried : ℚ) (hc : 0 ≤ carried) (ops : List Op) (ho : ∀ op ∈ ops, op.Ok) :
    Inv (run (start carried) ops).2 := by
  suffices ∀ s ops, Inv s → (∀ op ∈ ops, Op.Ok op) → Inv (run s ops).2 from
    this _ ops (by simp [Inv, start, hc]) ho
  intro s ops
  induction ops generalizing s with
  | nil => intro h _; exact h
  | cons op ops ih =>
    intro h ho
    exact ih _ (inv_step s op h (ho op (by simp))) (fun o ho' => ho o (by simp [ho']))

/-! ### The official worked examples -/

/-- **FR-2** BOFiP BOI-RPPM-PVBMC-30-20-20190902 § 110, and the same example in the 2086 notice (revenus 2025, under
lines 221, 261 and 321): nothing held, 1,000 € of crypto bought; in March, portfolio 1,200 €, a cession for 450 €:
450 − (1000 × 450 / 1200) = 75 €; in August, portfolio 1,300 €, everything sold for 1,300 €:
1300 − [(1000 − 375) × 1300 / 1300] = 675 €. The model's l.224 are 75 and 675, its l.223 1,000 then 625, and its
fractions 375 then 625. -/
theorem bofip_110 :
    (run (start 0) [.acquire 1000, .cession { price := 450, portfolio := some 1200 },
        .cession { price := 1300, portfolio := some 1300 }]).1 =
      [⟨450, some 1000, some 75, some 375⟩, ⟨1300, some 625, some 675, some 625⟩] := by
  simp [run, step, start, usable, l217, l218, fraction, gain, net, exchangeIn]; norm_num

/-- **FR-2** BOFiP BOI-RPPM-PVBMC-30-20-20190902 § 120: nothing held, 500 € of crypto bought; in March, portfolio
750 €, the crypto exchanged for other crypto worth 600 € plus a soulte of 150 € received in money:
(600 + 150) − [500 × (600 + 150) / 750] = 250 €; in October, portfolio 800 € (the crypto received), everything sold for
800 €: 800 − [((500 + 750) − 500 − 150) × 800 / 800] = 200 €. The model's l.224 are 250 and 200, and after the
exchange its l.220 is 500 + 750, l.221 500 and l.222 150, as in the source. -/
theorem bofip_120 :
    (run (start 0) [.acquire 500,
        .cession { price := 600, soulte := 150, portfolio := some 750, cryptoIn := true },
        .cession { price := 800, portfolio := some 800 }]).1 =
      [⟨750, some 500, some 250, some 500⟩, ⟨800, some 600, some 200, some 600⟩] ∧
    (run (start 0) [.acquire 500,
        .cession { price := 600, soulte := 150, portfolio := some 750, cryptoIn := true }]).2 =
      ⟨500 + 750, 500, 150, true⟩ := by
  constructor <;> simp [run, step, start, usable, l217, l218, fraction, gain, net, exchangeIn] <;> norm_num

/-! ### The classifier `frBook`, for swaps and fees (art. 150 VH bis II-A; 2086 notice, lines 213-218) -/

/-- A movement as `frBook` sees it: money (`fiat`) or crypto, and its value in euros (none: no price). -/
structure Move where
  fiat : Bool
  value : Option ℚ

/-- `sum`: the movements' total value, none when any has no price. -/
def total : List Move → Option ℚ
  | [] => some 0
  | m :: ms =>
    match m.value, total ms with
    | some v, some t => some (v + t)
    | _, _ => none

inductive How
  | sale
  | exchange
  | fees
  deriving DecidableEq

/-- `FrDraft`: a cession before its portfolio value is known (the day is the Paris day, yyyymmdd). -/
structure Draft where
  how : How
  day : ℕ
  price : ℚ
  fees : ℚ := 0
  soulte : ℚ := 0
  cryptoIn : Bool := false
  unpriced : Bool := false

/-- A swap happening: its transaction, day, what went out and what came in. -/
structure Swap where
  tx : ℕ
  day : ℕ
  out : List Move
  inn : List Move
  keepsCost : Bool := false

/-- A fee happening: its transaction, day and the movement paid (`rebate`: an amount not below 0, received). -/
structure Fee where
  tx : ℕ
  day : ℕ
  fee : Move
  rebate : Bool := false

inductive Event
  | swap (h : Swap)
  | fee (h : Fee)

/-- `frBook`'s state: the drafts, the acquisitions' prices paid, and its maps `byTx` (a transaction's cession),
`buyTx` (a transaction's purchase) and `feeDay` (a day's fees cession), each to an index. -/
structure Book where
  drafts : List Draft
  acquisitions : List ℚ
  byTx : ℕ → Option ℕ
  buyTx : ℕ → Option ℕ
  feeDay : ℕ → Option ℕ

/-- Changing the `i`-th element in place (the app mutates the draft object it holds). -/
def modifyAt {α : Type} (f : α → α) : ℕ → List α → List α
  | _, [] => []
  | 0, x :: xs => f x :: xs
  | n + 1, x :: xs => x :: modifyAt f n xs

/-- The regime's start: 1 January 2019. -/
def startDay : ℕ := 20190101

/-- `addFee`: coins paid as a fee are a cession for a service, one line per day: added to that day's fees line, or
a new one. -/
def addFee (b : Book) (day : ℕ) (v : ℚ) : Book :=
  match b.feeDay day with
  | some i => { b with drafts := modifyAt (fun d => { d with price := d.price + v }) i b.drafts }
  | none =>
    { b with drafts := b.drafts ++ [{ how := .fees, day := day, price := v }],
             feeDay := fun d => if d = day then some b.drafts.length else b.feeDay d }

/-- `frBook` on a swap: before 2019 or `keepsCost`, nothing; no crypto out: a purchase when crypto came in for money;
no money either side: nothing (sursis); crypto for money: a sale (money paid out is its fee); crypto for crypto with
money: an exchange, the money its soulte. -/
def bookSwap (b : Book) (h : Swap) : Book :=
  if h.day < startDay ∨ h.keepsCost = true then b else
  let fiatOut := h.out.filter (·.fiat)
  let fiatIn := h.inn.filter (·.fiat)
  let cryptoOut := h.out.filter (fun m => !m.fiat)
  let cryptoIn := h.inn.filter (fun m => !m.fiat)
  if cryptoOut = [] then
    if cryptoIn ≠ [] ∧ fiatOut ≠ [] then
      { b with acquisitions := b.acquisitions ++ [((total fiatOut).orElse (fun _ => total cryptoIn)).getD 0],
               buyTx := fun t => if t = h.tx then some b.acquisitions.length else b.buyTx t }
    else b
  else if fiatOut = [] ∧ fiatIn = [] then b
  else
    let d : Draft :=
      if cryptoIn = [] then
        let got := total fiatIn
        let paid := if fiatOut = [] then some 0 else total fiatOut
        { how := .sale, day := h.day, price := (got.orElse (fun _ => total cryptoOut)).getD 0, fees := paid.getD 0,
          unpriced := got.isNone || paid.isNone }
      else
        let value := total cryptoIn
        let soulte := if fiatIn = [] then (total fiatOut).map Neg.neg else total fiatIn
        { how := .exchange, day := h.day, price := value.getD 0, soulte := soulte.getD 0, cryptoIn := true,
          unpriced := value.isNone || soulte.isNone }
    { b with drafts := b.drafts ++ [d], byTx := fun t => if t = h.tx then some b.drafts.length else b.byTx t }

/-- `frBook` on a fee: a rebate or before 2019, nothing; on a cession's transaction, off its price (l.214); on a
purchase's, money adds to what was paid; money elsewhere, nothing; coins worth above 0 elsewhere, `addFee`. -/
def bookFee (b : Book) (h : Fee) : Book :=
  if h.day < startDay ∨ h.rebate = true then b else
  match b.byTx h.tx with
  | some i =>
    { b with drafts := modifyAt (fun d => { d with fees := d.fees + h.fee.value.getD 0,
                                                    unpriced := d.unpriced || h.fee.value.isNone }) i b.drafts }
  | none =>
    match b.buyTx h.tx with
    | some j =>
      match h.fee.fiat, h.fee.value with
      | true, some v => { b with acquisitions := modifyAt (· + v) j b.acquisitions }
      | _, _ => b
    | none =>
      match h.fee.fiat, h.fee.value with
      | false, some v => if 0 < v then addFee b h.day v else b
      | _, _ => b

def bookStep (b : Book) : Event → Book
  | .swap h => bookSwap b h
  | .fee h => bookFee b h

/-- The empty book. -/
def Book.empty : Book := ⟨[], [], fun _ => none, fun _ => none, fun _ => none⟩

/-- `frBook` over the happenings, in order. -/
def book (hs : List Event) : Book := hs.foldl bookStep Book.empty

/-- A crypto-for-crypto swap: no money on either side. -/
def Swap.noMoney (h : Swap) : Prop := ∀ m ∈ h.out ++ h.inn, m.fiat = false

/-- **FR-2** The swap itself, crypto for crypto with no money either side, gives no cession and no acquisition:
`frBook` leaves its book exactly as it was (sursis, art. 150 VH bis II-A). -/
theorem swap_no_line (b : Book) (h : Swap) (hn : h.noMoney) : bookStep b (.swap h) = b := by
  have hfo : h.out.filter (·.fiat) = [] :=
    List.filter_eq_nil_iff.mpr (fun m hm => by simp [hn m (List.mem_append_left _ hm)])
  have hfi : h.inn.filter (·.fiat) = [] :=
    List.filter_eq_nil_iff.mpr (fun m hm => by simp [hn m (List.mem_append_right _ hm)])
  simp only [bookStep, bookSwap, hfo, hfi]
  split_ifs <;> simp_all

/-- **FR-2** So removing such a swap from anywhere in the history gives the same book: no line, no acquisition, and
every later happening (a fee on it among them) classified exactly as without it. -/
theorem swap_changes_nothing (a rest : List Event) (h : Swap) (hn : h.noMoney) :
    book (a ++ .swap h :: rest) = book (a ++ rest) := by
  simp [book, List.foldl_append, List.foldl_cons, swap_no_line _ h hn]

/-- **FR-2** A fee paid in crypto on that swap is a separate cession: with no cession or purchase recorded for its
transaction, a fee in coins worth `v > 0` (from 2019) goes to `addFee`, a cession of those coins for a service. -/
theorem swap_fee_is_cession (b : Book) (h : Swap) (f : Fee) (v : ℚ) (hn : h.noMoney) (htx : f.tx = h.tx)
    (hb : b.byTx h.tx = none) (hu : b.buyTx h.tx = none) (hd : ¬ f.day < startDay) (hr : f.rebate = false)
    (hc : f.fee.fiat = false) (hv : f.fee.value = some v) (hp : 0 < v) :
    bookStep (bookStep b (.swap h)) (.fee f) = addFee b f.day v := by
  rw [swap_no_line b h hn]
  simp [bookStep, bookFee, hd, hr, htx, hb, hu, hc, hv, hp]

/-! #### `addFee` puts a coin fee on that day's fees line -/

theorem modifyAt_length {α : Type} (f : α → α) (i : ℕ) (l : List α) : (modifyAt f i l).length = l.length := by
  induction l generalizing i with
  | nil => simp [modifyAt]
  | cons x xs ih => cases i <;> simp [modifyAt, ih]

theorem modifyAt_get {α : Type} (f : α → α) (i j : ℕ) (l : List α) :
    (modifyAt f i l)[j]? = if j = i then (l[j]?).map f else l[j]? := by
  induction l generalizing i j with
  | nil => simp [modifyAt]
  | cons x xs ih =>
    cases i <;> cases j <;> simp [modifyAt, ih]

theorem modifyAt_sum (g : Draft → ℚ) (f : Draft → Draft) (c : ℚ) (hf : ∀ d, g (f d) = g d + c) (i : ℕ)
    (l : List Draft) (hi : i < l.length) : ((modifyAt f i l).map g).sum = (l.map g).sum + c := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [modifyAt, hf]; ring
    | succ n => simp [modifyAt, ih n (by simpa using hi)]; ring

/-- What `frBook` keeps true: each day's fees line is a fees draft of that day, and each recorded index is a draft or
an acquisition. -/
def Book.Ok (b : Book) : Prop :=
  (∀ d i, b.feeDay d = some i → ∃ x, b.drafts[i]? = some x ∧ x.how = .fees ∧ x.day = d) ∧
    (∀ t i, b.byTx t = some i → i < b.drafts.length) ∧ (∀ t j, b.buyTx t = some j → j < b.acquisitions.length)

theorem ok_modify (b : Book) (f : Draft → Draft) (i : ℕ) (hf : ∀ d, (f d).how = d.how ∧ (f d).day = d.day)
    (ho : b.Ok) : { b with drafts := modifyAt f i b.drafts }.Ok := by
  obtain ⟨h1, h2, h3⟩ := ho
  refine ⟨fun d k hk => ?_, fun t k hk => ?_, h3⟩
  · obtain ⟨x, hx, hh, hdd⟩ := h1 d k hk
    simp only [modifyAt_get, hx]
    split_ifs
    · exact ⟨f x, rfl, (hf x).1.trans hh, (hf x).2.trans hdd⟩
    · exact ⟨x, rfl, hh, hdd⟩
  · simp only [modifyAt_length]; exact h2 t k hk

theorem ok_push (b : Book) (x : Draft) (ho : b.Ok) : (∀ d i, b.feeDay d = some i → ∃ y,
    (b.drafts ++ [x])[i]? = some y ∧ y.how = .fees ∧ y.day = d) ∧
    (∀ t i, b.byTx t = some i → i < (b.drafts ++ [x]).length) := by
  obtain ⟨h1, h2, _⟩ := ho
  refine ⟨fun d i hi => ?_, fun t i hi => by simp; have := h2 t i hi; omega⟩
  obtain ⟨y, hy, hh, hd⟩ := h1 d i hi
  have hl : i < b.drafts.length := by
    rcases Nat.lt_or_ge i b.drafts.length with h | h
    · exact h
    · simp [List.getElem?_eq_none h] at hy
  exact ⟨y, by rw [List.getElem?_append_left hl]; exact hy, hh, hd⟩

theorem ok_addFee (b : Book) (day : ℕ) (v : ℚ) (ho : b.Ok) : (addFee b day v).Ok := by
  unfold addFee
  split
  · exact ok_modify b _ _ (fun _ => ⟨rfl, rfl⟩) ho
  · obtain ⟨p1, p2⟩ := ok_push b { how := .fees, day := day, price := v } ho
    refine ⟨fun d i hi => ?_, p2, ho.2.2⟩
    simp only at hi
    split_ifs at hi with hd
    · cases hi; exact ⟨_, List.getElem?_concat_length .., rfl, hd.symm⟩
    · exact p1 d i hi

theorem ok_pushTx (b : Book) (x : Draft) (tx : ℕ) (ho : b.Ok) :
    { b with drafts := b.drafts ++ [x], byTx := fun t => if t = tx then some b.drafts.length else b.byTx t }.Ok := by
  obtain ⟨p1, p2⟩ := ok_push b x ho
  refine ⟨p1, fun t i hi => ?_, ho.2.2⟩
  simp only at hi
  split_ifs at hi
  · cases hi; simp
  · exact p2 t i hi

theorem ok_buy (b : Book) (x : ℚ) (tx : ℕ) (ho : b.Ok) :
    { b with acquisitions := b.acquisitions ++ [x],
             buyTx := fun t => if t = tx then some b.acquisitions.length else b.buyTx t }.Ok := by
  refine ⟨ho.1, ho.2.1, fun t j hj => ?_⟩
  simp only at hj
  split_ifs at hj
  · cases hj; simp
  · have := ho.2.2 t j hj; simp; omega

theorem ok_step (b : Book) (e : Event) (ho : b.Ok) : (bookStep b e).Ok := by
  cases e with
  | swap h =>
    simp only [bookStep, bookSwap]
    split_ifs <;> first | exact ho | exact ok_buy b _ _ ho | exact ok_pushTx b _ _ ho
  | fee h =>
    simp only [bookStep, bookFee]
    split_ifs
    · exact ho
    · split
      · exact ok_modify b _ _ (fun _ => ⟨rfl, rfl⟩) ho
      · split
        · split
          · refine ⟨ho.1, ho.2.1, fun t j hj => ?_⟩
            simp only [modifyAt_length]; exact ho.2.2 t j hj
          · exact ho
        · split
          · split_ifs
            · exact ok_addFee b _ _ ho
            · exact ho
          · exact ho

theorem ok_book (hs : List Event) : (book hs).Ok := by
  suffices ∀ b, b.Ok → (hs.foldl bookStep b).Ok from this _ ⟨by simp [Book.empty], by simp [Book.empty],
    by simp [Book.empty]⟩
  induction hs with
  | nil => intro b hb; exact hb
  | cons e es ih => intro b hb; exact ih _ (ok_step b e hb)

/-- **FR-2** `addFee` on a book `frBook` built: the drafts' prices rise by exactly the fee's value `v`, the
acquisitions don't change, and that day's fees line is a fees draft of that day. -/
theorem addFee_spec (hs : List Event) (day : ℕ) (v : ℚ) :
    (((addFee (book hs) day v).drafts.map Draft.price).sum = ((book hs).drafts.map Draft.price).sum + v) ∧
      (addFee (book hs) day v).acquisitions = (book hs).acquisitions ∧
      ∃ i x, (addFee (book hs) day v).feeDay day = some i ∧ (addFee (book hs) day v).drafts[i]? = some x ∧
        x.how = .fees ∧ x.day = day := by
  have ho := ok_book hs
  have hok := (ok_addFee _ day v ho).1
  refine ⟨?_, by unfold addFee; split <;> rfl, ?_⟩
  · unfold addFee
    split
    · next i hi =>
      obtain ⟨x, hx, _⟩ := ho.1 day i hi
      have hl : i < (book hs).drafts.length := by
        rcases Nat.lt_or_ge i (book hs).drafts.length with h | h
        · exact h
        · simp [List.getElem?_eq_none h] at hx
      exact modifyAt_sum Draft.price _ v (fun _ => rfl) i _ hl
    · simp
  · have : ∃ i, (addFee (book hs) day v).feeDay day = some i := by
      unfold addFee; split
      · next i hi => exact ⟨i, hi⟩
      · exact ⟨(book hs).drafts.length, by simp⟩
    obtain ⟨i, hi⟩ := this
    obtain ⟨x, hx, hh, hd⟩ := hok day i hi
    exact ⟨i, x, hi, hx, hh, hd⟩

/-! ### Rule 3: an unknown portfolio value is never counted as 0 -/

/-- **FR-3** A portfolio value is unusable exactly when it is unknown, not above 0, or below the sale (l.217). -/
theorem unusable_iff (c : Cession) :
    usable c = none ↔ c.portfolio = none ∨ ∃ p, c.portfolio = some p ∧ (p ≤ 0 ∨ p < l217 c) := by
  unfold usable
  cases c.portfolio with
  | none => simp
  | some p => by_cases h : p ≤ 0 ∨ p < l217 c <;> simp [h]

/-- **FR-3** A cession after an unknown value, or with an unusable one, has no l.223 or l.224 (not 0), and every
later one stays unknown. -/
theorem unknown_line (s : State) (c : Cession) (h : s.known = false ∨ usable c = none) :
    (step s (.cession c)).2 = some ⟨l218 c, none, none, none⟩ ∧ (step s (.cession c)).1.known = false := by
  have : (if s.known then usable c else none) = none := by rcases h with h | h <;> simp [h]
  simp only [step, this, exchangeIn]
  split_ifs <;> simp

/-- **FR-3** Once a value is unknown, every later line has no l.223 or l.224 and the price left is unknown. -/
theorem unknown_sticks (s : State) (ops : List Op) (h : s.known = false) :
    (∀ L ∈ (run s ops).1, L.l223 = none ∧ L.l224 = none) ∧ left (run s ops).2 = none := by
  induction ops generalizing s with
  | nil => simp [run, left, h]
  | cons op ops ih =>
    have hk : (step s op).1.known = false ∧ ∀ L ∈ (step s op).2.toList, L.l223 = none ∧ L.l224 = none := by
      cases op with
      | acquire paid => simp [step, h]
      | cession c =>
        obtain ⟨h1, h2⟩ := unknown_line s c (Or.inl h)
        exact ⟨h2, by simp [h1]⟩
    obtain ⟨ih1, ih2⟩ := ih _ hk.1
    refine ⟨?_, ih2⟩
    intro L hL
    simp only [run, List.mem_append] at hL
    rcases hL with hL | hL
    · exact hk.2 L hL
    · exact ih1 L hL

/-! ### Rules 4-8: the year, the €305 limit, netting, the flat tax and boxes 3AN / 3BN -/

/-- Art. 150 VH bis II-B: exempt when the year's l.51 is not over €305. -/
def threshold : ℚ := 305

/-- Line 51: the year's l.218 added up. -/
def l51 (ls : List Line) : ℚ := (ls.map Line.l218).sum

/-- Line 52: the year's l.224 added up, gains and losses together; unknown if any line's is. -/
def l52 : List Line → Option ℚ
  | [] => some 0
  | L :: ls =>
    match L.l224, l52 ls with
    | some g, some n => some (g + n)
    | _, _ => none

/-- Whole euros, nearest, half away from zero (Decimal's ROUND_HALF_UP; art. 1657 CGI). -/
def euros (x : ℚ) : ℤ := if 0 ≤ x then ⌊x + 1 / 2⌋ else -⌊-x + 1 / 2⌋

/-- `centsUp`: up to the cent (Decimal's ROUND_CEIL). -/
def centsUp (x : ℚ) : ℚ := (⌈x * 100⌉ : ℚ) / 100

/-- Art. 200 C CGI: 12.8%. -/
def incomeRate : ℚ := 128 / 1000

/-- Social levies: 18.6% from 2025's gains (LFSS 2026), 17.2% before. -/
def socialRate (year : ℕ) : ℚ := if 2025 ≤ year then 186 / 1000 else 172 / 1000

inductive Box
  | AN
  | BN
  deriving DecidableEq

/-- `frYear`'s figures. -/
structure Year where
  l51 : ℚ
  exempt : Bool
  l52 : Option ℚ
  box : Option (Box × ℤ)
  incomeTax : Option ℚ
  social : Option ℚ
  tax : Option ℚ

/-- `frYear`: with a sale whose price couldn't be known (`unpriced`, estimated, or 0, in l.51) and l.51 at €305 or less,
nothing is settled: not exempt, no l.52, box or tax; else exempt at €305 or less; else unknown if l.52 is; else the
net result in whole euros to 3AN or 3BN and 12.8% plus the year's levies on its positive part, each rounded up to the
cent. -/
def yearOf (year : ℕ) (ls : List Line) (unpriced : Bool) : Year :=
  if unpriced = true ∧ l51 ls ≤ threshold then ⟨l51 ls, false, none, none, none, none, none⟩
  else if l51 ls ≤ threshold then ⟨l51 ls, true, l52 ls, none, some 0, some 0, some 0⟩
  else
    match l52 ls with
    | none => ⟨l51 ls, false, none, none, none, none, none⟩
    | some n =>
      ⟨l51 ls, false, some n,
        (if 0 < euros n then some (.AN, euros n) else if euros n < 0 then some (.BN, -euros n) else none),
        some (centsUp (max (euros n : ℚ) 0 * incomeRate)),
        some (centsUp (max (euros n : ℚ) 0 * socialRate year)),
        some (centsUp (max (euros n : ℚ) 0 * incomeRate) + centsUp (max (euros n : ℚ) 0 * socialRate year))⟩

/-- Box 3AN's amount (0 when empty). -/
def an (Y : Year) : ℤ := match Y.box with | some (.AN, a) => a | _ => 0

/-- Box 3BN's amount (0 when empty). -/
def bn (Y : Year) : ℤ := match Y.box with | some (.BN, a) => a | _ => 0

/-! #### Rule 3 for the year -/

/-- **FR-3** l.52 is unknown exactly when some line's l.224 is. -/
theorem l52_none_iff (ls : List Line) : l52 ls = none ↔ ∃ L ∈ ls, L.l224 = none := by
  induction ls with
  | nil => simp [l52]
  | cons L ls ih =>
    simp only [l52, List.mem_cons, exists_eq_or_imp]
    cases h1 : L.l224 <;> cases h2 : l52 ls <;> simp_all

/-- **FR-3** Over the limit with an unknown l.52: the tax, the parts and the box are unknown, never 0. -/
theorem year_unknown (year : ℕ) (ls : List Line) (u : Bool) (hs : threshold < l51 ls) (h : l52 ls = none) :
    (yearOf year ls u).tax = none ∧ (yearOf year ls u).incomeTax = none ∧ (yearOf year ls u).social = none ∧
      (yearOf year ls u).box = none := by
  simp [yearOf, not_le.mpr hs, h]

/-! #### Rule 4: the €305 limit (art. 150 VH bis II-B) -/

/-- **FR-4** At or under €305 of sale prices (l.51), every sale's price known: exempt, nothing is taxed and no box is
filled. -/
theorem exempt_untaxed (year : ℕ) (ls : List Line) (u : Bool) (hu : u = false) (h : l51 ls ≤ threshold) :
    (yearOf year ls u).exempt = true ∧ (yearOf year ls u).tax = some 0 ∧ (yearOf year ls u).box = none := by
  simp [yearOf, h, hu]

/-- **FR-4** A sale whose price couldn't be known (estimated, or 0, in l.51) with l.51 at or under €305: the year is not
shown exempt, and no l.52, tax, box, income tax or levies is given (neither exemption nor a tax is claimed). -/
theorem unpriced_unsettled (year : ℕ) (ls : List Line) (u : Bool) (hu : u = true) (h : l51 ls ≤ threshold) :
    (yearOf year ls u).exempt = false ∧ (yearOf year ls u).l52 = none ∧ (yearOf year ls u).tax = none ∧
      (yearOf year ls u).box = none ∧ (yearOf year ls u).incomeTax = none ∧ (yearOf year ls u).social = none := by
  simp [yearOf, h, hu]

/-- **FR-4** Over €305 the unpriced flag changes nothing: the year is the same with it or without it. -/
theorem unpriced_over_limit (year : ℕ) (ls : List Line) (hs : threshold < l51 ls) :
    yearOf year ls true = yearOf year ls false := by
  simp [yearOf, not_le.mpr hs]

/-- **FR-4** Over €305: the whole net gain in euros is taxed, not only the part above €305. -/
theorem over_limit_whole_gain (year : ℕ) (ls : List Line) (u : Bool) (n : ℚ) (hs : threshold < l51 ls) (h : l52 ls = some n) :
    (yearOf year ls u).tax = some (centsUp (max (euros n : ℚ) 0 * incomeRate)
      + centsUp (max (euros n : ℚ) 0 * socialRate year)) := by
  simp [yearOf, not_le.mpr hs, h]

/-! #### Rule 5: netting within the year, no carry (art. 150 VH bis IV) -/

/-- **FR-5** With every l.224 known, l.52 is their sum: gains and losses of the year net against each other. -/
theorem l52_sum (ls : List Line) (gs : List ℚ) (h : ls.map Line.l224 = gs.map some) : l52 ls = some gs.sum := by
  induction ls generalizing gs with
  | nil => cases gs <;> simp_all [l52]
  | cons L ls ih =>
    cases gs with
    | nil => simp at h
    | cons g gs =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp [l52, h.1, ih gs h.2]

/-- **FR-5** A net loss (or nothing) is not taxed (unless the year is left unsettled by an unpriced sale). -/
theorem loss_untaxed (year : ℕ) (ls : List Line) (u : Bool) (n : ℚ) (h : l52 ls = some n) (hn : n ≤ 0)
    (hu : u = false ∨ threshold < l51 ls) :
    (yearOf year ls u).tax = some 0 := by
  have he : euros n ≤ 0 := by
    unfold euros; split_ifs with h0
    · have : n = 0 := le_antisymm hn h0
      subst this; norm_num
    · have : (0 : ℤ) ≤ ⌊-n + 1 / 2⌋ := Int.floor_nonneg.mpr (by linarith)
      linarith
  unfold yearOf
  split_ifs with h1 h2
  · exfalso; rcases hu with hu | hu
    · simp [hu] at h1
    · linarith [h1.2]
  · rfl
  · have he' : max (euros n : ℚ) 0 = 0 := max_eq_right (by exact_mod_cast he)
    simp [h, he', centsUp]

/-- The lines of one year, from lines tagged with their year. -/
def linesOf (y : ℕ) (ls : List (ℕ × Line)) : List Line := (ls.filter (fun e => e.1 = y)).map Prod.snd

/-- **FR-5** A year's figures depend on its own lines only: lines of other years (a loss among them) added before
or after change nothing, so a net loss is never carried to another year. -/
theorem no_carry (y : ℕ) (u : Bool) (ls other : List (ℕ × Line)) (h : ∀ e ∈ other, e.1 ≠ y) :
    yearOf y (linesOf y (other ++ ls)) u = yearOf y (linesOf y ls) u ∧
      yearOf y (linesOf y (ls ++ other)) u = yearOf y (linesOf y ls) u := by
  have : other.filter (fun e => e.1 = y) = [] := List.filter_eq_nil_iff.mpr (by simpa using h)
  simp [linesOf, List.filter_append, this]

/-! #### Rule 6: the flat tax and its rounding -/

/-- **FR-6** The rates: 12.8% income tax; levies 18.6% from 2025 (31.4% in all), 17.2% before (30%). -/
theorem rates (year : ℕ) :
    incomeRate = 128 / 1000 ∧ (2025 ≤ year → incomeRate + socialRate year = 314 / 1000) ∧
      (year < 2025 → incomeRate + socialRate year = 300 / 1000) := by
  refine ⟨rfl, fun h => ?_, fun h => ?_⟩
  · simp [incomeRate, socialRate, h]; norm_num
  · simp [incomeRate, socialRate, not_le.mpr h]; norm_num

/-- **FR-6** The tax is exactly income tax + levies, all three known or all three unknown. -/
theorem tax_is_sum (year : ℕ) (ls : List Line) (u : Bool) :
    ((yearOf year ls u).tax = none ∧ (yearOf year ls u).incomeTax = none ∧ (yearOf year ls u).social = none) ∨
      ∃ i s, (yearOf year ls u).incomeTax = some i ∧ (yearOf year ls u).social = some s ∧
        (yearOf year ls u).tax = some (i + s) := by
  unfold yearOf
  split_ifs
  · left; exact ⟨rfl, rfl, rfl⟩
  · right; exact ⟨0, 0, rfl, rfl, by simp⟩
  · split
    · left; exact ⟨rfl, rfl, rfl⟩
    · right; exact ⟨_, _, rfl, rfl, rfl⟩

/-- **FR-6** Rounding up to the cent: never below the exact amount, less than a cent above. -/
theorem centsUp_bounds (x : ℚ) : x ≤ centsUp x ∧ centsUp x < x + 1 / 100 := by
  unfold centsUp
  have h1 := Int.le_ceil (x * 100)
  have h2 := Int.ceil_lt_add_one (x * 100)
  constructor
  · rw [le_div_iff₀ (by norm_num)]; exact h1
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-- **FR-6** Whole euros: never more than 50 cents from the exact figure, and a loss rounds as the same gain would. -/
theorem euros_bounds (x : ℚ) : |(euros x : ℚ) - x| ≤ 1 / 2 ∧ euros (-x) = -euros x := by
  constructor
  · unfold euros
    split_ifs with h
    · have h1 := Int.floor_le (x + 1 / 2)
      have h2 := Int.lt_floor_add_one (x + 1 / 2)
      rw [abs_le]; constructor <;> linarith
    · have h1 := Int.floor_le (-x + 1 / 2)
      have h2 := Int.lt_floor_add_one (-x + 1 / 2)
      rw [abs_le]; push_cast; constructor <;> linarith
  · unfold euros
    rcases lt_trichotomy x 0 with h | h | h
    · simp [not_le.mpr h, h.le]
    · subst h; norm_num
    · simp [h.le, not_le.mpr (neg_lt_zero.mpr h)]

/-- **FR-6** Over the limit with a known l.52, the tax is never below 12.8% + the levies of the taxed whole euros,
and less than 2 cents above (each part rounded up to the cent). -/
theorem tax_bounds (year : ℕ) (ls : List Line) (u : Bool) (n : ℚ) (hs : threshold < l51 ls) (h : l52 ls = some n) :
    ∃ t, (yearOf year ls u).tax = some t ∧
      max (euros n : ℚ) 0 * (incomeRate + socialRate year) ≤ t ∧
      t < max (euros n : ℚ) 0 * (incomeRate + socialRate year) + 2 / 100 := by
  refine ⟨_, over_limit_whole_gain year ls u n hs h, ?_, ?_⟩ <;>
  · have a := centsUp_bounds (max (euros n : ℚ) 0 * incomeRate)
    have b := centsUp_bounds (max (euros n : ℚ) 0 * socialRate year)
    linarith

/-! #### Rules 7-8: boxes 3AN and 3BN -/

/-- **FR-7** Over the limit, a net gain (in whole euros) goes to 3AN. -/
theorem gain_to_3AN (year : ℕ) (ls : List Line) (u : Bool) (n : ℚ) (hs : threshold < l51 ls) (h : l52 ls = some n)
    (hg : 0 < euros n) : (yearOf year ls u).box = some (.AN, euros n) := by
  simp [yearOf, not_le.mpr hs, h, hg]

/-- **FR-7** Over the limit, a net loss (in whole euros) goes to 3BN, as a positive amount. -/
theorem loss_to_3BN (year : ℕ) (ls : List Line) (u : Bool) (n : ℚ) (hs : threshold < l51 ls) (h : l52 ls = some n)
    (hl : euros n < 0) : (yearOf year ls u).box = some (.BN, -euros n) := by
  simp [yearOf, not_le.mpr hs, h, hl, not_lt.mpr hl.le]

/-- **FR-8** Never both boxes: at least one of 3AN and 3BN is 0, and a filled box is above 0. -/
theorem one_box (year : ℕ) (ls : List Line) (u : Bool) :
    (an (yearOf year ls u) = 0 ∨ bn (yearOf year ls u) = 0) ∧
      ∀ b a, (yearOf year ls u).box = some (b, a) → 0 < a := by
  constructor
  · unfold an bn
    rcases (yearOf year ls u).box with _ | ⟨_ | _, a⟩ <;> simp
  · intro b a hb
    unfold yearOf at hb
    split_ifs at hb with h0 h0'
    cases hl : l52 ls with
    | none => simp [hl] at hb
    | some n =>
      simp only [hl] at hb
      split_ifs at hb with h1 h2 <;> simp only [Option.some.injEq, Prod.mk.injEq] at hb
      · omega
      · omega

/-- **FR-8** The boxes agree with the year: 3AN − 3BN = l.52 in whole euros, and the tax is worked out on 3AN. -/
theorem boxes_agree (year : ℕ) (ls : List Line) (u : Bool) (n : ℚ) (hs : threshold < l51 ls) (h : l52 ls = some n) :
    an (yearOf year ls u) - bn (yearOf year ls u) = euros n ∧
      (yearOf year ls u).tax = some (centsUp ((an (yearOf year ls u) : ℚ) * incomeRate)
        + centsUp ((an (yearOf year ls u) : ℚ) * socialRate year)) := by
  have key : an (yearOf year ls u) = max (euros n) 0 ∧ bn (yearOf year ls u) = max (-euros n) 0 := by
    rcases lt_trichotomy (euros n) 0 with hl | he | hg
    · simp [an, bn, loss_to_3BN year ls u n hs h hl, hl.le]; try omega
    · have hb : (yearOf year ls u).box = none := by simp [yearOf, not_le.mpr hs, h, he]
      simp [an, bn, hb, he]
    · simp [an, bn, gain_to_3AN year ls u n hs h hg, hg.le]
  refine ⟨by rw [key.1, key.2]; omega, ?_⟩
  rw [key.1]; push_cast; exact over_limit_whole_gain year ls u n hs h

/-! ## Rule 9: filing dates (Service-public.fr A15597, revenus 2025) -/

/-- Paper return, revenus 2025: 19 May 2026. -/
def paper2025 : ℕ := 20260519

/-- Online, revenus 2025: 01-19 and abroad, 20-54, 55-974 and 976, then 975 (Saint-Pierre-et-Miquelon). -/
def online2025 : List ℕ := [20260521, 20260528, 20260604, 20260430]

/-- `frDeadlines`: the paper date and the online dates; none for a year not published. -/
def deadlines (y : ℕ) : Option (ℕ × List ℕ) := if y = 2025 then some (paper2025, online2025) else none

/-- The dates `upcoming.ts` looks through: paper, then the first three online zones. -/
def candidates (paper : ℕ) (online : List ℕ) : List ℕ := paper :: online.take 3

/-- The next date shown: the first in the list on or after today. -/
def next (today : ℕ) (l : List ℕ) : Option ℕ := l.find? (fun d => decide (today ≤ d))

/-- **FR-9** The encoded dates for revenus 2025. -/
theorem deadlines_2025 :
    deadlines 2025 = some (20260519, [20260521, 20260528, 20260604, 20260430]) ∧ ∀ y, y ≠ 2025 → deadlines y = none := by
  refine ⟨rfl, fun y hy => by simp [deadlines, hy]⟩

/-- **FR-9** In a list in date order, the date shown is in the list, on or after today, and the earliest such; when
none is shown, every date is past. -/
theorem next_spec (today : ℕ) (l : List ℕ) (hs : l.Pairwise (· ≤ ·)) :
    (∀ d, next today l = some d → d ∈ l ∧ today ≤ d ∧ ∀ x ∈ l, today ≤ x → d ≤ x) ∧
      (next today l = none → ∀ x ∈ l, x < today) := by
  induction l with
  | nil => simp [next]
  | cons a l ih =>
    rw [List.pairwise_cons] at hs
    obtain ⟨ih1, ih2⟩ := ih hs.2
    by_cases ha : today ≤ a
    · have hn : next today (a :: l) = some a := by simp [next, ha]
      refine ⟨fun d hd => ?_, fun hd => by simp [hn] at hd⟩
      rw [hn] at hd; cases hd
      refine ⟨by simp, ha, fun x hx _ => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_refl _
      · exact hs.1 x hx
    · have hn : next today (a :: l) = next today l := by simp [next, ha]
      rw [hn]
      refine ⟨fun d hd => ?_, fun hd x hx => ?_⟩
      · obtain ⟨h1, h2, h3⟩ := ih1 d hd
        refine ⟨List.mem_cons_of_mem _ h1, h2, fun x hx hx' => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd hx' ha
        · exact h3 x hx hx'
      · rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · exact ih2 hd x hx

/-- **FR-9** For revenus 2025: the date chosen is one of the paper and first three online dates, never before today,
and the earliest of them on or after today; none is chosen once all four are past. `upcoming.ts` only shows the chosen
date when the year is one of the person's years with a French sale (`frYears`) and the date is within its horizon
(120 days); the Saint-Pierre-et-Miquelon dates (online 30 April, paper 31 March) are named in the line, not chosen. -/
theorem next_2025 (today : ℕ) :
    (∀ d, next today (candidates paper2025 online2025) = some d →
      d ∈ candidates paper2025 online2025 ∧ today ≤ d ∧
        ∀ x ∈ candidates paper2025 online2025, today ≤ x → d ≤ x) ∧
      (next today (candidates paper2025 online2025) = none → ∀ x ∈ candidates paper2025 online2025, x < today) :=
  next_spec today _ (by decide)

end Kanon.France
