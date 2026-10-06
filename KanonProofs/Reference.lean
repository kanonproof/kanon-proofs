/-!
# Reference models (#9)

Small, executable versions of KANON's tax engines, written so they are easy to read against the law.
`scripts/Vectors.lean` runs them on hundreds of generated cases and writes the answers to
`vectors/*.json`; the app's own engines must give the same answers (kanon-app `reference.test.ts`).
Money is in cents. Brazil's tax is in cents × 10,000 (basis points), so it is exact.
-/

namespace Kanon.Reference

/-! ## Brazil: one month of sales (Lei 9.250 art. 22, Lei 8.981 art. 21) -/

/-- R$35,000.00 a month in sales, in cents. -/
def exemptCents : Nat := 3500000

/-- Band tax on a gain, in cents × 10,000: 15% to R$5m, 17.5% to R$10m, 22.5% above R$30m, 20% between. -/
def bandBp (g : Nat) : Nat :=
  1500 * min g 500000000
  + 1750 * (min g 1000000000 - 500000000)
  + 2000 * (min g 3000000000 - 1000000000)
  + 2250 * (g - 3000000000)

structure Sale where
  value : Nat
  cost : Nat

def totalValue : List Sale → Nat
  | [] => 0
  | s :: ss => s.value + totalValue ss

/-- A loss never offsets another sale's gain: each sale's tax is on its own gain, zero if it lost. -/
def gainsTax : List Sale → Nat
  | [] => 0
  | s :: ss => bandBp (s.value - s.cost) + gainsTax ss

def brMonthBp (sales : List Sale) : Nat :=
  if totalValue sales ≤ exemptCents then 0 else gainsTax sales

/-- **#9** The monthly exemption: R$35,000 of sales or less, no tax. -/
theorem br_exempt (sales : List Sale) (h : totalValue sales ≤ exemptCents) : brMonthBp sales = 0 := by
  simp [brMonthBp, h]

/-- **#9** Band tax never falls as the gain grows. -/
theorem bandBp_mono {a b : Nat} (h : a ≤ b) : bandBp a ≤ bandBp b := by
  unfold bandBp
  have h1 : min a 500000000 ≤ min b 500000000 := by omega
  have h2 : min a 1000000000 - 500000000 ≤ min b 1000000000 - 500000000 := by omega
  have h3 : min a 3000000000 - 1000000000 ≤ min b 3000000000 - 1000000000 := by omega
  have h4 : a - 3000000000 ≤ b - 3000000000 := by omega
  have := Nat.mul_le_mul_left 1500 h1
  have := Nat.mul_le_mul_left 1750 h2
  have := Nat.mul_le_mul_left 2000 h3
  have := Nat.mul_le_mul_left 2250 h4
  omega

/-- **#9** Up to R$5m of gain, the tax is exactly 15%. -/
theorem band_first (g : Nat) (h : g ≤ 500000000) : bandBp g = 1500 * g := by
  unfold bandBp; simp [Nat.min_eq_left h, Nat.min_eq_left (show g ≤ 1000000000 by omega),
    Nat.min_eq_left (show g ≤ 3000000000 by omega)]; omega

/-! ## South Africa: one year of capital gains (Eighth Schedule paras 5–10) -/

structure ZaYear where
  aggregate : Int
  assessedLoss : Nat
  net : Nat

/-- Sum the year, shrink it towards zero by the exclusion, then take off last year's assessed loss. -/
def zaYear (gains : List Int) (excl bf : Nat) : ZaYear :=
  let sum := gains.foldl (· + ·) 0
  let agg : Int := if sum > 0 then max (sum - excl) 0 else min (sum + excl) 0
  let after := agg - bf
  ⟨agg, (-after).toNat, after.toNat⟩

/-- **#9** The exclusion never turns a gain into a loss or a loss into a gain. -/
theorem za_no_flip (gains : List Int) (excl bf : Nat) :
    let s := gains.foldl (· + ·) 0
    (s ≥ 0 → (zaYear gains excl bf).aggregate ≥ 0) ∧ (s ≤ 0 → (zaYear gains excl bf).aggregate ≤ 0) := by
  simp only [zaYear]
  constructor <;> intro h <;> split <;> omega

/-- **#9** Either a net gain is taxed or a loss carries forward, never both. -/
theorem za_one_or_other (gains : List Int) (excl bf : Nat) :
    (zaYear gains excl bf).net = 0 ∨ (zaYear gains excl bf).assessedLoss = 0 := by
  simp only [zaYear]
  omega


/-! ## United States: the Qualified Dividends and Capital Gain Tax Worksheet (Form 1040)

Money in cents; tax in cents × 10,000. Brackets are (top of band in cents, rate in basis points); the last band has no top. -/

structure UsSchedule where
  bands : List (Nat × Nat)   -- (upTo, rate) for every band but the last
  topRate : Nat
  zeroUpTo : Nat
  fifteenUpTo : Nat
  deriving Inhabited

/-- Tax on ordinary income by the rate schedule, in cents × 10,000. -/
def ordinaryBp (x : Nat) (bands : List (Nat × Nat)) (top : Nat) : Nat :=
  let rec go (floor : Nat) : List (Nat × Nat) → Nat
    | [] => (x - floor) * top
    | (upTo, r) :: rest => (min x upTo - floor) * r + (if x ≤ upTo then 0 else go upTo rest)
  go 0 bands

/-- Form 1040 tax: under $100,000 the Tax Table taxes the midpoint of each $25 band (under $3,000) or
$50 band, rounded half up to whole dollars. -/
def regularBp (x : Nat) (s : UsSchedule) : Nat :=
  if 10000000 ≤ x then ordinaryBp x s.bands s.topRate
  else if x < 500 then 0
  else
    let mid := if x < 1500 then 1000 else if x < 2500 then 2000
      else let w := if x < 300000 then 2500 else 5000; x / w * w + w / 2
    (ordinaryBp mid s.bands s.topRate + 500000) / 1000000 * 1000000

/-- Worksheet lines 1–25: the part of taxable income that is net capital gain goes at 0%, 15% and 20%. -/
def usBp (taxable gain : Nat) (s : UsSchedule) : Nat :=
  let pref := min gain taxable
  let ordinary := taxable - pref
  let l6 := min taxable s.zeroUpTo
  let atZero := l6 - min ordinary l6
  let l12 := min taxable s.fifteenUpTo
  let l14 := l12 - (ordinary + atZero)
  let atFifteen := min (pref - atZero) l14
  let atTwenty := pref - atZero - atFifteen
  min (regularBp ordinary s + atFifteen * 1500 + atTwenty * 2000) (regularBp taxable s)

/-- **#9** The worksheet never charges more than taxing everything as ordinary income (line 25). -/
theorem us_le_regular (taxable gain : Nat) (s : UsSchedule) : usBp taxable gain s ≤ regularBp taxable s := by
  unfold usBp; exact Nat.min_le_right _ _

/-! ## Japan: one coin's year, total average and moving average (NTA crypto FAQ 2-4)

Quantities in the coin's smallest unit, money in yen. Average costs are exact fractions (numerator, denominator). -/

inductive JpTrade
  | buy (qty cost : Nat)
  | sell (qty : Nat)

/-- Total average: cost of coins sold = (cost carried in + bought) × sold ÷ (coins carried in + bought). -/
def jpTotal (openQty openCost : Nat) (ts : List JpTrade) : Nat × Nat :=
  let bq := ts.foldl (fun a t => match t with | .buy q _ => a + q | .sell _ => a) 0
  let bc := ts.foldl (fun a t => match t with | .buy _ c => a + c | .sell _ => a) 0
  let sq := ts.foldl (fun a t => match t with | .sell q => a + q | .buy _ _ => a) 0
  ((openCost + bc) * sq, openQty + bq)

/-- Moving average: the book value is re-averaged at every buy; a sale takes book × sold ÷ held.
Returns cost of coins sold as a fraction. -/
def jpMoving (openQty openCost : Nat) (ts : List JpTrade) : Nat × Nat := Id.run do
  -- book value = bn / bd, held coins = q; cost of sales = cn / cd
  let mut q := openQty
  let mut bn := openCost
  let mut bd := 1
  let mut cn := 0
  let mut cd := 1
  for t in ts do
    match t with
    | .buy k c => bn := bn + c * bd; q := q + k
    | .sell k =>
      if q > 0 then
        -- taken = book × k / q
        let tn := bn * k
        let td := bd * q
        cn := cn * td + tn * cd
        cd := cd * td
        bn := bn * (q - k)
        bd := bd * q
        q := q - k
  return (cn, cd)

/-! ## United Kingdom: one token's same-day, 30-day and pool matching (HMRC CRYPTO22200)

Days in order: (day number, bought, cost of buys, sold, proceeds). Money in pence; each matched part's cost is its
share rounded down, so the app's exact costs may be up to a penny higher per part. -/

structure UkDay where
  day : Nat
  buy : Nat
  buyCost : Nat
  sell : Nat
  proceeds : Nat
  deriving Inhabited

structure UkOut where
  disposals : List (Nat × Nat × Nat × Nat)   -- (day, sold, proceeds, cost)
  poolQty : Nat
  poolCost : Nat

def ukMatch (days : List UkDay) : UkOut := Id.run do
  let n := days.length
  let mut lb : Array Nat := (days.map (·.buy)).toArray      -- buys left
  let mut lc : Array Nat := (days.map (·.buyCost)).toArray  -- their cost left
  let mut ls : Array Nat := (days.map (·.sell)).toArray     -- sales left to match
  let mut cost : Array Nat := Array.replicate n 0
  -- 1. same day
  for i in [0:n] do
    let m := min lb[i]! ls[i]!
    if m > 0 then
      let c := lc[i]! * m / lb[i]!
      cost := cost.set! i (cost[i]! + c)
      lc := lc.set! i (lc[i]! - c); lb := lb.set! i (lb[i]! - m); ls := ls.set! i (ls[i]! - m)
  -- 2. buys in the next 30 days, earliest sale first, earliest buy first
  for i in [0:n] do
    for j in [i+1:n] do
      if ls[i]! > 0 && days[j]!.day ≤ days[i]!.day + 30 && lb[j]! > 0 then
        let m := min lb[j]! ls[i]!
        let c := lc[j]! * m / lb[j]!
        cost := cost.set! i (cost[i]! + c)
        lc := lc.set! j (lc[j]! - c); lb := lb.set! j (lb[j]! - m); ls := ls.set! i (ls[i]! - m)
  -- 3. the pool, in date order (whatever can't be matched has no known cost)
  let mut pq := 0
  let mut pc := 0
  let mut out : List (Nat × Nat × Nat × Nat) := []
  for i in [0:n] do
    pq := pq + lb[i]!; pc := pc + lc[i]!
    if ls[i]! > 0 && pq > 0 then
      let t := min ls[i]! pq
      let c := pc * t / pq
      cost := cost.set! i (cost[i]! + c)
      pc := pc - c; pq := pq - t
    if days[i]!.sell > 0 then out := out ++ [(days[i]!.day, days[i]!.sell, days[i]!.proceeds, cost[i]!)]
  return ⟨out, pq, pc⟩

end Kanon.Reference
