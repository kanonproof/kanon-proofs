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

end Kanon.Reference
