/-!
# Exit ladder (#21)

A ladder sells shares of the position in steps, each share in basis points (1/100 of a percent)
of what was held when the plan was made. We prove the steps never add up to more than what's held,
and each step sells no more than what is left when it runs.
-/

namespace Kanon.Ladder

def total : List Nat → Nat
  | [] => 0
  | b :: bs => b + total bs

/-- Coins each step sells: its share of the starting position, rounded down. -/
def stepQty (held bp : Nat) : Nat := held * bp / 10000

def sold (held : Nat) : List Nat → Nat
  | [] => 0
  | b :: bs => stepQty held b + sold held bs

theorem sold_le (held : Nat) (bps : List Nat) : sold held bps * 10000 ≤ held * total bps := by
  induction bps with
  | nil => simp [sold, total]
  | cons b bs ih =>
    simp only [sold, total, Nat.add_mul, Nat.mul_add]
    have : stepQty held b * 10000 ≤ held * b := by unfold stepQty; exact Nat.div_mul_le_self _ _
    omega

/-- **#21** Steps add up to at most 100% → the ladder never sells more than is held. -/
theorem never_oversells (held : Nat) (bps : List Nat) (h : total bps ≤ 10000) : sold held bps ≤ held := by
  have := sold_le held bps
  have : held * total bps ≤ held * 10000 := Nat.mul_le_mul_left _ h
  omega

/-- What's left after running the steps in order. -/
def left (held : Nat) (bps : List Nat) : Nat := held - sold held bps

/-- **#21** Each step sells no more than what's still there when it runs. -/
theorem step_within (held : Nat) (before : List Nat) (b : Nat) (after : List Nat)
    (h : total (before ++ b :: after) ≤ 10000) : stepQty held b ≤ left held before := by
  have hall := never_oversells held (before ++ b :: after) h
  have split : ∀ xs ys : List Nat, sold held (xs ++ ys) = sold held xs + sold held ys := by
    intro xs ys; induction xs with
    | nil => simp [sold]
    | cons x xs ih => simp [sold, ih]; omega
  rw [split] at hall
  simp [sold] at hall
  unfold left; omega

/-- Calendar tax years (the US, Brazil, Japan and most countries): a sale's year is its date's year. -/
def calendarYear (year _month _day : Nat) : Nat := year

/-- UK tax year: 6 April to 5 April, named by the year it starts. -/
def ukTaxYear (year month day : Nat) : Nat := if month > 4 ∨ (month = 4 ∧ day ≥ 6) then year else year - 1

/-- **#21** Each step lands in the right UK tax year: 5 April is the old year, 6 April the new one. -/
theorem uk_boundary (y : Nat) : ukTaxYear y 4 5 = y - 1 ∧ ukTaxYear y 4 6 = y := by
  simp [ukTaxYear]

end Kanon.Ladder
